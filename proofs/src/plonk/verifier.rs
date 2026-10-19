use std::{
    collections::BTreeMap,
    hash::Hash,
    iter::{self},
};

use ff::{FromUniformBytes, WithSmallOrderMulGroup};

use super::{Error, VerifyingKey};
use crate::{
    plonk::{argument, evaluate_identities, traces::VerifierTrace},
    poly::{PolynomialLabel, Rotation, VerifierQuery, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::compute_inner_product,
};

/// Given a plonk proof, this function parses it to extract the verifying trace.
/// This function computes all Fiat-Shamir challenges, with the exception of
/// `x`, which is computed in [verify_algebraic_constraints]
pub fn parse_trace<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances. (Committed instances go first, that is, the first
    // instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[CS::Commitment],
    instances: &[&[F]],
    transcript: &mut T,
) -> Result<VerifierTrace<F, CS>, Error>
where
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
{
    #[cfg(not(feature = "committed-instances"))]
    let committed_instances: Vec<CS::Commitment> = vec![];

    // Check that instances matches the expected number of instance columns
    if committed_instances.len() + instances.len() != vk.cs.num_instance_columns {
        return Err(Error::InvalidInstances);
    }

    // Hash verification key into transcript.
    let vk_absorbed = vk.absorb_into(transcript)?;
    let phase0_committed = argument::verifier::Committed::from_key(&vk_absorbed);

    for commitment in committed_instances.iter() {
        transcript.common(commitment)?
    }

    for instance in instances.iter() {
        transcript.common(&F::from_u128(instance.len() as u128))?;
        for value in instance.iter() {
            transcript.common(value)?;
        }
    }

    let phase1_committed = argument::verifier::Committed::read(&vk.phase1_labels(), transcript)?;

    // Sample theta challenges for keeping lookup columns linearly independent
    let theta: Vec<F> = transcript.squeeze_challenges(vk.cs.nb_theta_challenges());

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    // Sample the trash challenges after the advices have been committed to
    let trash_challenges: Vec<F> = transcript.squeeze_challenges(vk.cs.nb_trash_challenges());

    let phase2_committed = argument::verifier::Committed::read(&vk.phase2_labels(), transcript)?;

    // Sample y challenges, which keep the identities linearly independent.
    let y: Vec<F> = transcript.squeeze_challenges(vk.cs.nb_y_challenges());

    Ok(VerifierTrace {
        phase0_committed,
        phase1_committed,
        phase2_committed,
        beta,
        gamma,
        theta,
        trash_challenges,
        y,
    })
}

/// Given a VerifierTrace, this function computes the opening challenge, x,
/// and proceeds to verify the algebraic constraints with the claimed
/// evaluations. This function does not verify the PCS proof.
///
/// The verifier will error if there are trailing bits in the transcript.
pub fn verify_algebraic_constraints<F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    vk: &VerifyingKey<F, CS>,
    trace: VerifierTrace<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances. (Committed instances go first, that is, the first
    // instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[CS::Commitment],
    instances: &[&[F]],
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
{
    #[cfg(not(feature = "committed-instances"))]
    let committed_instances: Vec<CS::Commitment> = vec![];

    let nb_committed_instances = committed_instances.len();

    let VerifierTrace {
        phase0_committed,
        phase1_committed,
        phase2_committed,
        beta,
        gamma,
        theta,
        trash_challenges,
        y,
    } = trace;

    // Read the commitment to the quotient polynomial h(X) = nu(X)/(X^n-1) from
    // the transcript. The prover splits h(X) into `quotient_poly_degree + 1`
    // limbs, committed to as one group.
    let quotient_labels: Vec<_> = (0..vk.domain.get_quotient_poly_degree() + 1)
        .map(PolynomialLabel::QuotientPiece)
        .collect();
    let quotient_committed = argument::verifier::Committed::read(&quotient_labels, transcript)?;

    // Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability.
    let x: F = CS::squeeze_evaluation_point(transcript);

    let splitting_factor = x.pow_vartime([vk.n() - 2]);
    let xn = splitting_factor * x.square();

    let instance_evals: Vec<F> = {
        let (min_rotation, max_rotation) =
            vk.cs.instance_queries.iter().fold((0, 0), |(min, max), (_, rotation)| {
                if rotation.0 < min {
                    (rotation.0, max)
                } else if rotation.0 > max {
                    (min, rotation.0)
                } else {
                    (min, max)
                }
            });
        let max_instance_len = instances
            .iter()
            .map(|instance| instance.len())
            .max_by(Ord::cmp)
            .unwrap_or_default();
        let l_i_s = &vk.domain.l_i_range(
            x,
            xn,
            -max_rotation..max_instance_len as i32 + min_rotation.abs(),
        );
        vk.cs
            .instance_queries
            .iter()
            .map(|(column, rotation)| {
                if column.index() < nb_committed_instances {
                    transcript.read()
                } else {
                    let instance = instances[column.index() - nb_committed_instances];
                    let offset = (max_rotation - rotation.0) as usize;
                    Ok(compute_inner_product(
                        instance,
                        &l_i_s[offset..offset + instance.len()],
                    ))
                }
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    let domain = vk.get_domain();
    let cs = vk.cs();

    let x_rotations: BTreeMap<Rotation, F> = argument::rotations(cs)
        .into_iter()
        .map(|rotation| (rotation, domain.rotate_omega(x, rotation)))
        .collect();

    let phase0_evaluated = phase0_committed.evaluate(cs, &x_rotations, transcript)?;

    let phase1_evaluated = phase1_committed.evaluate(cs, &x_rotations, transcript)?;
    let phase2_evaluated = phase2_committed.evaluate(cs, &x_rotations, transcript)?;
    let mut quotient_evaluated = quotient_committed.evaluate(cs, &x_rotations, transcript)?;

    let phase0_evals = &phase0_evaluated.evals_map;
    let phase1_evals = &phase1_evaluated.evals_map;
    let phase2_evals = &phase2_evaluated.evals_map;

    // Evaluate the batched identities, nu(x)
    let nu_eval = evaluate_identities(
        vk,
        &instance_evals,
        phase0_evals,
        phase1_evals,
        phase2_evals,
        x,
        xn,
        beta,
        gamma,
        &theta,
        &trash_challenges,
        &y,
    );

    derive_h0_eval(&mut quotient_evaluated, nu_eval, x, splitting_factor, xn)?;

    // Collect queries that are checked in the multi-open argument
    //
    // The multi-open scales the first commitment by 1, which is best spent on
    // one read from the proof: the phase-0 commitments are known in advance and
    // a committed instance may be a constant, so both go after phases 1 and 2.
    let queries = iter::empty()
        .chain(phase1_evaluated.queries())
        .chain(phase2_evaluated.queries())
        .chain(phase0_evaluated.queries())
        .chain(vk.cs.instance_queries.iter().enumerate().filter_map(
            |(query_index, &(column, at))| {
                if column.index() < nb_committed_instances {
                    Some(VerifierQuery::new(
                        x_rotations[&at],
                        &committed_instances[column.index()],
                        PolynomialLabel::CommittedInstance(column.index()),
                        instance_evals[query_index],
                    ))
                } else {
                    None
                }
            },
        ))
        .chain(quotient_evaluated.queries())
        .collect::<Vec<_>>();

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values, which is true as long
    // as the following accumulator passes the invariant.
    CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
}

/// Adds the evaluation of the quotient limb `h_0` at `x` to
/// `quotient_evaluated`, which holds those of all the other limbs. It is
/// derived from `nu_eval = nu(x) = (x^n - 1) h(x)`, for
/// `h(x) = h_0(x) + x^{n-2} h_1(x) + ...`, so that opening `h_0` at `x` checks
/// the identities. `splitting_factor` is `x^{n-2}` and `xn` is `x^n`.
pub(crate) fn derive_h0_eval<F, CS>(
    quotient_evaluated: &mut argument::verifier::Evaluated<F, CS>,
    nu_eval: F,
    x: F,
    splitting_factor: F,
    xn: F,
) -> Result<(), Error>
where
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
{
    let higher_limbs = (quotient_evaluated.evals_map.values().skip(1).rev())
        .fold(F::ZERO, |acc, evals| {
            (acc + evals[0].eval()) * splitting_factor
        });
    let vanishing_inv =
        Option::<F>::from((xn - F::ONE).invert()).ok_or(Error::ConstraintSystemFailure)?;
    let h0_eval = nu_eval * vanishing_inv - higher_limbs;
    quotient_evaluated.insert(PolynomialLabel::QuotientPiece(0), x, h0_eval);
    Ok(())
}

/// Prepares a plonk proof into a PCS instance that can be finalized or
/// batched. It is responsibility of the verifier to check the validity of the
/// instance columns.
///
/// The verifier will error if there are trailing bytes in the transcript.
pub fn prepare<F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    vk: &VerifyingKey<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances. (Committed instances go first, that is, the first
    // instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[CS::Commitment],
    instances: &[&[F]],
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
{
    let trace = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        committed_instances,
        instances,
        transcript,
    )?;

    verify_algebraic_constraints(
        vk,
        trace,
        #[cfg(feature = "committed-instances")]
        committed_instances,
        instances,
        transcript,
    )
}

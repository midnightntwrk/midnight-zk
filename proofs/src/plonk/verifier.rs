use std::{
    collections::BTreeMap,
    hash::Hash,
    iter::{self},
};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};

use super::{Error, VerifyingKey};
use crate::{
    plonk::{
        lookup, partially_evaluate_identities,
        permutation::{self, verifier::CommonEvaluated},
        traces::VerifierTrace,
        trash,
    },
    poly::{commitment::PolynomialCommitmentScheme, VerifierQuery},
    transcript::{read_n, Hashable, Sampleable, Transcript},
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
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
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
    let committed_instances: Vec<Vec<CS::Commitment>> = vec![vec![]; instances.len()];

    let nb_committed_instances = committed_instances[0].len();
    for committed_instances in committed_instances.iter() {
        if committed_instances.len() != nb_committed_instances {
            return Err(Error::InvalidInstances);
        }
    }

    // Check that number of instances matches the expected number of instance
    // columns
    for (committed_instances, instances) in committed_instances.iter().zip(instances.iter()) {
        if committed_instances.len() + instances.len() != vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    let num_proofs = instances.len();

    // Hash verification key into transcript
    vk.hash_into(transcript)?;

    for committed_instances in committed_instances.iter() {
        for commitment in committed_instances.iter() {
            transcript.common(commitment)?
        }
    }

    for instance in instances.iter() {
        for instance in instance.iter() {
            transcript.common(&F::from_u128(instance.len() as u128))?;
            for value in instance.iter() {
                transcript.common(value)?;
            }
        }
    }

    // Read commitments to advice columns from the transcript and squeeze challenges
    let (advice_commitments, challenges) = {
        let mut advice_commitments =
            vec![vec![CS::Commitment::default(); vk.cs.num_advice_columns]; num_proofs];
        let mut challenges = vec![F::ZERO; vk.cs.num_challenges];

        for current_phase in vk.cs.phases() {
            for advice_commitments in advice_commitments.iter_mut() {
                for (phase, commitment) in
                    vk.cs.advice_column_phase.iter().zip(advice_commitments.iter_mut())
                {
                    if current_phase == *phase {
                        *commitment = transcript.read()?;
                    }
                }
            }
            for (phase, challenge) in vk.cs.challenge_phase.iter().zip(challenges.iter_mut()) {
                if current_phase == *phase {
                    *challenge = transcript.squeeze_challenge();
                }
            }
        }

        (advice_commitments, challenges)
    };

    // Sample theta challenge for batching independent lookup columns
    let theta: F = transcript.squeeze_challenge();

    // Lookup argument: Read commitments to permuted input and table columns from
    // the transcript
    let lookup_permuted_commitments = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            vk.cs
                .lookups
                .iter()
                .map(|argument| argument.read_permuted_commitments(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample beta challenge for permutation and lookup argument
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge for permutation and lookup argument
    let gamma: F = transcript.squeeze_challenge();

    // Permutation argument: Read commitments to limbs of product polynomial from
    // the transcript
    let permutation_product_commitments = (0..num_proofs)
        .map(|_| vk.cs.permutation.read_product_commitments(vk, transcript))
        .collect::<Result<Vec<_>, _>>()?;

    // Lookup argument: Read commitments to product polynomial from the transcript
    let lookup_product_commitments = lookup_permuted_commitments
        .into_iter()
        .map(|lookups| {
            lookups
                .into_iter()
                .map(|lookup| lookup.read_product_commitment(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample trash challenge
    let trash_challenge: F = transcript.squeeze_challenge();

    // Read commitments to trashcans from the transcript
    let trashcan_commitments = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            vk.cs
                .trashcans
                .iter()
                .map(|argument| argument.read_committed::<CS, _>(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample identity batching challenge y, for batching all independent identities
    let y: F = transcript.squeeze_challenge();

    Ok(VerifierTrace {
        advice_commitments,
        lookups: lookup_product_commitments,
        trashcans: trashcan_commitments,
        permutations: permutation_product_commitments,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    })
}

/// Construct the commitment to the linearization polynomial
/// (which will be checked that it opens to 0 at x in the multi-open argument):
///
///  S_0*id_0(x) + y*S_1*id_1(x) + y^2*S_2*id_2(x) + ... + y^m*S_m*id_m(x)
///        - (h_0 + x^n*h_1 + x^{2n}*h_2 + ... + x^{l*n}*h_l) * (x^n-1),
///
/// where:
/// * y^i is a power of the batching challenge y,
/// * id_j(x) is the result of (partially or fully) evaluating the identity id_j
///   at x (i.e., a scalar),
/// * S_j is, either,
///      - (i)  the commitment to a fixed column corresponding to a simple
///        selector, or,
///      - (ii) the zero commitment (because the corresponding identity id_i has
///        been fully evaluated and thus the resulting scalar is part of the
///        constant term of the linearization poly)
/// * h_k are commitments to the limbs of the quotient polynomial.
fn compute_linearization_commitment<
    'com,
    F: PrimeField + ff::WithSmallOrderMulGroup<3> + ff::FromUniformBytes<64> + std::cmp::Ord,
    CS: PolynomialCommitmentScheme<F>,
>(
    expressions: impl Iterator<Item = (Option<usize>, F)> + 'com,
    vk: &'com VerifyingKey<F, CS>,
    y: &F,
    xn: &F,
    quotient_limb_commitments: &'com [CS::Commitment],
    g1: &'com CS::Commitment,
) -> (Vec<&'com CS::Commitment>, Vec<F>) {
    let mut identities_points = Vec::new();
    let mut identities_scalars = Vec::new();

    identities_points.extend(quotient_limb_commitments);

    let mut xn_pow = F::ONE - *xn;
    for _ in 0..quotient_limb_commitments.len() {
        identities_scalars.push(xn_pow);
        xn_pow *= xn;
    }

    let mut grouped_points: BTreeMap<Option<usize>, F> = BTreeMap::new();
    let mut y_pow = F::ONE;
    expressions
        .collect::<Vec<(Option<usize>, F)>>()
        .iter()
        .rev()
        .for_each(|(col_idx, eval)| {
            *grouped_points.entry(*col_idx).or_default() += y_pow * eval;
            y_pow *= y;
        });

    grouped_points.into_iter().for_each(|(col_idx, eval)| {
        match col_idx {
            Some(col_idx) => identities_points.push(&vk.fixed_commitments[col_idx]),
            // Fully evaluated identities go to the constant term
            None => identities_points.push(g1),
        }
        identities_scalars.push(eval);
    });
    (identities_points, identities_scalars)
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
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
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
    let committed_instances: Vec<Vec<CS::Commitment>> = vec![vec![]; instances.len()];
    let nb_committed_instances = committed_instances[0].len();
    let num_proofs = instances.len();

    let VerifierTrace {
        advice_commitments,
        lookups,
        trashcans,
        permutations,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    } = trace;

    // Read commitments to limbs of the quotient polynomial h(X) = nu(X)/(X^n-1)
    // from the transcript
    let quotient_limb_coms = read_n(transcript, vk.domain.get_quotient_poly_degree())?;

    // Sample evaluation challenge x
    let x: F = transcript.squeeze_challenge();
    let xn = x.pow([vk.n()]);

    let instance_evals = {
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
            .flat_map(|instance| instance.iter().map(|instance| instance.len()))
            .max_by(Ord::cmp)
            .unwrap_or_default();
        let l_i_s = &vk.domain.l_i_range(
            x,
            xn,
            -max_rotation..max_instance_len as i32 + min_rotation.abs(),
        );
        instances
            .iter()
            .map(|instances| {
                vk.cs
                    .instance_queries
                    .iter()
                    .map(|(column, rotation)| {
                        if column.index() < nb_committed_instances {
                            transcript.read()
                        } else {
                            let instances = instances[column.index() - nb_committed_instances];
                            let offset = (max_rotation - rotation.0) as usize;
                            Ok(compute_inner_product(
                                instances,
                                &l_i_s[offset..offset + instances.len()],
                            ))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    // Read evals of all advice polys from transcript
    let advice_evals: Vec<Vec<F>> = (0..num_proofs)
        .map(|_| read_n(transcript, vk.cs.advice_queries.len()))
        .collect::<Result<Vec<_>, _>>()?;

    // Read num_evaluated_fixed_queries evals from the transcript, i.e.,
    // num_fixed_columns - num_simple_selectors evals and fill up the
    // "missing" places with 1 (the transcript doesn't contain evals corresp.
    // to simple selectors)
    let mut fixed_evals = read_n(transcript, vk.cs.num_evaluated_fixed_queries())?;
    for (idx, (col, _)) in vk.cs.fixed_queries().iter().enumerate() {
        if vk.cs.indices_simple_selectors.contains(&col.index()) {
            fixed_evals.insert(idx, F::ONE)
        }
    }

    let permutations_common = vk.permutation.evaluate(transcript)?;

    let permutations = permutations
        .into_iter()
        .map(|permutation| permutation.evaluate(transcript))
        .collect::<Result<Vec<_>, _>>()?;

    let (lookup_coms, lookup_evals) = lookups
        .into_iter()
        .map(|lookups| -> Result<(Vec<_>, Vec<_>), Error> {
            Ok(lookups
                .into_iter()
                .map(|lookup| lookup.evaluate(transcript))
                .collect::<Result<Vec<(_, _)>, _>>()?
                .into_iter()
                .unzip())
        })
        .collect::<Result<(Vec<_>, Vec<_>), _>>()?;

    let (trash_coms, trash_evals) = trashcans
        .into_iter()
        .map(|trashcans| -> Result<(Vec<_>, Vec<_>), Error> {
            Ok(trashcans
                .into_iter()
                .map(|trash| trash.evaluate(transcript))
                .collect::<Result<Vec<(_, _)>, _>>()?
                .into_iter()
                .unzip())
        })
        .collect::<Result<(Vec<_>, Vec<_>), _>>()?;

    // Partially evaluate batched identities
    // (without fixed columns corresponding to simple, multiplicative selectors)
    let expressions = partially_evaluate_identities(
        &fixed_evals,
        instance_evals.iter(),
        advice_evals.iter(),
        permutations.iter().map(|e| &e.sets),
        lookup_evals.iter(),
        trash_evals.iter(),
        &permutations_common,
        x,
        xn,
        beta,
        gamma,
        theta,
        trash_challenge,
        vk,
        &challenges,
    );

    let g1 = CS::constant_commitment();
    let lin_com =
        compute_linearization_commitment(expressions, vk, &y, &xn, &quotient_limb_coms, &g1);

    let queries = compute_queries(
        vk,
        nb_committed_instances,
        committed_instances,
        &permutations_common,
        &fixed_evals,
        &instance_evals,
        &advice_commitments,
        &advice_evals,
        &permutations,
        &lookup_evals,
        &lookup_coms,
        &trash_evals,
        &trash_coms,
        x,
        lin_com,
    );

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values, which is
    // true as long as the multi-open argument correctly verifies
    CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
}

/// Collect queries that are checked in the multi-open argument
///
/// NB: Queries corresponding to simple, multipl. selectors need not be checked
#[allow(clippy::too_many_arguments)]
fn compute_queries<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    vk: &'a VerifyingKey<F, CS>,
    nb_committed_instances: usize,
    committed_instances: &'a [&[CS::Commitment]],
    permutations_common: &'a CommonEvaluated<F>,
    fixed_evals: &[F],
    instance_evals: &[Vec<F>],
    advice_commitments: &'a [Vec<CS::Commitment>],
    advice_evals: &[Vec<F>],
    permutations: &'a [permutation::verifier::Evaluated<F, CS>],
    lookup_evals: &'a [Vec<lookup::Evaluated<F>>],
    lookup_coms: &'a [Vec<lookup::verifier::Committed<F, CS>>],
    trash_evals: &'a [Vec<trash::Evaluated<F>>],
    trash_coms: &'a [Vec<trash::verifier::Committed<F, CS>>],
    x: F,
    lin_com: (Vec<&'a CS::Commitment>, Vec<F>),
) -> Vec<VerifierQuery<'a, F, CS>> {
    committed_instances
        .iter()
        .zip(instance_evals.iter())
        .zip(advice_commitments.iter())
        .zip(advice_evals.iter())
        .zip(permutations.iter())
        .zip(lookup_evals)
        .zip(lookup_coms.iter())
        .zip(trash_evals)
        .zip(trash_coms.iter())
        .flat_map(
            |(
                (
                    (
                        (
                            (
                                (
                                    ((committed_instances, instance_evals), advice_commitments),
                                    advice_evals,
                                ),
                                permutation,
                            ),
                            lookup_evals,
                        ),
                        lookup_coms,
                    ),
                    trashcan_evals,
                ),
                trashcan_coms,
            )| {
                iter::empty()
                    .chain(vk.cs.instance_queries.iter().enumerate().filter_map(
                        move |(query_index, &(column, at))| {
                            if column.index() < nb_committed_instances {
                                Some(VerifierQuery::new(
                                    vk.domain.rotate_omega(x, at),
                                    &committed_instances[column.index()],
                                    instance_evals[query_index],
                                ))
                            } else {
                                None
                            }
                        },
                    ))
                    .chain(vk.cs.advice_queries.iter().enumerate().map(
                        move |(query_index, &(column, at))| {
                            VerifierQuery::new(
                                vk.domain.rotate_omega(x, at),
                                &advice_commitments[column.index()],
                                advice_evals[query_index],
                            )
                        },
                    ))
                    .chain(permutation.queries(vk, x))
                    .chain(
                        lookup_evals
                            .iter()
                            .zip(lookup_coms.iter())
                            .flat_map(move |(e, c)| lookup::verifier::queries(e, c, vk, x)),
                    )
                    .chain(
                        trashcan_evals
                            .iter()
                            .zip(trashcan_coms.iter())
                            .flat_map(move |(eval, com)| trash::verifier::queries(eval, com, x)),
                    )
            },
        )
        .chain(
            vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                // Filter out queries for simple, multipl. selectors
                .filter(|(_, (col, _))| !vk.cs.indices_simple_selectors.contains(&col.index()))
                .map(|(query_index, &(column, at))| {
                    VerifierQuery::new(
                        vk.domain.rotate_omega(x, at),
                        // fixed_commitments is sorted per column_index
                        &vk.fixed_commitments[column.index()],
                        // fixed_evals is sorted per fixed_queries
                        fixed_evals[query_index],
                    )
                }),
        )
        .chain(permutations_common.queries(&vk.permutation, x))
        .chain(iter::once(VerifierQuery::new_linear(
            x,
            lin_com.0,
            lin_com.1,
            F::ZERO,
        )))
        .collect::<Vec<_>>()
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
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
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

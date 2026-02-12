use std::{
    collections::{BTreeSet, HashMap, HashSet},
    hash::Hash,
    iter::{self},
    ops::RangeTo,
};

use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, OsRng, RngCore};

use super::{
    circuit::{
        sealed::{self},
        Advice, Any, Assignment, Challenge, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner,
        Instance, Selector,
    },
    logup, permutation, Error, ProvingKey,
};
use crate::{
    circuit::Value,
    plonk::{
        linearization::prover::compute_linearization_poly, partially_evaluate_identities,
        traces::ProverTrace, trash,
    },
    poly::{
        batch_invert_rational, commitment::PolynomialCommitmentScheme, Coeff, EvaluationDomain,
        ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, PolynomialRepresentation, ProverQuery,
        Rotation,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{arithmetic::eval_polynomial, rational::Rational},
};

pub(crate) fn compute_h_poly<
    F: WithSmallOrderMulGroup<3> + Hashable<T::Hash>,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
>(
    params: &CS::Parameters,
    domain: &EvaluationDomain<F>,
    nu_poly: Polynomial<F, ExtendedLagrangeCoeff>,
    transcript: &mut T,
) -> Result<Vec<Polynomial<F, Coeff>>, Error>
where
    CS::Commitment: Hashable<T::Hash>,
{
    // Construct quotient polynomial h(X) = nu(X) / (X^n - 1) in evaluation form
    let h_poly = domain.divide_by_vanishing_poly(nu_poly);

    // Convert h(X) to coefficient form
    let mut h_poly = domain.extended_to_coeff(h_poly);

    // Let n := size of evaluation domain
    // Let d := degree of constraint system
    // Hence, the degree of the quotient poly is: d*(n-1) - n = (d-1)*(n-1) - 1,
    // and a domain of size (d-1)*(n-1) suffices to correctly represent it
    h_poly.truncate((domain.n - 1) as usize * domain.get_quotient_poly_degree());

    // Split h(X) up into limbs
    let h_poly_iter = h_poly.chunks_exact((domain.n - 1) as usize);
    assert_eq!(h_poly_iter.remainder().len(), 0);
    let mut h_limbs = h_poly_iter.map(|v| v.to_vec()).collect::<Vec<_>>();
    drop(h_poly);

    blind_quotient_limbs(&mut h_limbs);

    let h_limbs: Vec<_> = h_limbs.into_iter().map(|h_limb| domain.coeff_from_vec(h_limb)).collect();

    // Compute commitment to each limb
    let h_commitments = h_limbs.iter().map(|h_piece| CS::commit(params, h_piece));

    // Write each limb commitment to the transcript
    for c in h_commitments {
        transcript.write(&c)?;
    }

    Ok(h_limbs)
}

fn blind_quotient_limbs<F: PrimeField>(quotient_limbs: &mut [Vec<F>]) {
    let nr_limbs = quotient_limbs.len();
    assert!(nr_limbs >= 2);

    for i in 1..nr_limbs {
        let t = F::random(OsRng);
        quotient_limbs[i - 1].push(t);
        quotient_limbs[i][0] -= t;
    }

    quotient_limbs[nr_limbs - 1].push(F::ZERO);
}

#[cfg(feature = "committed-instances")]
/// Commit to a vector of raw instances. This function can be used to prepare
/// the committed instances that the verifier will be provided with when this
/// feature is enabled.
pub fn commit_to_instances<F, CS: PolynomialCommitmentScheme<F>>(
    params: &CS::Parameters,
    domain: &EvaluationDomain<F>,
    instances: &[F],
) -> CS::Commitment
where
    F: WithSmallOrderMulGroup<3> + Ord + FromUniformBytes<64>,
{
    let mut poly = domain.empty_lagrange();
    for (poly_eval, value) in poly.iter_mut().zip(instances.iter()) {
        *poly_eval = *value;
    }
    CS::commit_lagrange(params, &poly)
}

/// This computes a proof trace for the provided `circuits` when given the
/// public parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// The trace can then be used to finalise proofs, or to fold them.
pub(crate) fn compute_trace<
    F,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuits: &[ConcreteCircuit],
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[&[F]]],
    mut rng: impl RngCore + CryptoRng,
    transcript: &mut T,
) -> Result<ProverTrace<F>, Error>
where
    CS::Commitment: Hashable<T::Hash>,
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
{
    #[cfg(not(feature = "committed-instances"))]
    let nb_committed_instances: usize = 0;

    if circuits.len() != instances.len() {
        return Err(Error::InvalidInstances);
    }

    for instances in instances.iter() {
        if instances.len() != pk.vk.cs.num_instance_columns
            || instances.len() < nb_committed_instances
        {
            return Err(Error::InvalidInstances);
        }
    }

    // Hash verification key into transcript
    pk.vk.hash_into(transcript)?;

    let domain = &pk.vk.domain;

    let instance = compute_instances(params, pk, instances, nb_committed_instances, transcript)?;

    let (advice, challenges) =
        parse_advices(params, pk, circuits, instances, transcript, &mut rng)?;

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    // Commit to the multiplicities columns
    let lookups: Vec<Vec<logup::prover::ComputedMultiplicities<F>>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| -> Result<Vec<_>, Error> {
            pk.vk
                .cs
                .lookups
                .iter()
                .flat_map(|l| l.split(pk.get_vk().cs().degree()))
                .map(|logup| {
                    logup.commit_multiplicities(
                        pk,
                        params,
                        theta,
                        &advice.advice_polys,
                        &pk.fixed_values,
                        &instance.instance_values,
                        &challenges,
                        transcript,
                    )
                })
                .collect::<Result<Vec<_>, Error>>()
        })
        .collect::<Result<Vec<_>, Error>>()?;

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    // Commit to permutations.
    let permutations: Vec<permutation::prover::Committed<F>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| {
            pk.vk.cs.permutation.commit(
                params,
                pk,
                &pk.permutation,
                &advice.advice_polys,
                &pk.fixed_values,
                &instance.instance_values,
                beta,
                gamma,
                &mut rng,
                transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lookups: Vec<Vec<logup::prover::Committed<F>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            // Construct and commit to products polynomials for each lookup
            lookups
                .into_iter()
                .map(|lookup| lookup.commit_logderivative(pk, params, beta, &mut rng, transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Trash argument
    let trash_challenge: F = transcript.squeeze_challenge();

    let trashcans: Vec<Vec<trash::prover::Committed<F>>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| -> Result<Vec<_>, Error> {
            pk.vk
                .cs
                .trashcans
                .iter()
                .map(|trash| {
                    trash.commit::<CS, _>(
                        params,
                        domain,
                        trash_challenge,
                        &advice.advice_polys,
                        &pk.fixed_values,
                        &instance.instance_values,
                        &challenges,
                        transcript,
                    )
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Obtain challenge for keeping all separate gates linearly independent
    let y: F = transcript.squeeze_challenge();

    let (instance_polys, instance_values) =
        instance.into_iter().map(|i| (i.instance_polys, i.instance_values)).unzip();

    let advice_polys = advice
        .into_iter()
        .map(|a| {
            a.advice_polys
                .into_iter()
                .map(|p| domain.lagrange_to_coeff(p))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    Ok(ProverTrace {
        advice_polys,
        instance_polys,
        instance_values,
        lookups,
        trashcans,
        permutations,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    })
}

/// This takes the computed trace of a set of witnesses and creates a proof
/// for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub(crate) fn finalise_proof<'a, F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    params: &'a CS::Parameters,
    pk: &'a ProvingKey<F, CS>,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    trace: ProverTrace<F>,
    transcript: &mut T,
) -> Result<(), Error>
where
    CS::Commitment: Hashable<T::Hash>,
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
{
    #[cfg(not(feature = "committed-instances"))]
    let nb_committed_instances: usize = 0;

    let nu_poly = compute_nu_poly(pk, &trace);

    // Construct the quotient polynomial h(X) = nu(X)/(X^n-1), split it into limbs,
    // and commit to each limb separately
    let quotient_limbs =
        compute_h_poly::<F, CS, T>(params, pk.get_vk().get_domain(), nu_poly, transcript)?;

    let ProverTrace {
        advice_polys,
        instance_polys,
        lookups,
        trashcans,
        permutations,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
        ..
    } = trace;

    let x: F = transcript.squeeze_challenge();

    let (fixed_evals, instance_evals, advice_evals) = write_evals_to_transcript(
        pk,
        nb_committed_instances,
        &instance_polys,
        &advice_polys,
        x,
        transcript,
    )?;

    // Evaluate common permutation data
    let permutations_common = pk.permutation.evaluate(x, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let permutations: Vec<permutation::prover::Evaluated<F>> = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> { permutation.evaluate(pk, x, transcript) })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<Vec<logup::prover::Evaluated<F>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|p| p.evaluate(pk, x, transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the trashcans, if any, at x.
    let trashcans: Vec<Vec<trash::prover::Evaluated<F>>> = trashcans
        .into_iter()
        .map(|trash| -> Result<Vec<_>, _> {
            trash
                .into_iter()
                .map(|p| p.evaluate(x, transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Partially evaluate batched identities (without fixed columns
    // corresponding to simple, multiplicative selectors)
    let splitting_factor = x.pow_vartime([pk.vk.n() - 1]);
    let xn = splitting_factor * x;
    let expressions = partially_evaluate_identities(
        &pk.vk,
        &fixed_evals,
        &instance_evals,
        &advice_evals,
        permutations.iter().map(|e| &e.evaluated),
        lookups.iter().map(|e| e.iter().map(|inner| &inner.evaluated)),
        trashcans.iter().map(|e| e.iter().map(|inner| &inner.evaluated)),
        &permutations_common,
        x,
        xn,
        beta,
        gamma,
        theta,
        trash_challenge,
        &challenges,
    );

    // Compute linearization polynomial
    let linearization_poly =
        compute_linearization_poly(expressions, pk, y, xn, splitting_factor, quotient_limbs);

    debug_assert_eq!(
        eval_polynomial(&linearization_poly, x),
        F::ZERO,
        "The linearization poly should evaluate to zero at the evaluation challenge x."
    );

    let queries = compute_queries(
        pk,
        nb_committed_instances,
        &instance_polys,
        &advice_polys,
        &permutations,
        &lookups,
        &trashcans,
        x,
        &linearization_poly,
    );

    CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
//
// NOTE: Any change here must be mirrored in src/plonk/bench/prover.rs
// to ensure the benchmarks remain aligned with the real prover.
pub fn create_proof<
    F,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuits: &[ConcreteCircuit],
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[&[F]]],
    rng: impl RngCore + CryptoRng,
    transcript: &mut T,
) -> Result<(), Error>
where
    CS::Commitment: Hashable<T::Hash>,
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
{
    let trace = compute_trace(
        params,
        pk,
        circuits,
        #[cfg(feature = "committed-instances")]
        nb_committed_instances,
        instances,
        rng,
        transcript,
    )?;
    finalise_proof(
        params,
        pk,
        #[cfg(feature = "committed-instances")]
        nb_committed_instances,
        trace,
        transcript,
    )
}

pub(super) fn compute_instances<F, CS, T>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    instances: &[&[&[F]]],
    nb_committed_instances: usize,
    transcript: &mut T,
) -> Result<Vec<InstanceSingle<F>>, Error>
where
    T: Transcript,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
{
    instances
        .iter()
        .map(|instance| -> Result<InstanceSingle<F>, Error> {
            let instance_values = instance
                .iter()
                .enumerate()
                .map(|(i, values)| {
                    // Committed instances go first.
                    let is_committed_instance = i < nb_committed_instances;
                    let mut poly = pk.vk.domain.empty_lagrange();
                    assert_eq!(poly.len(), pk.vk.domain.n as usize);
                    if values.len() > (poly.len() - (pk.vk.cs.blinding_factors() + 1)) {
                        return Err(Error::InstanceTooLarge);
                    }
                    if !is_committed_instance {
                        transcript.common(&F::from_u128(values.len() as u128))?;
                    }

                    for (poly_eval, value) in poly.iter_mut().zip(values.iter()) {
                        if !is_committed_instance {
                            transcript.common(value)?;
                        }
                        *poly_eval = *value;
                    }

                    if is_committed_instance {
                        transcript.common(&CS::commit_lagrange(params, &poly))?;
                    }

                    Ok(poly)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let instance_polys: Vec<_> = instance_values
                .iter()
                .map(|poly| {
                    let lagrange_vec = pk.vk.domain.lagrange_from_vec(poly.to_vec());
                    pk.vk.domain.lagrange_to_coeff(lagrange_vec)
                })
                .collect();

            Ok(InstanceSingle {
                instance_values,
                instance_polys,
            })
        })
        .collect::<Result<Vec<_>, _>>()
}

#[allow(clippy::type_complexity)]
pub(super) fn parse_advices<F, CS, ConcreteCircuit, T>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[F]]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
) -> Result<(Vec<AdviceSingle<F, LagrangeCoeff>>, Vec<F>), Error>
where
    F: WithSmallOrderMulGroup<3> + Sampleable<T::Hash>,
    CS: PolynomialCommitmentScheme<F>,
    ConcreteCircuit: Circuit<F>,
    T: Transcript,
    CS::Commitment: Hashable<T::Hash>,
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
{
    let mut meta = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut meta, circuits[0].params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut meta);

    let domain = &pk.vk.domain;
    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;

    let mut advice = vec![
        AdviceSingle::<F, LagrangeCoeff> {
            advice_polys: vec![domain.empty_lagrange(); meta.num_advice_columns],
        };
        instances.len()
    ];
    let mut challenges = HashMap::<usize, F>::with_capacity(meta.num_challenges);

    let unusable_rows_start = domain.n as usize - (meta.blinding_factors() + 1);
    for current_phase in pk.vk.cs.phases() {
        let column_indices = meta
            .advice_column_phase
            .iter()
            .enumerate()
            .filter_map(|(column_index, phase)| {
                if current_phase == *phase {
                    Some(column_index)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();

        for ((circuit, advice), instances) in circuits.iter().zip(advice.iter_mut()).zip(instances)
        {
            let mut witness = WitnessCollection {
                k: domain.k(),
                current_phase,
                advice: vec![domain.empty_lagrange_rational(); meta.num_advice_columns],
                unblinded_advice: HashSet::from_iter(meta.unblinded_advice_columns.clone()),
                instances,
                challenges: &challenges,
                // The prover will not be allowed to assign values to advice
                // cells that exist within inactive rows, which include some
                // number of blinding factors and an extra row for use in the
                // permutation argument.
                usable_rows: ..unusable_rows_start,
                _marker: std::marker::PhantomData,
            };

            // Synthesize the circuit to obtain the witness and other information.
            ConcreteCircuit::FloorPlanner::synthesize(
                &mut witness,
                circuit,
                config.clone(),
                meta.constants.clone(),
            )?;

            let mut advice_values = batch_invert_rational::<F>(
                witness
                    .advice
                    .into_iter()
                    .enumerate()
                    .filter_map(|(column_index, advice)| {
                        if column_indices.contains(&column_index) {
                            Some(advice)
                        } else {
                            None
                        }
                    })
                    .collect(),
            );

            for (column_index, advice_values) in column_indices.iter().zip(&mut advice_values) {
                if !witness.unblinded_advice.contains(column_index) {
                    for cell in &mut advice_values[unusable_rows_start..] {
                        *cell = F::random(&mut rng);
                    }
                } else {
                    #[cfg(debug_assertions)]
                    for cell in &advice_values[unusable_rows_start..] {
                        assert_eq!(*cell, F::ZERO);
                    }
                }
            }

            let advice_commitments: Vec<_> =
                advice_values.iter().map(|poly| CS::commit_lagrange(params, poly)).collect();

            for commitment in &advice_commitments {
                transcript.write(commitment)?;
            }
            for (column_index, advice_values) in column_indices.iter().zip(advice_values) {
                advice.advice_polys[*column_index] = advice_values;
            }
        }

        for (index, phase) in meta.challenge_phase.iter().enumerate() {
            if current_phase == *phase {
                let existing = challenges.insert(index, transcript.squeeze_challenge());
                assert!(existing.is_none());
            }
        }
    }

    assert_eq!(challenges.len(), meta.num_challenges);
    let challenges = (0..meta.num_challenges)
        .map(|index| challenges.remove(&index).unwrap())
        .collect::<Vec<_>>();

    Ok((advice, challenges))
}

pub(super) fn compute_nu_poly<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<F>,
) -> Polynomial<F, ExtendedLagrangeCoeff> {
    let ProverTrace {
        advice_polys,
        instance_polys,
        lookups,
        trashcans,
        permutations,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
        ..
    } = &trace;
    // Calculate the advice and instance cosets
    let advice_cosets: Vec<Vec<Polynomial<F, ExtendedLagrangeCoeff>>> = advice_polys
        .iter()
        .map(|advice_polys| {
            advice_polys
                .iter()
                .map(|poly| pk.vk.get_domain().coeff_to_extended(poly.clone()))
                .collect()
        })
        .collect();
    let instance_cosets: Vec<Vec<Polynomial<F, ExtendedLagrangeCoeff>>> = instance_polys
        .iter()
        .map(|instance_polys| {
            instance_polys
                .iter()
                .map(|poly| pk.vk.get_domain().coeff_to_extended(poly.clone()))
                .collect()
        })
        .collect();

    // Evaluate the numerator polynomial nu(X) of the quotient polynomial
    // h(X) = nu(X) / (X^n-1): nu(X) is a random linear combination of all
    // independent identities
    pk.ev.evaluate_numerator::<ExtendedLagrangeCoeff>(
        &pk.vk.domain,
        &pk.vk.cs,
        &advice_cosets.iter().map(|a| a.as_slice()).collect::<Vec<_>>(),
        &instance_cosets.iter().map(|i| i.as_slice()).collect::<Vec<_>>(),
        &pk.fixed_cosets,
        challenges,
        *y,
        *beta,
        *gamma,
        *theta,
        *trash_challenge,
        lookups,
        trashcans,
        permutations,
        &pk.l0,
        &pk.l_last,
        &pk.l_active_row,
        &pk.permutation.cosets,
    )
}

#[allow(clippy::type_complexity)]
pub(super) fn write_evals_to_transcript<F, CS, T>(
    pk: &ProvingKey<F, CS>,
    nb_committed_instances: usize,
    instance_polys: &[Vec<Polynomial<F, Coeff>>],
    advice_polys: &[Vec<Polynomial<F, Coeff>>],
    x: F,
    transcript: &mut T,
) -> Result<(Vec<F>, Vec<Vec<F>>, Vec<Vec<F>>), Error>
where
    F: WithSmallOrderMulGroup<3> + Hashable<T::Hash>,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
{
    let domain = &pk.vk.domain;
    let meta = &pk.vk.cs;

    // Compute and hash evals for the polynomials of the committed instances of
    // each circuit
    let instance_evals: Vec<Vec<F>> = instance_polys
        .iter()
        .map(|instance| {
            // Evaluate polynomials at omega^i x
            meta.instance_queries
                .iter()
                .map(|&(column, at)| {
                    let eval =
                        eval_polynomial(&instance[column.index()], domain.rotate_omega(x, at));
                    if column.index() < nb_committed_instances {
                        transcript.write(&eval)?;
                    }
                    Ok(eval)
                })
                .collect::<Result<Vec<F>, Error>>()
        })
        .collect::<Result<Vec<_>, Error>>()?;

    // Compute and hash advice evals for each circuit instance
    let advice_evals: Vec<Vec<F>> = advice_polys
        .iter()
        .map(|advice| {
            // Evaluate polynomials at omega^i x
            meta.advice_queries
                .iter()
                .map(|&(column, at)| {
                    let eval = eval_polynomial(&advice[column.index()], domain.rotate_omega(x, at));
                    transcript.write(&eval).map(|_| Ok(eval))?
                })
                .collect::<Result<Vec<F>, Error>>()
        })
        .collect::<Result<Vec<_>, Error>>()?;

    // Compute evals of fixed columns (shared across all circuit instances),
    // and write them to the transcript
    //
    // NB: Fixed columns corresponding to simple, multiplicative selectors don't
    // need to be evaluated, nor written to the transcript
    let fixed_evals: Vec<F> = meta
        .fixed_queries
        .iter()
        .map(|&(column, at)| {
            let col_idx = column.index();
            if meta.selector_flags.contains(&col_idx) {
                Ok(F::ONE)
            } else {
                let eval = eval_polynomial(&pk.fixed_polys[col_idx], domain.rotate_omega(x, at));
                transcript.write(&eval).map(|_| Ok(eval))?
            }
        })
        .collect::<Result<Vec<F>, Error>>()?;

    Ok((fixed_evals, instance_evals, advice_evals))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compute_queries<
    'a,
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
>(
    pk: &'a ProvingKey<F, CS>,
    nb_committed_instances: usize,
    instance_polys: &'a [Vec<Polynomial<F, Coeff>>],
    advice_polys: &'a [Vec<Polynomial<F, Coeff>>],
    permutations: &'a [permutation::prover::Evaluated<F>],
    lookups: &'a [Vec<logup::prover::Evaluated<F>>],
    trashcans: &'a [Vec<trash::prover::Evaluated<F>>],
    x: F,
    linearization_poly: &'a Polynomial<F, Coeff>,
) -> Vec<ProverQuery<'a, F>> {
    let domain = pk.vk.get_domain();
    instance_polys
        .iter()
        .zip(advice_polys.iter())
        .zip(permutations.iter())
        .zip(lookups.iter())
        .zip(trashcans.iter())
        .flat_map(
            move |((((instance, advice), permutation), lookups), trash)| {
                iter::empty()
                    .chain(
                        pk.vk.cs.instance_queries.iter().filter_map(move |&(column, at)| {
                            if column.index() < nb_committed_instances {
                                Some(ProverQuery {
                                    point: domain.rotate_omega(x, at),
                                    poly: &instance[column.index()],
                                })
                            } else {
                                None
                            }
                        }),
                    )
                    .chain(
                        pk.vk.cs.advice_queries.iter().map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(x, at),
                            poly: &advice[column.index()],
                        }),
                    )
                    .chain(permutation.open(pk, x))
                    .chain(lookups.iter().flat_map(move |p| p.open(pk, x)))
                    .chain(trash.iter().flat_map(move |p| p.open(x)))
            },
        )
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                // Filter out queries for simple, multiplicative selectors
                .filter(|(col, _)| !pk.vk.cs.selector_flags.contains(&col.index()))
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(x, at),
                    poly: &pk.fixed_polys[column.index()],
                }),
        )
        .chain(pk.permutation.open(x))
        .chain(iter::once(ProverQuery {
            point: domain.rotate_omega(x, Rotation::cur()),
            poly: linearization_poly,
        }))
        .collect()
}

#[derive(Clone)]
pub(super) struct InstanceSingle<F: PrimeField> {
    pub instance_values: Vec<Polynomial<F, LagrangeCoeff>>,
    pub instance_polys: Vec<Polynomial<F, Coeff>>,
}

#[derive(Clone)]
pub(super) struct AdviceSingle<F: PrimeField, B: PolynomialRepresentation> {
    pub advice_polys: Vec<Polynomial<F, B>>,
}

struct WitnessCollection<'a, F: Field> {
    k: u32,
    current_phase: sealed::Phase,
    advice: Vec<Polynomial<Rational<F>, LagrangeCoeff>>,
    unblinded_advice: HashSet<usize>,
    challenges: &'a HashMap<usize, F>,
    instances: &'a [&'a [F]],
    usable_rows: RangeTo<usize>,
    _marker: std::marker::PhantomData<F>,
}

impl<F: Field> Assignment<F> for WitnessCollection<'_, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here

        Ok(())
    }

    fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.instances
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Ignore assignment of advice column in different phase than current one.
        if self.current_phase != column.column_type().phase {
            return Ok(());
        }

        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .advice
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here

        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        // We only care about advice columns here

        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Rational<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, challenge: Challenge) -> Value<F> {
        self.challenges
            .get(&challenge.index())
            .cloned()
            .map(Value::known)
            .unwrap_or_else(Value::unknown)
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

#[test]
#[cfg(feature = "dev-curves")]
fn test_create_proof() {
    use midnight_curves::bn256::{Bn256, Fr};
    use rand_core::OsRng;

    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk_with_k},
        poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
        transcript::CircuitTranscript,
    };

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    const K: u32 = 4;
    let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(K, OsRng);
    let vk = keygen_vk_with_k(&params, &MyCircuit, K).expect("keygen_vk should not fail");
    let pk = keygen_pk(vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = CircuitTranscript::<_>::init();

    // Create proof with wrong number of instances
    let proof = create_proof::<Fr, KZGCommitmentScheme<Bn256>, _, _>(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        #[cfg(feature = "committed-instances")]
        0,
        &[],
        OsRng,
        &mut transcript,
    );
    assert!(matches!(proof.unwrap_err(), Error::InvalidInstances));

    // Create proof with correct number of instances
    create_proof::<Fr, KZGCommitmentScheme<Bn256>, _, _>(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        #[cfg(feature = "committed-instances")]
        0,
        &[&[], &[]],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
}

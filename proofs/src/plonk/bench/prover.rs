//! Benchmarking utilities for the PLONK prover.

use std::hash::Hash;

use criterion::BenchmarkGroup;
use ff::{FromUniformBytes, WithSmallOrderMulGroup};

use crate::{
    plonk::{
        circuit::Circuit,
        lookup, permutation, trash, vanishing,
        prover::{compute_h_poly, compute_instances, compute_queries, parse_advices, write_evals_to_transcript},
        traces::ProverTrace,
        Error, ProvingKey,
    },
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Sampleable, Transcript},
};
use rand_core::{CryptoRng, RngCore};

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

    let (advice, challenges) = parse_advices(params, pk, circuits, instances, transcript, &mut rng)?;

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    let lookups: Vec<Vec<lookup::prover::Permuted<F>>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| -> Result<Vec<_>, Error> {
            // Construct and commit to permuted values for each lookup
            pk.vk
                .cs
                .lookups
                .iter()
                .map(|lookup| {
                    lookup.commit_permuted(
                        pk,
                        params,
                        domain,
                        theta,
                        &advice.advice_polys,
                        &pk.fixed_values,
                        &instance.instance_values,
                        &challenges,
                        &mut rng,
                        transcript,
                    )
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;

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

    let lookups: Vec<Vec<lookup::prover::Committed<F>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            // Construct and commit to products for each lookup
            lookups
                .into_iter()
                .map(|lookup| lookup.commit_product(pk, params, beta, gamma, &mut rng, transcript))
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

    // Commit to the vanishing argument's random polynomial for blinding h(x_3)
    let vanishing = vanishing::Argument::<F, CS>::commit(params, domain, &mut rng, transcript)?;

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
        vanishing,
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

    let domain = pk.get_vk().get_domain();

    let h_poly = compute_h_poly(pk, &trace);

    let ProverTrace {
        advice_polys,
        instance_polys,
        lookups,
        trashcans,
        permutations,
        vanishing,
        ..
    } = trace;

    // Construct the vanishing argument's h(X) commitments
    let vanishing = vanishing.construct::<CS, T>(params, domain, h_poly, transcript)?;

    let x: F = transcript.squeeze_challenge();

    write_evals_to_transcript(
        pk,
        nb_committed_instances,
        &instance_polys,
        &advice_polys,
        x,
        transcript,
    )?;

    let vanishing = vanishing.evaluate(x, domain, transcript)?;

    // Evaluate common permutation data
    pk.permutation.evaluate(x, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let permutations: Vec<permutation::prover::Evaluated<F>> = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> { permutation.evaluate(pk, x, transcript) })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<Vec<lookup::prover::Evaluated<F>>> = lookups
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

    let queries = compute_queries(
        pk,
        nb_committed_instances,
        &instance_polys,
        &advice_polys,
        &permutations,
        &lookups,
        &trashcans,
        &vanishing,
        x,
    );

    CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

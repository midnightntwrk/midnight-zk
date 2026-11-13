//! Benchmarking utilities for the PLONK prover.

use std::{collections::BTreeMap, hash::Hash};

use criterion::BenchmarkGroup;
use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use crate::{
    plonk::{
        Error, ProvingKey, argument,
        circuit::Circuit,
        prover::{
            compute_h_poly, compute_instances, compute_logderivatives, compute_multiplicities,
            compute_nu_poly, compute_queries, parse_advices, phase1_polys, phase2_polys,
            write_instance_evals_to_transcript,
        },
        traces::ProverTrace,
    },
    poly::{PolynomialLabel, Rotation, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// This computes a proof trace for the provided `circuit` when given the
/// public parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// The trace can then be used to finalise the proof.
///
/// Benchmarks individual internal steps using the provided `group`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_trace<
    'a,
    F,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<F, CS>,
    circuit: &ConcreteCircuit,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[F]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
    group: &mut BenchmarkGroup<'_, criterion::measurement::WallTime>,
) -> Result<ProverTrace<'a, F>, Error>
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

    if instances.len() != pk.vk.cs.num_instance_columns || instances.len() < nb_committed_instances
    {
        return Err(Error::InvalidInstances);
    }

    // Hash verification key into transcript
    group.bench_function("Hash VK", |b| {
        b.iter_batched(
            || transcript.clone(),
            |mut t| {
                let _ = pk.vk.hash_into(&mut t);
            },
            criterion::BatchSize::SmallInput,
        )
    });
    let vk_absorbed = pk.vk.absorb_into(transcript)?;
    let phase0_committed = pk.phase0_polys.committed(&vk_absorbed);

    let domain = &pk.vk.domain;

    let instance = {
        let instances_clone = instances.to_vec();
        group.bench_function("Compute instances", |b| {
            b.iter_batched(
                || (transcript.clone(), instances_clone.clone()),
                |(mut t, inst)| {
                    let _ = compute_instances::<F, CS, T>(
                        params,
                        pk,
                        &inst,
                        nb_committed_instances,
                        &mut t,
                    );
                },
                criterion::BatchSize::SmallInput,
            )
        });
        compute_instances(params, pk, instances, nb_committed_instances, transcript)?
    };

    let advice_polys = {
        group.bench_function("Parse advices", |b| {
            b.iter(|| {
                let _ = parse_advices::<F, CS, ConcreteCircuit>(pk, circuit, instances, &mut rng);
            })
        });
        parse_advices(pk, circuit, instances, &mut rng)?
    };

    // Pre-generate multiplicities blindings so the measured closures don't need
    // `&mut rng`. One extra value beyond `blinding_factors` is required by
    // `compute_multiplicities` (see the assert on `table.len() - usable_rows`).
    let num_lookups = pk.vk.cs.lookups.len();
    let mult_blinding_count = pk.vk.cs.blinding_factors() + 1;
    let mult_blindings: Vec<Vec<F>> = (0..num_lookups)
        .map(|_| (0..mult_blinding_count).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Compute the multiplicities columns and commit to them as the phase1
    // argument group: one commitment over every multiplicities polynomial,
    // rather than one per lookup argument. Compute and transcript write are
    // separate API calls — measure them together to match the prior
    // `commit_multiplicities` shape.
    let advice_labels = pk.vk.cs.advice_labels();
    let (multiplicities, phase1_committed) = {
        group.bench_function("Commit advices and lookup multiplicities", |b| {
            b.iter_batched(
                || {
                    (
                        transcript.clone(),
                        mult_blindings.clone(),
                        advice_polys.clone(),
                    )
                },
                |(mut t, mult_blinds, advice_polys)| -> Result<(), Error> {
                    let (_, multiplicities_polys) = compute_multiplicities(
                        pk,
                        &advice_polys,
                        &instance.instance_values,
                        &mult_blinds,
                    )?;
                    argument::prover::Committed::commit::<CS, _>(
                        params,
                        phase1_polys(&pk.vk.cs, advice_polys, multiplicities_polys)?,
                        &mut t,
                    )?;
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });
        let (multiplicities, multiplicities_polys) = compute_multiplicities(
            pk,
            &advice_polys,
            &instance.instance_values,
            &mult_blindings,
        )?;
        let committed = argument::prover::Committed::commit::<CS, T>(
            params,
            phase1_polys(&pk.vk.cs, advice_polys, multiplicities_polys)?,
            transcript,
        )?;
        (multiplicities, committed)
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    // Sample the trash challenge after the advices have been committed to
    let trash_challenge: F = transcript.squeeze_challenge();

    // Pre-generate permutation blindings for the per-iteration compute.
    let blinding_factors = pk.vk.cs.blinding_factors();
    let chunk_len = pk.vk.cs_degree - 2;
    let num_perm_sets = pk.vk.cs.permutation.columns.chunks(chunk_len).len();
    let perm_blindings: Vec<Vec<F>> = (0..num_perm_sets)
        .map(|_| (0..blinding_factors).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Compute the permutation accumulators.
    let compute_perm_z_polys = |perm_blindings: Vec<Vec<F>>| {
        pk.vk.cs.permutation.compute_z_polys::<F, CS>(
            pk,
            phase1_committed.polys_of(&advice_labels),
            &pk.fixed_values,
            &instance.instance_values,
            beta,
            gamma,
            perm_blindings,
        )
    };

    let perm_z_polys = {
        group.bench_function("Compute permutation accumulators", |b| {
            b.iter_batched(
                || perm_blindings.clone(),
                compute_perm_z_polys,
                criterion::BatchSize::LargeInput,
            )
        });
        compute_perm_z_polys(perm_blindings)
    };

    // Pre-generate logderivative blindings, one vector per lookup.
    let logup_blindings: Vec<Vec<F>> = (0..num_lookups)
        .map(|_| (0..blinding_factors).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Construct the lookup product polynomials. They are committed further
    // below, as part of the phase2 argument group.
    let logderivatives = {
        group.bench_function("Compute lookup products", |b| {
            b.iter_batched(
                || (multiplicities.clone(), logup_blindings.clone()),
                |(multiplicities, blinds)| {
                    compute_logderivatives(
                        pk,
                        multiplicities,
                        &phase1_committed,
                        theta,
                        beta,
                        blinds,
                    )
                },
                criterion::BatchSize::LargeInput,
            )
        });
        compute_logderivatives(
            pk,
            multiplicities,
            &phase1_committed,
            theta,
            beta,
            logup_blindings,
        )?
    };

    // Phase2 argument group: the logup helper and aggregator polynomials
    // together with the trash polynomials, under a single commitment.
    //
    // CAVEAT: this stage used to commit the trash polynomials alone. It now
    // covers the logup polynomials too, so its cost is not comparable with the
    // same line from earlier revisions.
    let phase2_committed = {
        group.bench_function("Commit phase2 arguments", |b| {
            b.iter_batched(
                || {
                    (
                        transcript.clone(),
                        logderivatives.clone(),
                        perm_z_polys.clone(),
                    )
                },
                |(mut t, logderivatives, perm_z_polys)| -> Result<(), Error> {
                    let polys = phase2_polys(
                        pk,
                        perm_z_polys,
                        logderivatives,
                        trash_challenge,
                        phase1_committed.polys_of(&advice_labels),
                        &instance.instance_values,
                    )?;
                    argument::prover::Committed::commit::<CS, _>(params, polys, &mut t)?;
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });

        let polys = phase2_polys(
            pk,
            perm_z_polys,
            logderivatives,
            trash_challenge,
            phase1_committed.polys_of(&advice_labels),
            &instance.instance_values,
        )?;
        argument::prover::Committed::commit::<CS, T>(params, polys, transcript)?
    };

    // Obtain challenge for keeping all separate gates linearly independent
    let y: F = transcript.squeeze_challenge();

    let instance_polys = instance.instance_polys;
    let instance_values = instance.instance_values;

    let phase1_committed = phase1_committed.into_coeff(domain);
    let phase2_committed = phase2_committed.into_coeff(domain);

    Ok(ProverTrace {
        instance_polys,
        instance_values,
        phase0_committed,
        phase1_committed,
        phase2_committed,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    })
}

/// This takes the computed trace of a witness and creates a proof
/// for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// Benchmarks individual internal steps using the provided `group`.
pub(crate) fn finalise_proof<'a, F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    params: &'a CS::Parameters,
    pk: &'a ProvingKey<F, CS>,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    trace: ProverTrace<'a, F>,
    transcript: &mut T,
    group: &mut BenchmarkGroup<'_, criterion::measurement::WallTime>,
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

    let nu_poly = {
        group.bench_function("Compute numerator poly", |b| {
            b.iter(|| {
                let _ = compute_nu_poly(pk, &trace);
            })
        });
        compute_nu_poly(pk, &trace)
    };

    // Construct the quotient polynomial h(X) = nu(X)/(X^n-1), split it into
    // limbs and commit to the limbs as one group.
    let quotient_committed = {
        group.bench_function("Compute quotient poly", |b| {
            b.iter_batched(
                || transcript.clone(),
                |mut t| {
                    let _ = compute_h_poly::<F, CS, T>(
                        params,
                        pk.get_vk().get_domain(),
                        nu_poly.clone(),
                        &mut t,
                    );
                },
                criterion::BatchSize::SmallInput,
            )
        });
        compute_h_poly::<F, CS, T>(params, pk.get_vk().get_domain(), nu_poly, transcript)?
    };

    let ProverTrace {
        instance_polys,
        phase0_committed,
        phase1_committed,
        phase2_committed,
        ..
    } = trace;

    // PCS-aware squeeze (see plonk/prover.rs).
    let x: F = CS::squeeze_evaluation_point(transcript);

    let domain = pk.vk.get_domain();
    let cs = pk.vk.cs();
    let x_rotations: BTreeMap<Rotation, F> = argument::rotations(cs)
        .into_iter()
        .map(|rotation| (rotation, domain.rotate_omega(x, rotation)))
        .collect();

    group.bench_function("Write evals to transcript", |b| {
        b.iter_batched(
            || transcript.clone(),
            |mut t| {
                let _ = write_instance_evals_to_transcript(
                    pk,
                    nb_committed_instances,
                    &instance_polys,
                    &x_rotations,
                    &mut t,
                );
            },
            criterion::BatchSize::SmallInput,
        )
    });
    write_instance_evals_to_transcript(
        pk,
        nb_committed_instances,
        &instance_polys,
        &x_rotations,
        transcript,
    )?;

    // Evaluate the fixed permutation polynomials, committed to in the verifying
    // key.
    group.bench_function("Evaluate permutation data", |b| {
        b.iter_batched(
            || transcript.clone(),
            |mut t| {
                let _ = phase0_committed.evaluate(cs, &x_rotations, &mut t);
            },
            criterion::BatchSize::SmallInput,
        )
    });
    let phase0_evaluated = phase0_committed.evaluate(cs, &x_rotations, transcript)?;

    // Evaluate the phase1 and phase2 arguments, if any, at their opening points.
    let phase1_evaluated = phase1_committed.evaluate(cs, &x_rotations, transcript)?;
    let phase2_evaluated = phase2_committed.evaluate(cs, &x_rotations, transcript)?;
    let mut quotient_evaluated = quotient_committed.evaluate(cs, &x_rotations, transcript)?;

    // h_0(x) is not written to the proof, the verifier derives it.
    let h0 = PolynomialLabel::QuotientPiece(0);
    let h0_eval = eval_polynomial(
        quotient_committed.poly(&h0).expect("a quotient limb h_0"),
        x,
    );
    quotient_evaluated.insert(h0, x, h0_eval);

    let instance_labels: Vec<_> = (0..nb_committed_instances)
        .map(|i| [PolynomialLabel::CommittedInstance(i)])
        .collect();
    let queries = {
        group.bench_function("Compute queries", |b| {
            b.iter(|| {
                let _ = compute_queries(
                    pk,
                    &instance_labels,
                    &instance_polys,
                    &phase0_evaluated,
                    &phase1_evaluated,
                    &phase2_evaluated,
                    &quotient_evaluated,
                    &x_rotations,
                );
            })
        });
        compute_queries(
            pk,
            &instance_labels,
            &instance_polys,
            &phase0_evaluated,
            &phase1_evaluated,
            &phase2_evaluated,
            &quotient_evaluated,
            &x_rotations,
        )
    };

    group.bench_function("Multi open argument", |b| {
        b.iter_batched(
            || (transcript.clone(), queries.clone()),
            |(mut t, q)| {
                let _ = CS::multi_open(params, &q, &mut t);
            },
            criterion::BatchSize::SmallInput,
        )
    });
    CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

/// Benchmarked version of proof creation that measures each internal step.
///
/// This function simply calls `compute_trace` and `finalise_proof` with the
/// provided benchmark group, which causes those functions to benchmark their
/// internal steps.
#[allow(clippy::too_many_arguments)]
pub fn benchmark_create_proof<
    F,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuit: &ConcreteCircuit,
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[F]],
    transcript: &mut T,
    rng: &mut (impl RngCore + CryptoRng),
    group: &mut BenchmarkGroup<'_, criterion::measurement::WallTime>,
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

    let trace = compute_trace(
        params,
        pk,
        circuit,
        #[cfg(feature = "committed-instances")]
        nb_committed_instances,
        instances,
        transcript,
        rng,
        group,
    )?;

    finalise_proof(
        params,
        pk,
        #[cfg(feature = "committed-instances")]
        nb_committed_instances,
        trace,
        transcript,
        group,
    )
}

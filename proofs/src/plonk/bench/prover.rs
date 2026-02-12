//! Benchmarking utilities for the PLONK prover.

use std::hash::Hash;

use criterion::BenchmarkGroup;
use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use crate::{
    plonk::{
        circuit::Circuit,
        linearization::prover::compute_linearization_poly,
        logup, partially_evaluate_identities, permutation,
        prover::{
            compute_h_poly, compute_instances, compute_nu_poly, compute_queries, parse_advices,
            write_evals_to_transcript,
        },
        traces::ProverTrace,
        trash, Error, ProvingKey,
    },
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// This computes a proof trace for the provided `circuits` when given the
/// public parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// The trace can then be used to finalise proofs, or to fold them.
///
/// Benchmarks individual internal steps using the provided `group`.
#[allow(clippy::too_many_arguments)]
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
    group: &mut BenchmarkGroup<criterion::measurement::WallTime>,
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
    group.bench_function("Hash VK", |b| {
        b.iter_batched(
            || transcript.clone(),
            |mut t| {
                let _ = pk.vk.hash_into(&mut t);
            },
            criterion::BatchSize::SmallInput,
        )
    });
    pk.vk.hash_into(transcript)?;

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

    let (advice, challenges) = {
        group.bench_function("Parse advices", |b| {
            b.iter_batched(
                || transcript.clone(),
                |mut t| {
                    let _ = parse_advices::<F, CS, ConcreteCircuit, T>(
                        params, pk, circuits, instances, &mut t, &mut rng,
                    );
                },
                criterion::BatchSize::LargeInput,
            )
        });
        parse_advices(params, pk, circuits, instances, transcript, &mut rng)?
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    // Commit to the multiplicities columns
    let lookups: Vec<Vec<logup::prover::ComputedMultiplicities<F>>> = {
        group.bench_function("Commit lookup products", |b| {
            b.iter_batched(
                || transcript.clone(),
                |mut t| {
                    let _: Result<Vec<Vec<_>>, _> = instance
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
                                        &mut t,
                                    )
                                })
                                .collect::<Result<Vec<_>, Error>>()
                        })
                        .collect();
                },
                criterion::BatchSize::LargeInput,
            )
        });
        instance
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
            .collect::<Result<Vec<_>, Error>>()?
    };

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    // Commit to permutations
    let permutations: Vec<permutation::prover::Committed<F>> = {
        group.bench_function("Commit permutations", |b| {
            b.iter_batched(
                || (transcript.clone(), instance.clone(), advice.clone()),
                |(mut t, inst, adv)| {
                    let _: Result<Vec<_>, _> = inst
                        .iter()
                        .zip(adv.iter())
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
                                &mut t,
                            )
                        })
                        .collect();
                },
                criterion::BatchSize::LargeInput,
            )
        });
        instance
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
            .collect::<Result<Vec<_>, _>>()?
    };

    // Construct and commit to lookup product polynomials
    let lookups: Vec<Vec<logup::prover::Committed<F>>> = {
        group.bench_function("Commit lookup products", |b| {
            b.iter_batched(
                || transcript.clone(),
                |mut t| {
                    let _: Result<Vec<Vec<_>>, _> = lookups
                        .clone()
                        .into_iter()
                        .map(|lookups| -> Result<Vec<_>, _> {
                            // Construct and commit to products polynomials for each lookup
                            lookups
                                .into_iter()
                                .map(|lookup| {
                                    lookup.commit_logderivative(pk, params, beta, &mut rng, &mut t)
                                })
                                .collect::<Result<Vec<_>, _>>()
                        })
                        .collect();
                },
                criterion::BatchSize::LargeInput,
            )
        });
        lookups
            .into_iter()
            .map(|lookups| -> Result<Vec<_>, _> {
                // Construct and commit to products polynomials for each lookup
                lookups
                    .into_iter()
                    .map(|lookup| {
                        lookup.commit_logderivative(pk, params, beta, &mut rng, transcript)
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    // Trash argument
    let trash_challenge: F = transcript.squeeze_challenge();

    let trashcans: Vec<Vec<trash::prover::Committed<F>>> = {
        group.bench_function("Commit trash arguments", |b| {
            b.iter_batched(
                || (transcript.clone(), instance.clone(), advice.clone()),
                |(mut t, inst, adv)| {
                    let _: Result<Vec<Vec<_>>, _> = inst
                        .iter()
                        .zip(adv.iter())
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
                                        &mut t,
                                    )
                                })
                                .collect()
                        })
                        .collect();
                },
                criterion::BatchSize::LargeInput,
            )
        });
        instance
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
            .collect::<Result<Vec<_>, _>>()?
    };

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
///
/// Benchmarks individual internal steps using the provided `group`.
pub(crate) fn finalise_proof<'a, F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    params: &'a CS::Parameters,
    pk: &'a ProvingKey<F, CS>,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    trace: ProverTrace<F>,
    transcript: &mut T,
    group: &mut BenchmarkGroup<criterion::measurement::WallTime>,
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

    let quotient_limbs = {
        group.bench_function("Compute quotient poly", |b| {
            b.iter(|| {
                let _ = compute_h_poly::<F, CS, T>(
                    params,
                    pk.get_vk().get_domain(),
                    nu_poly.clone(),
                    transcript,
                );
            })
        });
        compute_h_poly::<F, CS, T>(params, pk.get_vk().get_domain(), nu_poly, transcript)?
    };

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

    group.bench_function("Write evals to transcript", |b| {
        b.iter_batched(
            || transcript.clone(),
            |mut t| {
                let _ = write_evals_to_transcript(
                    pk,
                    nb_committed_instances,
                    &instance_polys,
                    &advice_polys,
                    x,
                    &mut t,
                );
            },
            criterion::BatchSize::SmallInput,
        )
    });
    let (fixed_evals, instance_evals, advice_evals) = write_evals_to_transcript(
        pk,
        nb_committed_instances,
        &instance_polys,
        &advice_polys,
        x,
        transcript,
    )?;

    // Evaluate common permutation data
    group.bench_function("Evaluate permutation data", |b| {
        b.iter_batched(
            || transcript.clone(),
            |mut t| {
                let _ = pk.permutation.evaluate(x, &mut t);
            },
            criterion::BatchSize::SmallInput,
        )
    });
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
    let expressions = {
        group.bench_function("Partially evaluate identities", |b| {
            b.iter(|| {
                let _ = partially_evaluate_identities(
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
            })
        });
        partially_evaluate_identities(
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
        )
    };

    // Compute linearization polynomial
    let linearization_poly = {
        group.bench_function("Compute linearization poly", |b| {
            b.iter(|| {
                let _ = compute_linearization_poly(
                    expressions.clone(),
                    pk,
                    y,
                    xn,
                    splitting_factor,
                    quotient_limbs.clone(),
                );
            })
        });
        compute_linearization_poly(expressions, pk, y, xn, splitting_factor, quotient_limbs)
    };

    debug_assert_eq!(
        eval_polynomial(&linearization_poly, x),
        F::ZERO,
        "The linearization poly should evaluate to zero at the evaluation challenge x."
    );

    let queries = {
        group.bench_function("Compute queries", |b| {
            b.iter(|| {
                let _ = compute_queries(
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
            })
        });
        compute_queries(
            pk,
            nb_committed_instances,
            &instance_polys,
            &advice_polys,
            &permutations,
            &lookups,
            &trashcans,
            x,
            &linearization_poly,
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
    circuits: &[ConcreteCircuit],
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[&[F]]],
    rng: impl RngCore + CryptoRng,
    transcript: &mut T,
    group: &mut BenchmarkGroup<criterion::measurement::WallTime>,
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
        circuits,
        #[cfg(feature = "committed-instances")]
        nb_committed_instances,
        instances,
        rng,
        transcript,
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

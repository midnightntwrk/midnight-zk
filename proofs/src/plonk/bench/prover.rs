//! Benchmarking utilities for the PLONK prover.

use std::hash::Hash;

use criterion::BenchmarkGroup;
use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{
        circuit::Circuit,
        linearization::prover::compute_linearization_poly,
        logup, partially_evaluate_identities,
        prover::{
            compute_h_poly, compute_instances, compute_nu_poly, compute_queries, parse_advices,
            write_evals_to_transcript, Evals,
        },
        traces::ProverTrace,
        trash, Error, ProvingKey,
    },
    poly::commitment::PolynomialCommitmentScheme,
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
    F,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuit: &ConcreteCircuit,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[F]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
    group: &mut BenchmarkGroup<'_, criterion::measurement::WallTime>,
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
                        params, pk, circuit, instances, &mut t, &mut rng,
                    );
                },
                criterion::BatchSize::LargeInput,
            )
        });
        parse_advices(params, pk, circuit, instances, transcript, &mut rng)?
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    // Pre-generate multiplicities blindings so the measured closures don't need
    // `&mut rng`. One extra value beyond `blinding_factors` is required by
    // `compute_multiplicities` (see the assert on `table.len() - usable_rows`).
    let num_lookups = pk.vk.cs.lookups.len();
    let mult_blinding_count = pk.vk.cs.blinding_factors() + 1;
    let mult_blindings: Vec<Vec<F>> = (0..num_lookups)
        .map(|_| (0..mult_blinding_count).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Commit to the multiplicities columns. Compute and transcript write are
    // now separate API calls — measure them together to match the prior
    // `commit_multiplicities` shape.
    let lookups: Vec<logup::prover::ComputedMultiplicities<F>> = {
        group.bench_function("Commit lookup multiplicities", |b| {
            b.iter_batched(
                || (transcript.clone(), mult_blindings.clone()),
                |(mut t, mult_blinds)| -> Result<(), Error> {
                    let logup_args: Vec<_> = pk
                        .vk
                        .cs
                        .lookups
                        .iter()
                        .map(|l| l.chunk_by_degree(pk.vk.cs.degree()))
                        .collect();
                    let results: Vec<_> = logup_args
                        .par_iter()
                        .zip(mult_blinds.par_iter())
                        .map(|(logup, blinds)| {
                            logup.compute_multiplicities_parallel(
                                pk,
                                params,
                                theta,
                                &advice.advice_polys,
                                &pk.fixed_values,
                                &instance.instance_values,
                                &challenges,
                                blinds,
                            )
                        })
                        .collect::<Result<Vec<_>, Error>>()?;
                    for (_, commitment) in &results {
                        t.write(commitment)?;
                    }
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });
        let logup_args: Vec<_> =
            pk.vk.cs.lookups.iter().map(|l| l.chunk_by_degree(pk.vk.cs.degree())).collect();
        let results: Vec<_> = logup_args
            .par_iter()
            .zip(mult_blindings.par_iter())
            .map(|(logup, blinds)| {
                logup.compute_multiplicities_parallel(
                    pk,
                    params,
                    theta,
                    &advice.advice_polys,
                    &pk.fixed_values,
                    &instance.instance_values,
                    &challenges,
                    blinds,
                )
            })
            .collect::<Result<Vec<_>, Error>>()?;
        results
            .into_iter()
            .map(|(c, commitment)| {
                transcript.write(&commitment)?;
                Ok::<_, Error>(c)
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    // Pre-generate permutation blindings for the per-iteration compute.
    let blinding_factors = pk.vk.cs.blinding_factors();
    let chunk_len = pk.vk.cs_degree - 2;
    let num_perm_sets = pk.vk.cs.permutation.columns.chunks(chunk_len).len();
    let perm_blindings: Vec<Vec<F>> = (0..num_perm_sets)
        .map(|_| (0..blinding_factors).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Commit to permutations. `Argument::compute` returns z polys + commitments
    // without touching the transcript; `write_and_convert` then writes
    // commitments and converts to coefficient form. Measure both together.
    //
    // CAVEAT: in `create_proof` this phase runs inside a `rayon::join` with the
    // logup logderivative compute, so permutation and logup overlap in wall
    // time. This benchmark measures each phase in isolation, so the sum of
    // "Commit permutations" + "Commit lookup products" overstates the combined
    // cost versus what `create_proof` actually pays.
    let permutations = {
        group.bench_function("Commit permutations", |b| {
            b.iter_batched(
                || (transcript.clone(), perm_blindings.clone()),
                |(mut t, perm_blinds)| -> Result<(), Error> {
                    let computed = pk.vk.cs.permutation.compute::<F, CS>(
                        params,
                        pk,
                        &pk.permutation,
                        &advice.advice_polys,
                        &pk.fixed_values,
                        &instance.instance_values,
                        beta,
                        gamma,
                        perm_blinds,
                    );
                    let _ = computed.write_and_convert(domain, &mut t)?;
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });
        let computed = pk.vk.cs.permutation.compute::<F, CS>(
            params,
            pk,
            &pk.permutation,
            &advice.advice_polys,
            &pk.fixed_values,
            &instance.instance_values,
            beta,
            gamma,
            perm_blindings,
        );
        computed.write_and_convert(domain, transcript)?
    };

    // Pre-generate logderivative blindings, one vector per lookup.
    let logup_blindings: Vec<Vec<F>> = (0..lookups.len())
        .map(|_| (0..blinding_factors).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Construct and commit to lookup product polynomials.
    // `compute_logderivative` returns helper_polys_lagrange + aggregator
    // commitment without transcript writes. Helper commitments must be taken
    // and written here, and Lagrange polys converted to coefficient form.
    let lookups: Vec<logup::prover::Committed<F>> = {
        group.bench_function("Commit lookup products", |b| {
            b.iter_batched(
                || (transcript.clone(), lookups.clone(), logup_blindings.clone()),
                |(mut t, lookups, logup_blinds)| -> Result<(), Error> {
                    let computed: Vec<_> = lookups
                        .into_par_iter()
                        .zip(logup_blinds.into_par_iter())
                        .map(|(lookup, blinds)| {
                            lookup.compute_logderivative(pk, params, beta, blinds)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let all_helper_commitments: Vec<Vec<CS::Commitment>> = computed
                        .par_iter()
                        .map(|c| {
                            c.helper_polys_lagrange
                                .par_iter()
                                .map(|h| {
                                    let h_poly = domain.lagrange_from_vec(h.clone());
                                    CS::commit(params, &h_poly)
                                })
                                .collect()
                        })
                        .collect();
                    for (c, helper_commitments) in
                        computed.iter().zip(all_helper_commitments.iter())
                    {
                        for h_commitment in helper_commitments {
                            t.write(h_commitment)?;
                        }
                        t.write(&c.aggregator_commitment)?;
                    }
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });
        let computed: Vec<_> = lookups
            .into_par_iter()
            .zip(logup_blindings.into_par_iter())
            .map(|(lookup, blinds)| lookup.compute_logderivative(pk, params, beta, blinds))
            .collect::<Result<Vec<_>, _>>()?;
        let all_helper_commitments: Vec<Vec<CS::Commitment>> = computed
            .par_iter()
            .map(|c| {
                c.helper_polys_lagrange
                    .par_iter()
                    .map(|h| {
                        let h_poly = domain.lagrange_from_vec(h.clone());
                        CS::commit(params, &h_poly)
                    })
                    .collect()
            })
            .collect();
        for (c, helper_commitments) in computed.iter().zip(all_helper_commitments.iter()) {
            for h_commitment in helper_commitments {
                transcript.write(h_commitment)?;
            }
            transcript.write(&c.aggregator_commitment)?;
        }
        computed
            .into_par_iter()
            .map(|c| {
                let helper_polys = c
                    .helper_polys_lagrange
                    .into_iter()
                    .map(|h| domain.lagrange_to_coeff(domain.lagrange_from_vec(h)))
                    .collect();
                logup::prover::Committed {
                    multiplicities: domain.lagrange_to_coeff(c.multiplicities),
                    helper_polys,
                    aggregator_poly: domain.lagrange_to_coeff(c.aggregator_poly),
                }
            })
            .collect()
    };

    // Trash argument
    let trash_challenge: F = transcript.squeeze_challenge();

    let trashcans: Vec<trash::prover::Committed<F>> = {
        group.bench_function("Commit trash arguments", |b| {
            b.iter_batched(
                || (transcript.clone(), instance.clone(), advice.clone()),
                |(mut t, inst, adv)| {
                    let _: Result<Vec<_>, _> = pk
                        .vk
                        .cs
                        .trashcans
                        .iter()
                        .map(|trash| {
                            trash.commit::<CS, _>(
                                params,
                                domain,
                                trash_challenge,
                                &adv.advice_polys,
                                &pk.fixed_values,
                                &inst.instance_values,
                                &challenges,
                                &mut t,
                            )
                        })
                        .collect();
                },
                criterion::BatchSize::LargeInput,
            )
        });
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
            .collect::<Result<Vec<_>, _>>()?
    };

    // Obtain challenge for keeping all separate gates linearly independent
    let y: F = transcript.squeeze_challenge();

    let instance_polys = instance.instance_polys;
    let instance_values = instance.instance_values;

    let advice_polys: Vec<_> =
        advice.advice_polys.into_iter().map(|p| domain.lagrange_to_coeff(p)).collect();

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
    trace: ProverTrace<F>,
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

    // Construct the quotient polynomial h(X) = nu(X)/(X^n-1) and commit.
    // When `single-h-commitment` is enabled this produces a single commitment;
    // otherwise h(X) is split into limbs and each is committed separately.
    let quotient_limbs = {
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
    let Evals {
        fixed_evals,
        instance_evals,
        advice_evals,
        ..
    } = write_evals_to_transcript(
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
    let permutations = permutations.evaluate(pk, x, transcript)?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<logup::prover::Evaluated<F>> = lookups
        .into_iter()
        .map(|p| p.evaluate(pk, x, transcript))
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the trashcans, if any, at x.
    let trashcans: Vec<trash::prover::Evaluated<F>> = trashcans
        .into_iter()
        .map(|p| p.evaluate(x, transcript))
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
                    &permutations.evaluated,
                    lookups.iter().map(|inner| &inner.evaluated),
                    trashcans.iter().map(|inner| &inner.evaluated),
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
            &permutations.evaluated,
            lookups.iter().map(|inner| &inner.evaluated),
            trashcans.iter().map(|inner| &inner.evaluated),
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
    let (lin_poly_non_constant_part, lin_poly_constant_term) = {
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
        eval_polynomial(&lin_poly_non_constant_part, x),
        -lin_poly_constant_term,
        "L'(x) should equal -C, where C is the constant part of the linearization polynomial"
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
                    &lin_poly_non_constant_part,
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
            &lin_poly_non_constant_part,
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

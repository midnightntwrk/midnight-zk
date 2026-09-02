//! Benchmarking utilities for the PLONK prover.

use std::{collections::BTreeMap, hash::Hash};

use criterion::BenchmarkGroup;
use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{
        Error, ProvingKey, argument,
        circuit::Circuit,
        linearization::prover::compute_linearization_poly,
        logup, partially_evaluate_identities,
        prover::{
            Evals, compute_h_poly, compute_instances, compute_nu_poly, compute_queries,
            parse_advices, write_evals_to_transcript,
        },
        traces::ProverTrace,
    },
    poly::{LagrangeCoeff, Polynomial, PolynomialLabel, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// The polynomials of one argument phase group, keyed by their label.
type PhaseGroupPolys<F> = BTreeMap<PolynomialLabel, Polynomial<F, LagrangeCoeff>>;

/// One lookup argument's compressed inputs paired with its multiplicities
/// polynomial, as `compute_multiplicities_parallel` returns them.
type ComputedMultiplicitiesPair<F> = (
    logup::prover::ComputedMultiplicities<F>,
    Polynomial<F, LagrangeCoeff>,
);

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

    let advice = {
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

    // Compute the multiplicities columns and commit to them as the phase1
    // argument group: one commitment over every multiplicities polynomial,
    // rather than one per lookup argument. Compute and transcript write are
    // separate API calls — measure them together to match the prior
    // `commit_multiplicities` shape.
    let compute_multiplicities = |advice_polys: &[Polynomial<F, LagrangeCoeff>],
                                  instance_values: &[Polynomial<F, LagrangeCoeff>],
                                  blindings: &[Vec<F>]|
     -> Result<Vec<ComputedMultiplicitiesPair<F>>, Error> {
        let logup_args: Vec<_> =
            pk.vk.cs.lookups.iter().map(|l| l.chunk_by_degree(pk.vk.cs.degree())).collect();
        logup_args
            .par_iter()
            .enumerate()
            .zip(blindings.par_iter())
            .map(|((argument_index, logup), blinds)| {
                logup.compute_multiplicities_parallel(
                    argument_index,
                    pk,
                    theta,
                    advice_polys,
                    &pk.fixed_values,
                    instance_values,
                    blinds,
                )
            })
            .collect::<Result<Vec<_>, Error>>()
    };

    // Hand the multiplicities polynomials over to the phase1 group, keeping the
    // rest of each `ComputedMultiplicities` for the phase2 computation.
    let split_multiplicities = |computed: Vec<ComputedMultiplicitiesPair<F>>| {
        let mut polys_map = BTreeMap::new();
        let mut rest = Vec::with_capacity(computed.len());
        for (c, multiplicities) in computed {
            polys_map.insert(
                PolynomialLabel::LogupMultiplicities(c.argument_index),
                multiplicities,
            );
            rest.push(c);
        }
        (rest, polys_map)
    };

    let (logup_multiplicities, phase1_committed) = {
        group.bench_function("Commit lookup multiplicities", |b| {
            b.iter_batched(
                || (transcript.clone(), mult_blindings.clone()),
                |(mut t, mult_blinds)| -> Result<(), Error> {
                    let computed = compute_multiplicities(
                        &advice.advice_polys,
                        &instance.instance_values,
                        &mult_blinds,
                    )?;
                    let (_, polys_map) = split_multiplicities(computed);
                    argument::prover::Committed::commit::<CS, _>(params, polys_map, &mut t)?;
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });
        let (multiplicities, polys_map) = split_multiplicities(compute_multiplicities(
            &advice.advice_polys,
            &instance.instance_values,
            &mult_blindings,
        )?);
        let committed =
            argument::prover::Committed::commit::<CS, T>(params, polys_map, transcript)?;
        (multiplicities, committed)
    };

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

    // Commit to permutations. `Argument::compute` returns z polys + commitments
    // without touching the transcript; `write_and_convert` then writes
    // commitments and converts to coefficient form. Measure both together.
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
    let logup_blindings: Vec<Vec<F>> = (0..logup_multiplicities.len())
        .map(|_| (0..blinding_factors).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Construct the lookup product polynomials. `compute_logderivative` returns
    // the helper polynomials and the aggregator without touching the transcript;
    // they are committed further below, as part of the phase2 argument group.
    let logup_phase2_polys = |multiplicities: Vec<logup::prover::ComputedMultiplicities<F>>,
                              blindings: Vec<Vec<F>>|
     -> Result<Vec<PhaseGroupPolys<F>>, Error> {
        Ok(multiplicities
            .into_par_iter()
            .zip(blindings.into_par_iter())
            .map(|(lookup, blinds)| {
                let multiplicities = phase1_committed
                    .polys_map
                    .get(&PolynomialLabel::LogupMultiplicities(lookup.argument_index))
                    .expect("the phase1 group holds every multiplicities polynomial");
                lookup.compute_logderivative(pk, multiplicities, beta, blinds)
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_par_iter()
            .map(|c| {
                BTreeMap::from_iter(
                    [
                        c.helper_polys_lagrange
                            .into_iter()
                            .enumerate()
                            .map(|(j, p)| {
                                (
                                    PolynomialLabel::LogupHelper(c.argument_index, j),
                                    domain.lagrange_from_vec(p),
                                )
                            })
                            .collect::<Vec<_>>(),
                        vec![(
                            PolynomialLabel::LogupAggregator(c.argument_index),
                            c.aggregator_poly,
                        )],
                    ]
                    .concat(),
                )
            })
            .collect::<Vec<_>>())
    };

    let logup_polys_maps = {
        group.bench_function("Compute lookup products", |b| {
            b.iter_batched(
                || (logup_multiplicities.clone(), logup_blindings.clone()),
                |(multiplicities, blinds)| logup_phase2_polys(multiplicities, blinds),
                criterion::BatchSize::LargeInput,
            )
        });
        logup_phase2_polys(logup_multiplicities, logup_blindings)?
    };

    // Phase2 argument group: the logup helper and aggregator polynomials
    // together with the trash polynomials, under a single commitment.
    //
    // CAVEAT: this stage used to commit the trash polynomials alone. It now
    // covers the logup polynomials too, so its cost is not comparable with the
    // same line from earlier revisions.
    let build_phase2_polys_map = |logup_polys_maps: Vec<PhaseGroupPolys<F>>,
                                  advice_polys: &[Polynomial<F, LagrangeCoeff>],
                                  instance_values: &[Polynomial<F, LagrangeCoeff>]|
     -> Result<PhaseGroupPolys<F>, Error> {
        let mut phase2_polys_map = BTreeMap::new();

        for polys_map in logup_polys_maps {
            for (label, p) in polys_map {
                if phase2_polys_map.insert(label, p).is_some() {
                    return Err(Error::DuplicatedLabel);
                }
            }
        }

        for (i, trash) in pk.vk.cs.trashcans.iter().enumerate() {
            let p = trash.compute_trash_poly(
                domain,
                trash_challenge,
                advice_polys,
                &pk.fixed_values,
                instance_values,
            );

            if phase2_polys_map.insert(PolynomialLabel::Trash(i), p).is_some() {
                return Err(Error::DuplicatedLabel);
            }
        }

        Ok(phase2_polys_map)
    };

    let phase2_committed = {
        group.bench_function("Commit phase2 arguments", |b| {
            b.iter_batched(
                || (transcript.clone(), logup_polys_maps.clone()),
                |(mut t, logup_maps)| -> Result<(), Error> {
                    let polys_map = build_phase2_polys_map(
                        logup_maps,
                        &advice.advice_polys,
                        &instance.instance_values,
                    )?;
                    argument::prover::Committed::commit::<CS, _>(params, polys_map, &mut t)?;
                    Ok(())
                },
                criterion::BatchSize::LargeInput,
            )
        });

        let polys_map = build_phase2_polys_map(
            logup_polys_maps,
            &advice.advice_polys,
            &instance.instance_values,
        )?;
        argument::prover::Committed::commit::<CS, T>(params, polys_map, transcript)?
    };

    // Obtain challenge for keeping all separate gates linearly independent
    let y: F = transcript.squeeze_challenge();

    let instance_polys = instance.instance_polys;
    let instance_values = instance.instance_values;

    let advice_polys: Vec<_> =
        advice.advice_polys.into_iter().map(|p| domain.lagrange_to_coeff(p)).collect();

    let phase1_committed = phase1_committed.into_coeff(domain);
    let phase2_committed = phase2_committed.into_coeff(domain);

    Ok(ProverTrace {
        advice_polys,
        instance_polys,
        instance_values,
        phase1_committed,
        phase2_committed,
        permutations,
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
        phase1_committed,
        phase2_committed,
        permutations,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
        ..
    } = trace;

    // PCS-aware squeeze (see plonk/prover.rs).
    let x: F = CS::squeeze_evaluation_point(transcript);

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

    // Evaluate the phase1 and phase2 arguments, if any, at their opening points.
    let domain = pk.vk.get_domain();
    let phase1_evaluated = phase1_committed.evaluate(domain, x, transcript)?;
    let phase2_evaluated = phase2_committed.evaluate(domain, x, transcript)?;

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
                    &phase1_evaluated.evals_map,
                    &phase2_evaluated.evals_map,
                    &permutations_common,
                    x,
                    xn,
                    beta,
                    gamma,
                    theta,
                    trash_challenge,
                );
            })
        });
        partially_evaluate_identities(
            &pk.vk,
            &fixed_evals,
            &instance_evals,
            &advice_evals,
            &permutations.evaluated,
            &phase1_evaluated.evals_map,
            &phase2_evaluated.evals_map,
            &permutations_common,
            x,
            xn,
            beta,
            gamma,
            theta,
            trash_challenge,
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
                    &phase1_evaluated,
                    &phase2_evaluated,
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
            &phase1_evaluated,
            &phase2_evaluated,
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

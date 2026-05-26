use std::{
    collections::HashSet,
    hash::Hash,
    iter::{self},
    ops::RangeTo,
};

use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
#[cfg(not(feature = "single-h-commitment"))]
use rand_core::OsRng;
use rand_core::{CryptoRng, RngCore};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use super::{
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
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
        batch_invert_rational, commitment::PolynomialCommitmentScheme, Coeff, CommitmentLabel,
        EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial,
        PolynomialRepresentation, ProverQuery, Rotation,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{
        arithmetic::{eval_polynomial, eval_polynomial_seq},
        rational::Rational,
    },
};

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
    CS::commit(params, &poly, CommitmentLabel::Instance(0))
}

/// This computes a proof trace for the provided `circuit` when given the
/// public parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// The trace can then be used to finalise the proof.
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
    pk.vk.hash_into(transcript)?;

    let domain = &pk.vk.domain;

    let instance = compute_instances(params, pk, instances, nb_committed_instances, transcript)?;

    let advice = parse_advices(params, pk, circuit, instances, transcript, &mut rng)?;

    // Helper: sample `num_sets` blinding vectors, each of length `inner_len`.
    // Used to pre-generate every blinding the parallel compute sections below
    // consume, since `&mut rng` cannot cross rayon thread boundaries.
    let mut sample_blindings = |num_sets: usize, inner_len: usize| -> Vec<Vec<F>> {
        (0..num_sets)
            .map(|_| (0..inner_len).map(|_| F::random(&mut rng)).collect())
            .collect()
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    let num_lookups = pk.vk.cs.lookups.len();
    let mult_blinding_count = pk.vk.cs.blinding_factors() + 1;
    let mult_blindings: Vec<Vec<F>> = sample_blindings(num_lookups, mult_blinding_count);

    // Commit to the multiplicities columns.
    // Computation in parallel, then sequential transcript writes.
    let lookups: Vec<logup::prover::ComputedMultiplicities<F>> = {
        let logup_args: Vec<_> =
            pk.vk.cs.lookups.iter().map(|l| l.chunk_by_degree(pk.vk.cs.degree())).collect();
        // Compute all lookups in parallel (no transcript access, no rng).
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
                    blinds,
                )
            })
            .collect::<Result<Vec<_>, Error>>()?;
        // Sequential transcript writes to preserve Fiat-Shamir ordering.
        results
            .into_iter()
            .map(|(computed, commitment)| {
                transcript.write(&commitment)?;
                Ok(computed)
            })
            .collect::<Result<Vec<_>, Error>>()?
    };

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    let blinding_factors = pk.vk.cs.blinding_factors();
    let chunk_len = pk.vk.cs_degree - 2;
    let num_perm_sets = pk.vk.cs.permutation.columns.chunks(chunk_len).len();
    let perm_blindings: Vec<Vec<F>> = sample_blindings(num_perm_sets, blinding_factors);
    let logup_blindings: Vec<Vec<F>> = sample_blindings(lookups.len(), blinding_factors);

    // Overlap permutation and logup computation.
    // Both only need β (and γ for permutation). Neither touches the transcript.
    // Transcript writes preserve the original ordering:
    // permutation commitments first, then logup commitments.
    let (perm_computed, logup_computed) = rayon::join(
        || {
            pk.vk.cs.permutation.compute::<F, CS>(
                params,
                pk,
                &pk.permutation,
                &advice.advice_polys,
                &pk.fixed_values,
                &instance.instance_values,
                beta,
                gamma,
                perm_blindings,
            )
        },
        || -> Result<_, Error> {
            let computed: Vec<_> = lookups
                .into_par_iter()
                .zip(logup_blindings.into_par_iter())
                .map(|(lookup, blindings)| {
                    lookup.compute_logderivative(pk, params, beta, blindings)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let all_helper_commitments: Vec<Vec<CS::Commitment>> = computed
                .par_iter()
                .map(|c| {
                    c.helper_polys_lagrange
                        .par_iter()
                        .map(|h| {
                            let h_poly = domain.lagrange_from_vec(h.clone());
                            CS::commit(params, &h_poly, CommitmentLabel::NoLabel)
                        })
                        .collect()
                })
                .collect();
            Ok((computed, all_helper_commitments))
        },
    );

    // Write permutation commitments first.
    let permutations = perm_computed.write_and_convert(domain, transcript)?;

    // Then write logup commitments and convert to coefficient form.
    let (computed, all_helper_commitments) = logup_computed?;
    for (c, helper_commitments) in computed.iter().zip(all_helper_commitments.iter()) {
        for h_commitment in helper_commitments {
            transcript.write(h_commitment)?;
        }
        transcript.write(&c.aggregator_commitment)?;
    }
    let lookups: Vec<logup::prover::Committed<F>> = computed
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
        .collect();

    // Trash argument
    let trash_challenge: F = transcript.squeeze_challenge();

    let trashcans: Vec<trash::prover::Committed<F>> = pk
        .vk
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
                transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Obtain challenge for keeping all separate gates linearly independent
    let y: F = transcript.squeeze_challenge();

    let InstanceSingle {
        instance_polys,
        instance_values,
    } = instance;

    let advice_polys: Vec<_> = advice
        .advice_polys
        .into_par_iter()
        .map(|p| domain.lagrange_to_coeff(p))
        .collect();

    Ok(ProverTrace {
        advice_polys,
        instance_polys,
        instance_values,
        lookups,
        trashcans,
        permutations,
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
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
        ..
    } = trace;

    let x: F = transcript.squeeze_challenge();

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
    let expressions = partially_evaluate_identities(
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
    );

    // Compute linearization polynomial
    let (lin_poly_non_constant_part, lin_poly_constant_term) =
        compute_linearization_poly(expressions, pk, y, xn, splitting_factor, quotient_limbs);

    debug_assert_eq!(
        eval_polynomial(&lin_poly_non_constant_part, x),
        -lin_poly_constant_term,
        "L'(x) should equal -C, where C is the constant part of the linearization polynomial"
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
        &lin_poly_non_constant_part,
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
    circuit: &ConcreteCircuit,
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[F]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
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
        circuit,
        #[cfg(feature = "committed-instances")]
        nb_committed_instances,
        instances,
        transcript,
        &mut rng,
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
    instances: &[&[F]],
    nb_committed_instances: usize,
    transcript: &mut T,
) -> Result<InstanceSingle<F>, Error>
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
    let instance_values = instances
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
                transcript.common(&CS::commit(params, &poly, CommitmentLabel::NoLabel))?;
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
}

pub(super) fn parse_advices<F, CS, ConcreteCircuit, T>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuit: &ConcreteCircuit,
    instances: &[&[F]],
    transcript: &mut T,
    rng: &mut (impl RngCore + CryptoRng),
) -> Result<AdviceSingle<F, LagrangeCoeff>, Error>
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
    let config = ConcreteCircuit::configure_with_params(&mut meta, circuit.params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut meta);

    let domain = &pk.vk.domain;
    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;

    let mut advice = AdviceSingle::<F, LagrangeCoeff> {
        advice_polys: vec![domain.empty_lagrange(); meta.num_advice_columns],
    };

    let unusable_rows_start = domain.n as usize - (meta.blinding_factors() + 1);

    let mut witness = WitnessCollection {
        k: domain.k(),
        advice: vec![domain.empty_lagrange_rational(); meta.num_advice_columns],
        unblinded_advice: HashSet::from_iter(meta.unblinded_advice_columns.clone()),
        instances,
        // The prover will not be allowed to assign values to advice
        // cells that exist within inactive rows, which include some
        // number of blinding factors and an extra row for use in the
        // permutation argument.
        usable_rows: ..unusable_rows_start,
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain the witness. If keygen captured
    // the region layout (see `ProvingKey::region_starts`), we reuse it
    // here to skip the shape pass; otherwise the floor planner falls
    // back to computing it.
    ConcreteCircuit::FloorPlanner::synthesize_with_cached_regions(
        &mut witness,
        circuit,
        config.clone(),
        meta.constants.clone(),
        pk.region_starts.as_deref(),
    )?;

    let mut advice_values = batch_invert_rational::<F>(witness.advice);

    for (i, advice_values) in advice_values.iter_mut().enumerate() {
        if !witness.unblinded_advice.contains(&i) {
            for cell in &mut advice_values[unusable_rows_start..] {
                *cell = F::random(&mut *rng);
            }
        } else {
            #[cfg(debug_assertions)]
            for cell in &advice_values[unusable_rows_start..] {
                assert_eq!(*cell, F::ZERO);
            }
        }
    }

    let advice_commitments: Vec<_> = advice_values
        .par_iter()
        .enumerate()
        .map(|(i, poly)| CS::commit(params, poly, CommitmentLabel::Advice(i)))
        .collect();

    for commitment in &advice_commitments {
        transcript.write(commitment)?;
    }

    advice.advice_polys = advice_values;

    Ok(advice)
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
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
        ..
    } = &trace;
    // Calculate the advice and instance cosets
    let advice_cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>> = advice_polys
        .par_iter()
        .map(|poly| pk.vk.get_domain().coeff_to_extended(poly.clone()))
        .collect();
    let instance_cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>> = instance_polys
        .par_iter()
        .map(|poly| pk.vk.get_domain().coeff_to_extended(poly.clone()))
        .collect();

    // Evaluate the numerator polynomial nu(X) of the quotient polynomial
    // h(X) = nu(X) / (X^n-1): nu(X) is a random linear combination of all
    // independent identities
    pk.ev.evaluate_numerator::<ExtendedLagrangeCoeff>(
        &pk.vk.domain,
        &pk.vk.cs,
        &advice_cosets,
        &instance_cosets,
        &pk.fixed_cosets,
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

/// Computes the quotient polynomial `h(X) = nu(X) / (X^n - 1)` and commits to
/// it, writing the commitment(s) to the transcript.
///
/// **Default behaviour** (`single-h-commitment` feature *disabled*): `h(X)` is
/// split into `quotient_poly_degree` limbs of degree `n-2` each, so that each
/// can be committed with an SRS of size `n` after 1 term for blinding. Each
/// limb is independently blinded and committed, and all `quotient_poly_degree`
/// commitments are written to the transcript. The returned `Vec` contains the
/// `quotient_poly_degree` limb polynomials in coefficient form.
///
/// **Alternative behaviour** (`single-h-commitment` feature *enabled*): `h(X)`
/// is committed as a single polynomial without splitting. A single commitment
/// is written to the transcript. The returned `Vec` contains exactly one
/// element: the full `h(X)` in coefficient form. In this mode the `params`
/// **must** supply an SRS of at least `(n-1) * quotient_poly_degree` elements
/// (i.e., params generated with `k' >= log2(n * (d-1))`).
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

    // When the single-h-commitment feature is enabled, commit to h(X) in one go.
    // The params SRS must have at least h_poly.len() monomial elements.
    #[cfg(feature = "single-h-commitment")]
    {
        use crate::poly::commitment::Params;
        if params.g_monomial_size() < h_poly.len() {
            return Err(Error::SrsError(params.g_monomial_size(), h_poly.len()));
        }
        let h_poly = Polynomial {
            values: h_poly,
            _marker: std::marker::PhantomData,
        };
        let h_com = CS::commit(params, &h_poly, CommitmentLabel::NoLabel);
        transcript.write(&h_com)?;
        Ok(vec![h_poly])
    }

    // Split h(X) up into limbs and add inter-limb blinding so that
    // individual limb commitments do not leak information about h(X).
    #[cfg(not(feature = "single-h-commitment"))]
    {
        let h_poly_iter = h_poly.chunks_exact((domain.n - 1) as usize);
        assert_eq!(h_poly_iter.remainder().len(), 0);
        let mut h_limbs = h_poly_iter.map(|v| v.to_vec()).collect::<Vec<_>>();
        drop(h_poly);

        blind_quotient_limbs(&mut h_limbs);

        let h_limbs: Vec<_> =
            h_limbs.into_iter().map(|h_limb| domain.coeff_from_vec(h_limb)).collect();

        // Compute commitment to each limb (parallel MSMs).
        let h_commitments: Vec<_> = h_limbs
            .par_iter()
            .map(|h_piece| CS::commit(params, h_piece, CommitmentLabel::NoLabel))
            .collect();

        // Write each limb commitment to the transcript in order.
        for c in h_commitments {
            transcript.write(&c)?;
        }

        Ok(h_limbs)
    }
}

#[cfg(not(feature = "single-h-commitment"))]
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

// Structure for holding evaluations of fixed, instance, and advice columns.
#[derive(Debug, Clone)]
pub(super) struct Evals<F>
where
    F: WithSmallOrderMulGroup<3>,
{
    pub(crate) fixed_evals: Vec<F>,
    pub(crate) instance_evals: Vec<F>,
    pub(crate) advice_evals: Vec<F>,
}

pub(super) fn write_evals_to_transcript<F, CS, T>(
    pk: &ProvingKey<F, CS>,
    nb_committed_instances: usize,
    instance_polys: &[Polynomial<F, Coeff>],
    advice_polys: &[Polynomial<F, Coeff>],
    x: F,
    transcript: &mut T,
) -> Result<Evals<F>, Error>
where
    F: WithSmallOrderMulGroup<3> + Hashable<T::Hash>,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
{
    let domain = &pk.vk.domain;
    let meta = &pk.vk.cs;

    // Batch-evaluate all polynomials with outer parallelism and sequential
    // Horner per task, avoiding the per-call rayon::scope overhead of the
    // internally-parallel eval_polynomial.
    let instance_evals: Vec<F> = meta
        .instance_queries
        .par_iter()
        .map(|&(column, at)| {
            eval_polynomial_seq(&instance_polys[column.index()], domain.rotate_omega(x, at))
        })
        .collect();

    let advice_evals: Vec<F> = meta
        .advice_queries
        .par_iter()
        .map(|&(column, at)| {
            eval_polynomial_seq(&advice_polys[column.index()], domain.rotate_omega(x, at))
        })
        .collect();

    let fixed_evals: Vec<F> = meta
        .fixed_queries
        .par_iter()
        .map(|&(column, at)| {
            let col_idx = column.index();
            if meta.has_simple_selector_col(col_idx) {
                F::ONE
            } else {
                eval_polynomial_seq(&pk.fixed_polys[col_idx], domain.rotate_omega(x, at))
            }
        })
        .collect();

    // Write evaluations to transcript in the canonical order.
    for (eval, &(column, _)) in instance_evals.iter().zip(meta.instance_queries.iter()) {
        if column.index() < nb_committed_instances {
            transcript.write(eval)?;
        }
    }

    for eval in &advice_evals {
        transcript.write(eval)?;
    }

    for (eval, &(column, _)) in fixed_evals.iter().zip(meta.fixed_queries.iter()) {
        if !meta.has_simple_selector_col(column.index()) {
            transcript.write(eval)?;
        }
    }

    Ok(Evals {
        fixed_evals,
        instance_evals,
        advice_evals,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compute_queries<
    'a,
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
>(
    pk: &'a ProvingKey<F, CS>,
    nb_committed_instances: usize,
    instance_polys: &'a [Polynomial<F, Coeff>],
    advice_polys: &'a [Polynomial<F, Coeff>],
    permutations: &'a permutation::prover::Evaluated<F>,
    lookups: &'a [logup::prover::Evaluated<F>],
    trashcans: &'a [trash::prover::Evaluated<F>],
    x: F,
    lin_poly_non_constant_part: &'a Polynomial<F, Coeff>,
) -> Vec<ProverQuery<'a, F>> {
    let domain = pk.vk.get_domain();
    iter::empty()
        .chain(
            pk.vk.cs.advice_queries.iter().map(move |&(column, at)| ProverQuery {
                point: domain.rotate_omega(x, at),
                poly: &advice_polys[column.index()],
            }),
        )
        .chain(
            pk.vk.cs.instance_queries.iter().filter_map(move |&(column, at)| {
                if column.index() < nb_committed_instances {
                    Some(ProverQuery {
                        point: domain.rotate_omega(x, at),
                        poly: &instance_polys[column.index()],
                    })
                } else {
                    None
                }
            }),
        )
        .chain(permutations.open(pk, x))
        .chain(lookups.iter().flat_map(move |p| p.open(pk, x)))
        .chain(trashcans.iter().flat_map(move |p| p.open(x)))
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                // Filter out queries for simple, multiplicative selectors
                .filter(|(col, _)| !pk.vk.cs.has_simple_selector_col(col.index()))
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(x, at),
                    poly: &pk.fixed_polys[column.index()],
                }),
        )
        .chain(pk.permutation.open(x))
        .chain(iter::once(ProverQuery {
            point: domain.rotate_omega(x, Rotation::cur()),
            poly: lin_poly_non_constant_part,
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
    advice: Vec<Polynomial<Rational<F>, LagrangeCoeff>>,
    unblinded_advice: HashSet<usize>,
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
    let vk = keygen_vk_with_k::<Fr, KZGCommitmentScheme<Bn256>, _>(&params, &MyCircuit, K)
        .expect("keygen_vk should not fail");
    let pk = keygen_pk(vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = CircuitTranscript::<_>::init();

    // Create proof with wrong number of instances (extra column).
    let proof = create_proof(
        &params,
        &pk,
        &MyCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        &[&[]],
        &mut transcript,
        OsRng,
    );
    assert!(matches!(proof.unwrap_err(), Error::InvalidInstances));

    // Create proof with correct number of instances.
    create_proof(
        &params,
        &pk,
        &MyCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        &[],
        &mut transcript,
        OsRng,
    )
    .expect("proof generation should not fail");
}

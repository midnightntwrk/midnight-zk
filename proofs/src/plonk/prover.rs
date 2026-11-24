use std::{
    collections::{BTreeMap, HashSet},
    iter::{self},
    ops::RangeTo,
    slice,
};

use ff::{Field, FromUniformBytes, PrimeField};
use rand_core::{CryptoRng, OsRng, RngCore};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

#[cfg(not(feature = "prover-par"))]
use super::circuit::FloorPlanner;
use super::{
    Error, ProvingKey,
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, Instance, Selector,
    },
    logup,
};
#[cfg(not(feature = "prover-par"))]
use crate::utils::arithmetic::eval_polynomial;
use crate::{
    circuit::Value,
    plonk::{ProofField, argument, traces::ProverTrace},
    poly::{
        Coeff, EvaluationDomain, ExtendedLagrangeCoeff, FftDomain, LagrangeCoeff, Polynomial,
        PolynomialLabel, ProverQuery, Rotation, batch_invert_rational,
        commitment::PolynomialCommitmentScheme,
    },
    profiling::{self, Kernel, Phase},
    transcript::{Hashable, Transcript},
    utils::{arithmetic::eval_polynomial_seq, rational::Rational},
};

#[cfg(feature = "committed-instances")]
/// Commit to a vector of raw instances. This function can be used to prepare
/// the committed instances that the verifier will be provided with when this
/// feature is enabled.
///
/// `column` is the index of the instance column these values fill. The
/// commitment is labelled with it, so the verifier accepts it only there.
///
/// # Panics
///
/// If `instances` is longer than the domain.
pub fn commit_to_instances<F, PCS>(
    params: &PCS::Parameters,
    domain: &EvaluationDomain<F>,
    instances: &[F],
    column: usize,
) -> PCS::Commitment
where
    F: Ord + FromUniformBytes<64>,
    PCS: PolynomialCommitmentScheme<F>,
{
    let mut poly = domain.empty_lagrange();
    assert!(instances.len() <= poly.len());
    for (poly_eval, value) in poly.iter_mut().zip(instances.iter()) {
        *poly_eval = *value;
    }
    PCS::commit(params, &poly, PolynomialLabel::CommittedInstance(column))
}

/// This computes a proof trace for the provided `circuit` when given the
/// public parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// The trace can then be used to finalise the proof.
pub(crate) fn compute_trace<'a, F, PCS, T, ConcreteCircuit>(
    params: &PCS::Parameters,
    pk: &'a ProvingKey<F, PCS>,
    circuit: &ConcreteCircuit,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[F]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
) -> Result<ProverTrace<'a, F>, Error>
where
    F: ProofField<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
{
    #[cfg(not(feature = "committed-instances"))]
    let nb_committed_instances: usize = 0;

    if instances.len() != pk.vk.cs.num_instance_columns || instances.len() < nb_committed_instances
    {
        return Err(Error::InvalidInstances);
    }

    // Hash verification key into transcript
    let vk_absorbed = pk.vk.absorb_into(transcript)?;
    let phase0_committed = pk.phase0_polys.committed(&vk_absorbed);

    let domain = &pk.vk.domain;

    let instance = compute_instances(params, pk, instances, nb_committed_instances, transcript)?;

    profiling::set_phase(Phase::Synthesis);
    let advice_polys = parse_advices(pk, circuit, instances, &mut rng)?;

    // Helper: sample `num_sets` blinding vectors, each of length `inner_len`.
    // Used to pre-generate every blinding the parallel compute sections below
    // consume, since `&mut rng` cannot cross rayon thread boundaries.
    let mut sample_blindings = |num_sets: usize, inner_len: usize| -> Vec<Vec<F>> {
        (0..num_sets)
            .map(|_| (0..inner_len).map(|_| F::random(&mut rng)).collect())
            .collect()
    };

    profiling::set_phase(Phase::Lookups);
    let num_lookups = pk.vk.cs.lookups.len();
    let mult_blinding_count = pk.vk.cs.blinding_factors() + 1;
    let mult_blindings: Vec<Vec<F>> = sample_blindings(num_lookups, mult_blinding_count);

    // Compute the multiplicities columns in parallel. They are committed to
    // below, as the phase1 argument group.
    let logup_multiplicities: Vec<logup::prover::ComputedMultiplicities<F>> = {
        let logup_args: Vec<_> =
            pk.vk.cs.lookups.iter().map(|l| l.chunk_by_degree(pk.vk.cs.degree())).collect();
        logup_args
            .par_iter()
            .enumerate()
            .zip(mult_blindings.par_iter())
            .map(|((argument_index, logup), blinds)| {
                logup.compute_multiplicities_parallel(
                    argument_index,
                    pk,
                    &advice_polys,
                    &pk.fixed_values,
                    &instance.instance_values,
                    blinds,
                )
            })
            .collect::<Result<Vec<_>, Error>>()?
    };

    profiling::set_phase(Phase::AdviceCommit);
    let logup_multiplicities_len = logup_multiplicities.len();
    // The advice columns and the multiplicities form the phase1 group.
    // TODO: Check the multiplicities clone - see if we can remove it.
    let advice_labels = pk.vk.cs.advice_labels();
    let mut phase1_polys_map: BTreeMap<PolynomialLabel, Polynomial<F, LagrangeCoeff>> =
        BTreeMap::new();

    for (label, poly) in advice_labels.iter().cloned().zip(advice_polys) {
        if phase1_polys_map.insert(label, poly).is_some() {
            return Err(Error::DuplicatedLabel);
        }
    }

    for c in logup_multiplicities.iter() {
        let label = PolynomialLabel::LogupMultiplicities(c.argument_index);
        if phase1_polys_map.insert(label, c.multiplicities.clone()).is_some() {
            return Err(Error::DuplicatedLabel);
        }
    }

    let phase1_committed = argument::prover::Committed::commit::<PCS, T, _>(
        params,
        phase1_polys_map,
        Polynomial::to_delta,
        transcript,
    )?;

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    // Sample the trash challenge after the advices have been committed to
    let trash_challenge: F = transcript.squeeze_challenge();

    profiling::set_phase(Phase::Permutation);
    let blinding_factors = pk.vk.cs.blinding_factors();
    let num_perm_sets = pk.vk.cs.permutation.num_sets(pk.vk.cs_degree);
    let perm_blindings: Vec<Vec<F>> = sample_blindings(num_perm_sets, blinding_factors);
    let logup_blindings: Vec<Vec<F>> = sample_blindings(logup_multiplicities_len, blinding_factors);

    let mut phase2_polys_map: BTreeMap<PolynomialLabel, Polynomial<F, LagrangeCoeff>> =
        BTreeMap::new();

    let perm_z_polys = pk.vk.cs.permutation.compute_z_polys::<F, PCS>(
        pk,
        phase1_committed.polys_of(&advice_labels),
        &pk.fixed_values,
        &instance.instance_values,
        beta,
        gamma,
        perm_blindings,
    );

    for (i, poly) in perm_z_polys.into_iter().enumerate() {
        if phase2_polys_map
            .insert(PolynomialLabel::PermutationAccumulator(i), poly)
            .is_some()
        {
            return Err(Error::DuplicatedLabel);
        }
    }

    profiling::set_phase(Phase::Lookups);
    let logup_polys_maps = logup_multiplicities
        .into_par_iter()
        .zip(logup_blindings.into_par_iter())
        .map(|(lookup, blindings)| lookup.compute_logderivative(pk, theta, beta, blindings))
        .collect::<Result<Vec<_>, Error>>()?
        .into_par_iter()
        .map(|c| {
            BTreeMap::from_iter(
                [
                    c.helper_polys_lagrange
                        .into_par_iter()
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
        .collect::<Vec<_>>();

    for polys_map in logup_polys_maps {
        for (label, p) in polys_map {
            if phase2_polys_map.insert(label, p).is_some() {
                return Err(Error::DuplicatedLabel);
            }
        }
    }

    if !pk.vk.cs.trashcans.is_empty() {
        profiling::set_phase(Phase::Trash);
    }
    for (i, trash) in pk.vk.cs.trashcans.iter().enumerate() {
        let p = trash.compute_trash_poly(
            domain,
            trash_challenge,
            phase1_committed.polys_of(&advice_labels),
            &pk.fixed_values,
            &instance.instance_values,
        );

        if phase2_polys_map.insert(PolynomialLabel::Trash(i), p).is_some() {
            return Err(Error::DuplicatedLabel);
        }
    }

    profiling::set_phase(Phase::ArgumentsCommit);
    let phase2_committed = argument::prover::Committed::commit::<PCS, T, _>(
        params,
        phase2_polys_map,
        Polynomial::to_double_delta,
        transcript,
    )?;

    // Obtain challenge for keeping all separate gates linearly independent
    let y: F = transcript.squeeze_challenge();

    let InstanceSingle {
        instance_polys,
        instance_values,
    } = instance;

    let fft_domain = &pk.fft_domain;

    // The quotient is computed from the coefficient form of the polynomials.
    profiling::set_phase(Phase::Quotient);
    let phase1_committed = phase1_committed.into_coeff(fft_domain);
    let phase2_committed = phase2_committed.into_coeff(fft_domain);

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

/// The quotient group of [`finalise_proof`] with the feature `gpu`: the
/// blinded limbs of `h(X)` are witness-dependent, so the group is held
/// in this guard from the point where it exists until the end of the
/// proof. The guard dereferences to the group for the evaluations and
/// the multi-open, and on drop — on the success path and on every
/// error path out of `finalise_proof` alike — it zeroes every limb over
/// the whole capacity of its allocation before the stock drop frees
/// it.
#[cfg(feature = "gpu")]
#[derive(Debug)]
struct ErasingQuotient<F: PrimeField>(argument::prover::Committed<F, Coeff>);

#[cfg(feature = "gpu")]
impl<F: PrimeField> std::ops::Deref for ErasingQuotient<F> {
    type Target = argument::prover::Committed<F, Coeff>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(feature = "gpu")]
impl<F: PrimeField> Drop for ErasingQuotient<F> {
    fn drop(&mut self) {
        self.0.erase_polys();
    }
}

/// This takes the computed trace of a set of witnesses and creates a proof
/// for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub(crate) fn finalise_proof<'a, F, PCS, T>(
    params: &'a PCS::Parameters,
    pk: &'a ProvingKey<F, PCS>,
    // The prover needs to get all instances in non-committed form. However,
    // the first `nb_committed_instances` instance columns are dedicated for
    // instances that the verifier receives in committed form.
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    trace: ProverTrace<'a, F>,
    transcript: &mut T,
) -> Result<(), Error>
where
    F: ProofField<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    #[cfg(not(feature = "committed-instances"))]
    let nb_committed_instances: usize = 0;

    profiling::set_phase(Phase::Quotient);
    #[cfg(not(feature = "gpu"))]
    let nu_poly = compute_nu_poly(pk, &trace);

    // Construct the quotient polynomial h(X) = nu(X)/(X^n-1), split it into limbs,
    // and commit to the limbs as one group
    #[cfg(not(feature = "gpu"))]
    let quotient_committed =
        compute_h_poly::<F, PCS, T>(params, &pk.fft_domain, nu_poly, transcript)?;

    // With the feature `gpu`, the installed quotient hook may compute the
    // coefficients of h(X); when it declines, the stock code runs.
    #[cfg(feature = "gpu")]
    let quotient_committed = {
        let domain = pk.get_vk().get_domain();
        let fft_domain = &pk.fft_domain;
        let stock = || {
            let nu_poly = compute_nu_poly(pk, &trace);
            fft_domain.extended_to_coeff(domain.divide_by_vanishing_poly(nu_poly))
        };
        match crate::gpu::quotient_coeffs(pk, &trace, stock) {
            Some(h_poly) => {
                commit_h_coeffs_erasing::<F, PCS, T>(params, domain, h_poly, transcript)?
            }
            None => {
                let nu_poly = compute_nu_poly(pk, &trace);
                compute_h_poly::<F, PCS, T>(params, fft_domain, nu_poly, transcript)?
            }
        }
    };

    // With the feature `gpu`, the quotient limbs are zeroed when the
    // group is released at the end of this function, on every path out
    // of it from here on.
    #[cfg(feature = "gpu")]
    let quotient_committed = ErasingQuotient(quotient_committed);

    let ProverTrace {
        instance_polys,
        phase0_committed,
        phase1_committed,
        phase2_committed,
        ..
    } = trace;

    profiling::set_phase(Phase::Evals);
    let x: F = PCS::squeeze_evaluation_point(transcript);
    let domain = pk.vk.get_domain();
    let cs = pk.vk.cs();

    let x_rotations: BTreeMap<Rotation, F> = argument::rotations(cs)
        .into_iter()
        .map(|rotation| (rotation, domain.rotate_omega(x, rotation)))
        .collect();

    write_instance_evals_to_transcript(
        pk,
        nb_committed_instances,
        &instance_polys,
        &x_rotations,
        transcript,
    )?;

    let phase0_evaluated = phase0_committed.evaluate(cs, &x_rotations, transcript)?;

    let phase1_evaluated = phase1_committed.evaluate(cs, &x_rotations, transcript)?;

    let phase2_evaluated = phase2_committed.evaluate(cs, &x_rotations, transcript)?;

    let mut quotient_evaluated = quotient_committed.evaluate(cs, &x_rotations, transcript)?;

    // h_0(x) is not written to the proof, the verifier derives it.
    let h0 = PolynomialLabel::QuotientPiece(0);
    #[cfg(not(feature = "prover-par"))]
    let h0_eval = eval_polynomial(
        quotient_committed.poly(&h0).expect("a quotient limb h_0"),
        x,
    );
    #[cfg(feature = "prover-par")]
    let h0_eval = crate::par::open::eval_many(&[(
        &quotient_committed.poly(&h0).expect("a quotient limb h_0").values[..],
        x,
    )])[0];
    quotient_evaluated.insert(h0, x, h0_eval);

    profiling::set_phase(Phase::MultiOpen);
    let instance_labels: Vec<_> = (0..nb_committed_instances)
        .map(|i| [PolynomialLabel::CommittedInstance(i)])
        .collect();
    let queries = compute_queries(
        pk,
        &instance_labels,
        &instance_polys,
        &phase0_evaluated,
        &phase1_evaluated,
        &phase2_evaluated,
        &quotient_evaluated,
        &x_rotations,
    );

    PCS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_proof<F, PCS, T, ConcreteCircuit>(
    params: &PCS::Parameters,
    pk: &ProvingKey<F, PCS>,
    circuit: &ConcreteCircuit,
    #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
    instances: &[&[F]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
) -> Result<(), Error>
where
    F: ProofField<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
    ConcreteCircuit: Circuit<F>,
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

fn compute_instances<F, PCS, T>(
    params: &PCS::Parameters,
    pk: &ProvingKey<F, PCS>,
    instances: &[&[F]],
    nb_committed_instances: usize,
    transcript: &mut T,
) -> Result<InstanceSingle<F>, Error>
where
    F: ProofField<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
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
                transcript.common(&PCS::commit(
                    params,
                    &poly,
                    PolynomialLabel::CommittedInstance(i),
                ))?;
            }

            Ok(poly)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let instance_polys: Vec<_> = instance_values
        .iter()
        .map(|poly| {
            let lagrange_vec = pk.vk.domain.lagrange_from_vec(poly.to_vec());
            pk.fft_domain.lagrange_to_coeff(lagrange_vec)
        })
        .collect();

    Ok(InstanceSingle {
        instance_values,
        instance_polys,
    })
}

fn parse_advices<F, PCS, ConcreteCircuit>(
    pk: &ProvingKey<F, PCS>,
    circuit: &ConcreteCircuit,
    instances: &[&[F]],
    rng: &mut (impl RngCore + CryptoRng),
) -> Result<Vec<Polynomial<F, LagrangeCoeff>>, Error>
where
    F: PrimeField,
    PCS: PolynomialCommitmentScheme<F>,
    ConcreteCircuit: Circuit<F>,
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
    #[cfg(not(feature = "prover-par"))]
    ConcreteCircuit::FloorPlanner::synthesize_with_cached_regions(
        &mut witness,
        circuit,
        config,
        meta.constants.clone(),
        pk.region_starts.as_deref(),
    )?;
    // See `crate::par::layout`.
    #[cfg(feature = "prover-par")]
    crate::par::layout::synthesize(
        &mut witness,
        |witness| {
            witness.advice = vec![domain.empty_lagrange_rational(); meta.num_advice_columns];
        },
        circuit,
        config,
        meta.constants.clone(),
        pk.region_starts.as_deref(),
        &pk.region_starts_cache,
    )?;

    let mut advice_polys = batch_invert_rational::<F>(witness.advice);

    for (i, advice_polys) in advice_polys.iter_mut().enumerate() {
        if !witness.unblinded_advice.contains(&i) {
            for cell in &mut advice_polys[unusable_rows_start..] {
                *cell = F::random(&mut *rng);
            }
        } else {
            #[cfg(debug_assertions)]
            for cell in &advice_polys[unusable_rows_start..] {
                assert_eq!(*cell, F::ZERO);
            }
        }
    }

    Ok(advice_polys)
}

pub(crate) fn compute_nu_poly<F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, PCS>,
    trace: &ProverTrace<'_, F>,
) -> Polynomial<F, ExtendedLagrangeCoeff> {
    let ProverTrace {
        instance_polys,
        phase1_committed,
        phase2_committed,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
        ..
    } = &trace;
    let fft_domain = &pk.fft_domain;
    // Calculate the advice and instance cosets
    let advice_cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>> = phase1_committed
        .polys_of(&pk.vk.cs.advice_labels())
        .par_iter()
        .map(|poly| fft_domain.coeff_to_extended(poly.clone()))
        .collect();
    let instance_cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>> = instance_polys
        .par_iter()
        .map(|poly| fft_domain.coeff_to_extended(poly.clone()))
        .collect();

    // Evaluate the numerator polynomial nu(X) of the quotient polynomial
    // h(X) = nu(X) / (X^n-1): nu(X) is a random linear combination of all
    // independent identities
    pk.ev.evaluate_numerator::<ExtendedLagrangeCoeff>(
        fft_domain,
        &pk.vk.cs,
        &advice_cosets,
        &instance_cosets,
        &pk.fixed_cosets,
        *y,
        *beta,
        *gamma,
        *theta,
        *trash_challenge,
        phase1_committed,
        phase2_committed,
        &pk.l0,
        &pk.l_last,
        &pk.l_active_row,
        &pk.sigmas.cosets,
    )
}

/// Computes the quotient polynomial `h(X) = nu(X) / (X^n - 1)` and commits to
/// it, writing the commitment to the transcript.
///
/// `h(X)` is split into `quotient_poly_degree + 1` limbs `h_k(X)` of `n-2`
/// coefficients, with `h(X) = Σ_k X^{k(n-2)} h_k(X)`, so that each can be
/// committed with an SRS of size `n` after 2 terms for blinding. The blinded
/// limbs are committed to as one group, labeled `QuotientPiece(0)`,
/// `QuotientPiece(1)`, ..., which is returned in coefficient form.
///
/// # Panics
///
/// If `n < quotient_poly_degree + 2`, as the limbs could not hold `h(X)`.
fn compute_h_poly<F, PCS, T>(
    params: &PCS::Parameters,
    fft_domain: &FftDomain<F>,
    nu_poly: Polynomial<F, ExtendedLagrangeCoeff>,
    transcript: &mut T,
) -> Result<argument::prover::Committed<F, Coeff>, Error>
where
    F: PrimeField + Hashable<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    let domain = fft_domain.domain();
    // Construct quotient polynomial h(X) = nu(X) / (X^n - 1) in evaluation form
    let h_poly = domain.divide_by_vanishing_poly(nu_poly);

    // Convert h(X) to coefficient form
    let h_poly = fft_domain.extended_to_coeff(h_poly);

    commit_h_coeffs::<F, PCS, T>(params, domain, h_poly, transcript)
}

/// Splits the coefficients of `h(X)` (`extended_to_coeff` of the quotient)
/// into blinded limbs and commits to them; see [`compute_h_poly`].
#[cfg_attr(feature = "gpu", allow(unreachable_code, unused_mut))]
fn commit_h_coeffs<F, PCS, T>(
    params: &PCS::Parameters,
    domain: &EvaluationDomain<F>,
    mut h_poly: Vec<F>,
    transcript: &mut T,
) -> Result<argument::prover::Committed<F, Coeff>, Error>
where
    F: PrimeField + Hashable<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    // With the feature `gpu`, the coefficients are witness-dependent
    // values of the hook layer: adopt the stock allocation at once and
    // split it in erasing owners. Without the feature this block is not
    // compiled and the stock code below runs unchanged.
    #[cfg(feature = "gpu")]
    return commit_h_coeffs_erasing::<F, PCS, T>(
        params,
        domain,
        crate::gpu::erasing::ErasingVec::from_vec(h_poly),
        transcript,
    );
    // Let n := size of evaluation domain
    // Let d := degree of constraint system
    // Hence, the degree of the quotient poly is: d*(n-1) - n = (d-1)*(n-1) - 1,
    // and a domain of size (d-1)*(n-1) suffices to correctly represent it
    h_poly.truncate((domain.n - 1) as usize * domain.get_quotient_poly_degree());

    // Split h(X) up into limbs and add inter-limb blinding so that
    // individual limb commitments and evaluations do not leak information
    // about h(X).
    let limb_len = (domain.n - 2) as usize;
    let nb_limbs = domain.get_quotient_poly_degree() + 1;
    assert!(
        nb_limbs * limb_len >= h_poly.len(),
        "the domain is too small to split the quotient into {nb_limbs} limbs"
    );
    h_poly.resize(nb_limbs * limb_len, F::ZERO);
    let mut h_limbs = h_poly.chunks_exact(limb_len).map(|v| v.to_vec()).collect::<Vec<_>>();
    drop(h_poly);

    blind_quotient_limbs(&mut h_limbs);

    let h_limbs = (h_limbs.into_iter().enumerate())
        .map(|(i, h_limb)| {
            (
                PolynomialLabel::QuotientPiece(i),
                domain.coeff_from_vec(h_limb),
            )
        })
        .collect();

    argument::prover::Committed::commit::<PCS, T, _>(params, h_limbs, Polynomial::clone, transcript)
}

/// [`commit_h_coeffs`] with the feature `gpu`: `h_poly` and the limbs
/// split from it live in erasing owners (fixed capacity, zeroed on
/// drop), so no copy of `h` is made by a growing `Vec` and the buffer of
/// `h` is zeroed once the limbs are split off. The arithmetic, the
/// blinding draws and the transcript operations are those of
/// [`commit_h_coeffs`], in the same order, so proof bytes do not change.
/// The only hand-over to stock code is the last one: each blinded limb
/// becomes the `Vec` of a stock polynomial for the commitment, by moving
/// its allocation (`into_vec`, no copy), because the stock polynomial
/// type owns a `Vec`.
#[cfg(feature = "gpu")]
fn commit_h_coeffs_erasing<F, PCS, T>(
    params: &PCS::Parameters,
    domain: &EvaluationDomain<F>,
    mut h_poly: crate::gpu::erasing::ErasingVec<F>,
    transcript: &mut T,
) -> Result<argument::prover::Committed<F, Coeff>, Error>
where
    F: PrimeField + Hashable<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    h_poly.truncate((domain.n - 1) as usize * domain.get_quotient_poly_degree());

    let limb_len = (domain.n - 2) as usize;
    let nb_limbs = domain.get_quotient_poly_degree() + 1;
    assert!(
        nb_limbs * limb_len >= h_poly.len(),
        "the domain is too small to split the quotient into {nb_limbs} limbs"
    );
    // Each limb is one fixed allocation of `n` coefficients: `n - 2`
    // coefficients of `h` (zero beyond the end of `h`) and the two
    // blinding coefficients appended below, within the same capacity.
    // The stock `resize` of the whole `h` and the per-limb `to_vec`
    // copies, which reallocate and leave unzeroed copies, do not happen.
    let h: &[F] = &h_poly;
    let mut h_limbs: Vec<_> = (0..nb_limbs)
        .into_par_iter()
        .map(|k| {
            let mut limb =
                crate::gpu::erasing::ErasingVec::with_capacity_zeroed(limb_len + 2, limb_len);
            let start = k * limb_len;
            let avail = h.len().saturating_sub(start).min(limb_len);
            crate::par::columns::copy_from_slice(&mut limb[..avail], &h[start..start + avail]);
            limb
        })
        .collect();
    drop(h_poly);

    blind_quotient_limbs_erasing(&mut h_limbs);

    let h_limbs = (h_limbs.into_iter().enumerate())
        .map(|(i, h_limb)| {
            (
                PolynomialLabel::QuotientPiece(i),
                domain.coeff_from_vec(h_limb.into_vec()),
            )
        })
        .collect();

    // The commitment is made from references to the group's limbs, so
    // no copy of a limb is made for it; the caller holds the group in a
    // guard that zeroes the limbs when it is released.
    argument::prover::Committed::commit_without_copy::<PCS, T>(params, h_limbs, transcript)
}

/// [`blind_quotient_limbs`] over erasing owners, with the same draws in
/// the same order: the two blinding coefficients of a limb are appended
/// within its fixed capacity instead of by a growing `extend`.
#[cfg(feature = "gpu")]
fn blind_quotient_limbs_erasing<F: PrimeField>(
    quotient_limbs: &mut [crate::gpu::erasing::ErasingVec<F>],
) {
    let nr_limbs = quotient_limbs.len();
    assert!(nr_limbs >= 2);

    #[cfg(any(test, feature = "gpu-test"))]
    if let Some(mut rng) = test_blinding::rng() {
        for i in 1..nr_limbs {
            let (t, t_prime) = (F::random(&mut rng), F::random(&mut rng));
            quotient_limbs[i - 1].push_fixed(t);
            quotient_limbs[i - 1].push_fixed(t_prime);
            quotient_limbs[i][0] -= t;
            quotient_limbs[i][1] -= t_prime;
        }
        quotient_limbs[nr_limbs - 1].push_fixed(F::ZERO);
        quotient_limbs[nr_limbs - 1].push_fixed(F::ZERO);
        return;
    }

    for i in 1..nr_limbs {
        let (t, t_prime) = (F::random(OsRng), F::random(OsRng));
        quotient_limbs[i - 1].push_fixed(t);
        quotient_limbs[i - 1].push_fixed(t_prime);
        quotient_limbs[i][0] -= t;
        quotient_limbs[i][1] -= t_prime;
    }

    quotient_limbs[nr_limbs - 1].push_fixed(F::ZERO);
    quotient_limbs[nr_limbs - 1].push_fixed(F::ZERO);
}

/// Blinds the limbs `h_k(X)` of `h(X) = Σ_k X^{k(n-2)} h_k(X)`, of `n-2`
/// coefficients each, without changing `h(X)`: each boundary between two limbs
/// gets two random `t`, `t'`, added as `t X^{n-2} + t' X^{n-1}` to the lower
/// limb and subtracted as `t + t' X` from the upper one.
fn blind_quotient_limbs<F: PrimeField>(quotient_limbs: &mut [Vec<F>]) {
    let nr_limbs = quotient_limbs.len();
    assert!(nr_limbs >= 2);

    // Test-only: a seeded blinding RNG makes proofs reproducible.
    #[cfg(any(test, feature = "gpu-test"))]
    if let Some(mut rng) = test_blinding::rng() {
        for i in 1..nr_limbs {
            let (t, t_prime) = (F::random(&mut rng), F::random(&mut rng));
            quotient_limbs[i - 1].extend([t, t_prime]);
            quotient_limbs[i][0] -= t;
            quotient_limbs[i][1] -= t_prime;
        }
        quotient_limbs[nr_limbs - 1].extend([F::ZERO; 2]);
        return;
    }

    for i in 1..nr_limbs {
        let (t, t_prime) = (F::random(OsRng), F::random(OsRng));
        quotient_limbs[i - 1].extend([t, t_prime]);
        quotient_limbs[i][0] -= t;
        quotient_limbs[i][1] -= t_prime;
    }

    quotient_limbs[nr_limbs - 1].extend([F::ZERO; 2]);
}

/// Test-only seed of the quotient limb blinding (unit tests, and the feature
/// `gpu-test`): with a seed set, proofs are reproducible.
#[cfg(any(test, feature = "gpu-test"))]
pub(crate) mod test_blinding {
    use std::sync::Mutex;

    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    static SEED: Mutex<Option<u64>> = Mutex::new(None);

    pub(crate) fn set(seed: Option<u64>) {
        *SEED.lock().unwrap_or_else(|e| e.into_inner()) = seed;
    }

    pub(crate) fn rng() -> Option<ChaCha20Rng> {
        SEED.lock().unwrap_or_else(|e| e.into_inner()).map(ChaCha20Rng::seed_from_u64)
    }
}

pub(super) fn write_instance_evals_to_transcript<F, PCS, T>(
    pk: &ProvingKey<F, PCS>,
    nb_committed_instances: usize,
    instance_polys: &[Polynomial<F, Coeff>],
    x_rotations: &BTreeMap<Rotation, F>,
    transcript: &mut T,
) -> Result<Vec<F>, Error>
where
    F: PrimeField + Hashable<T::Hash>,
    PCS: PolynomialCommitmentScheme<F>,
    T: Transcript,
{
    let meta = &pk.vk.cs;

    // Batch-evaluate all polynomials with outer parallelism and sequential
    // Horner per task, avoiding the per-call rayon::scope overhead of the
    // internally-parallel eval_polynomial.
    let span = profiling::span(Kernel::PolyEval, meta.instance_queries.len());
    let instance_evals: Vec<F> = meta
        .instance_queries
        .par_iter()
        .map(|&(column, at)| eval_polynomial_seq(&instance_polys[column.index()], x_rotations[&at]))
        .collect();
    drop(span);

    // Write evaluations to transcript in the canonical order.
    for (eval, &(column, _)) in instance_evals.iter().zip(meta.instance_queries.iter()) {
        if column.index() < nb_committed_instances {
            transcript.write(eval)?;
        }
    }

    Ok(instance_evals)
}

#[allow(clippy::too_many_arguments)]
fn compute_queries<'a, F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    pk: &'a ProvingKey<F, PCS>,
    instance_labels: &'a [[PolynomialLabel; 1]],
    instance_polys: &'a [Polynomial<F, Coeff>],
    phase0_evals: &'a argument::prover::Evaluated<'a, F>,
    phase1_evals: &'a argument::prover::Evaluated<'a, F>,
    phase2_evals: &'a argument::prover::Evaluated<'a, F>,
    quotient_evals: &'a argument::prover::Evaluated<'a, F>,
    x_rotations: &'a BTreeMap<Rotation, F>,
) -> Vec<ProverQuery<'a, F>> {
    // The multi-open scales the first commitment by 1, which is best spent on
    // one read from the proof: the phase-0 commitments are known in advance and
    // a committed instance may be a constant, so both go after phases 1 and 2.
    iter::empty()
        .chain(phase1_evals.open())
        .chain(phase2_evals.open())
        .chain(phase0_evals.open())
        .chain(
            pk.vk.cs.instance_queries.iter().filter_map(move |&(column, at)| {
                let i = column.index();
                instance_labels.get(i).map(|labels| {
                    ProverQuery::new(
                        labels,
                        slice::from_ref(&instance_polys[i]),
                        x_rotations[&at],
                        labels[0].clone(),
                    )
                })
            }),
        )
        .chain(quotient_evals.open())
        .collect()
}

#[derive(Clone)]
pub(super) struct InstanceSingle<F: PrimeField> {
    pub instance_values: Vec<Polynomial<F, LagrangeCoeff>>,
    pub instance_polys: Vec<Polynomial<F, Coeff>>,
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
        poly::kzg::{KZGCommitmentScheme, params::ParamsKZG},
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

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    hash::Hash,
    iter,
    ops::RangeTo,
};

use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use super::{
    circuit::{
        sealed::{self},
        Advice, Any, Assignment, Challenge, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner,
        Instance, Selector,
    },
    lookup, permutation, Error, ProvingKey,
};

#[cfg(feature = "committed-instances")]
use crate::poly::EvaluationDomain;
use crate::{
    circuit::Value,
    plonk::{self, traces::ProverTrace, trash},
    poly::{
        batch_invert_rational, commitment::PolynomialCommitmentScheme, Coeff,
        ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, PolynomialRepresentation, ProverQuery,
        Rotation,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{arithmetic::eval_polynomial, rational::Rational},
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
    let mut meta = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut meta, circuits[0].params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut meta);

    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;

    struct InstanceSingle<F: PrimeField> {
        pub instance_values: Vec<Polynomial<F, LagrangeCoeff>>,
        pub instance_polys: Vec<Polynomial<F, Coeff>>,
    }

    // For each proof, wrap instance columns
    let instance: Vec<InstanceSingle<F>> = instances
        .iter()
        .map(|instance| -> Result<InstanceSingle<F>, Error> {
            let instance_values = instance
                .iter()
                .enumerate()
                .map(|(i, values)| {
                    // Committed instances go first.
                    let is_committed_instance = i < nb_committed_instances;
                    let mut poly = domain.empty_lagrange();
                    assert_eq!(poly.len(), domain.n as usize);
                    if values.len() > (poly.len() - (meta.nr_blinding_factors() + 1)) {
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
                    let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                    domain.lagrange_to_coeff(lagrange_vec)
                })
                .collect();

            Ok(InstanceSingle {
                instance_values,
                instance_polys,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    #[derive(Clone)]
    struct AdviceSingle<F: PrimeField, B: PolynomialRepresentation> {
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

        fn copy(
            &mut self,
            _: Column<Any>,
            _: usize,
            _: Column<Any>,
            _: usize,
        ) -> Result<(), Error> {
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

    // Obtain and commit to advice columns
    let (advice, challenges) = {
        let mut advice = vec![
            AdviceSingle::<F, LagrangeCoeff> {
                advice_polys: vec![domain.empty_lagrange(); meta.num_advice_columns],
            };
            instances.len()
        ];
        let mut challenges = HashMap::<usize, F>::with_capacity(meta.num_challenges);

        let unusable_rows_start = domain.n as usize - (meta.nr_blinding_factors() + 1);
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

            for ((circuit, advice), instances) in
                circuits.iter().zip(advice.iter_mut()).zip(instances)
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
                        #[cfg(feature = "sanity-checks")]
                        for cell in &advice_values[unusable_rows_start..] {
                            assert_eq!(*cell, F::ZERO);
                        }
                    }
                }

                let advice_commitments: Vec<_> = advice_values
                    .iter()
                    .map(|poly| CS::commit_lagrange(params, poly))
                    .collect();

                // Write advice commitments to the transcript
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

        (advice, challenges)
    };

    // Sample theta challenge for batching independent lookup columns
    let theta: F = transcript.squeeze_challenge();

    // Lookup argument: For each lookup, construct and commit to permuted advice and table columns
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

    // Sample beta challenge for permutation argument
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge for permutation argument
    let gamma: F = transcript.squeeze_challenge();

    // Permutation argument: Construct and commit to limbs of product polynomial
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

    // Lookup argument: For each lookup, construct and commit to product polynomial
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

    // Challenge for trash argument
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

    // Sample identity batching challenge y, for batching all independent identities
    let y: F = transcript.squeeze_challenge();

    let (instance_polys, instance_values) = instance
        .into_iter()
        .map(|i| (i.instance_polys, i.instance_values))
        .unzip();

    Ok(ProverTrace {
        advice_polys: advice
            .into_iter()
            .map(|a| {
                a.advice_polys
                    .into_iter()
                    .map(|p| domain.lagrange_to_coeff(p))
                    .collect()
            })
            .collect(),
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

    let domain = pk.get_vk().get_domain();
    let meta = pk.get_vk().cs();

    let ProverTrace {
        advice_polys,
        instance_polys,
        lookups,
        trashcans,
        permutations,
        challenges,
        y,
        beta,
        gamma,
        theta,
        trash_challenge,
        ..
    } = trace;

    // Calculate the advice and instance cosets
    let advice_cosets: Vec<Vec<Polynomial<F, ExtendedLagrangeCoeff>>> = advice_polys
        .iter()
        .map(|advice_polys| {
            advice_polys
                .iter()
                .map(|poly| domain.coeff_to_extended(poly.clone()))
                .collect()
        })
        .collect();
    let instance_cosets: Vec<Vec<Polynomial<F, ExtendedLagrangeCoeff>>> = instance_polys
        .iter()
        .map(|instance_polys| {
            instance_polys
                .iter()
                .map(|poly| domain.coeff_to_extended(poly.clone()))
                .collect()
        })
        .collect();

    // Evaluate the numerator polynomial nu(X) of the quotient polynomial h(X)=nu(X)/(X^n-1):
    // nu(X) is a random linear/parametric combination of all independent identities
    let nu_poly = pk.ev.evaluate_numerator::<ExtendedLagrangeCoeff>(
        &pk.vk.domain,
        &pk.vk.cs,
        &advice_cosets
            .iter()
            .map(|a| a.as_slice())
            .collect::<Vec<_>>(),
        &instance_cosets
            .iter()
            .map(|i| i.as_slice())
            .collect::<Vec<_>>(),
        &pk.fixed_cosets,
        &challenges,
        y,
        beta,
        gamma,
        theta,
        trash_challenge,
        &lookups,
        &trashcans,
        &permutations,
        &pk.l0,
        &pk.l_last,
        &pk.l_active_row,
        &pk.permutation.cosets,
    );

    // Advice and instance cosets are no longer required and are dropped to reduce
    // memory usage
    drop(advice_cosets);
    drop(instance_cosets);

    fn construct_h_poly<
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
        // Construct quotient polynomial h(X): divide nu(X) by t(X) = X^{params.n} - 1
        let h_poly = domain.divide_by_vanishing_poly(nu_poly);

        // Obtain final quotient polynomial h(X) in coefficient form
        let mut h_poly = domain.extended_to_coeff(h_poly);

        // Truncate coefficient vector of h(X) to match the size of the quotient polynomial;
        // the evaluation domain might be slightly larger than necessary because it always lies
        // on a power-of-two boundary
        h_poly.truncate(domain.n as usize * domain.get_quotient_poly_degree());

        // Split h(X) up into pieces h_i(X) of size n (i.e., deg(h_i)<=n-1);
        // h(X) = h_0(X) + X^n*h_1(X) + X^{2n}*h_2(X) + ... + X^{ln}*h_l(X)
        let h_pieces = h_poly
            .chunks_exact(domain.n as usize)
            .map(|v| domain.coeff_from_vec(v.to_vec()))
            .collect::<Vec<_>>();
        drop(h_poly);

        // Compute commitments to each h_i(X) limb
        let h_commitments: Vec<_> = h_pieces
            .iter()
            .map(|h_piece| CS::commit(params, h_piece))
            .collect();

        // Write limb commitments to the transcript
        for c in h_commitments.iter() {
            transcript.write(c)?;
        }

        Ok(h_pieces)
    }

    // Construct the quotient polynomial h(X) = nu(X)/(X^n-1), split it into limbs of size n,
    // commit to each limb separately, and write limb commitments to the transcript
    let quotient_limbs =
        construct_h_poly::<F, CS, T>(params, pk.get_vk().get_domain(), nu_poly, transcript)?;

    // Sample evaluation challenge x
    let x: F = transcript.squeeze_challenge();

    // For constructing the linearization poly, collect all evaluations
    // except those from simple selectors
    let mut instance_evals_combined = Vec::new();
    let mut advice_evals_combined = Vec::new();
    let mut permutation_evals_combined = Vec::new();
    let mut lookup_evals_combined = Vec::new();
    let mut trashcan_evals_combined = Vec::new();

    // Compute and hash evals for the polynomials of the committed instances of
    // each circuit
    for instance in instance_polys.iter() {
        let mut instance_evals = Vec::new();
        // Evaluate polynomials at omega^i x
        for &(column, at) in meta.instance_queries.iter() {
            if column.index() < nb_committed_instances {
                let eval = eval_polynomial(&instance[column.index()], domain.rotate_omega(x, at));
                instance_evals.push(eval);
                transcript.write(&eval)?;
            } else {
                let eval = eval_polynomial(&instance[column.index()], domain.rotate_omega(x, at));
                instance_evals.push(eval);
            }
        }
        instance_evals_combined.push(instance_evals);
    }

    // Compute and hash advice evals for each circuit instance
    for advice in advice_polys.iter() {
        // Evaluate polynomials at omega^i x
        let advice_evals: Vec<_> = meta
            .advice_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(&advice[column.index()], domain.rotate_omega(x, at))
            })
            .collect();

        advice_evals_combined.push(advice_evals.clone());

        // Hash each advice column evaluation
        for eval in advice_evals.iter() {
            transcript.write(eval)?;
        }
    }

    // Compute and hash evaluations of fixed columns (shared across all circuit instances)
    //
    // Filter out fixed evals corresponding to simple selectors
    // NB: `fixed_evals` is indexed according to `fixed_queries` (which is NOT indexed
    // per column index, but in the order in which queries were added)
    let fixed_evals: Vec<F> = meta
        .fixed_queries
        .iter()
        .map(|&(column, at)| {
            if meta.indices_simple_selectors.contains(&column.index()) {
                // Fixed columns corresponding to simple selectors don't need to be evaluated
                F::ONE
            } else {
                eval_polynomial(&pk.fixed_polys[column.index()], domain.rotate_omega(x, at))
            }
        })
        .collect();

    // Write only fixed evals corresponding to *non-simple* selectors to the transcript
    for (idx, (col, _)) in meta.fixed_queries.iter().enumerate() {
        if !meta.indices_simple_selectors.contains(&col.index()) {
            transcript.write(&fixed_evals[idx])?;
        }
    }

    // Evaluate common permutation data
    let permutations_common = pk.permutation.evaluate(x, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let permutations = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> {
            permutation.evaluate(pk, x, transcript, &mut permutation_evals_combined)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<Vec<lookup::prover::Evaluated<F>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            let mut lookup_evals =
                Vec::<crate::plonk::lookup::prover::PartiallyEvaluated<F>>::new();
            let c = lookups
                .into_iter()
                .map(|p| p.evaluate(pk, x, transcript, &mut lookup_evals))
                .collect::<Result<Vec<_>, _>>();
            lookup_evals_combined.push(lookup_evals);
            c
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the trashcans, if any, at x.
    let trashcans = trashcans
        .into_iter()
        .map(|trash| -> Result<Vec<_>, _> {
            let mut trashcan_evals =
                Vec::<crate::plonk::trash::prover::PartiallyEvaluated<F>>::new();
            let t = trash
                .into_iter()
                .map(|p| p.evaluate(x, transcript, &mut trashcan_evals))
                .collect::<Result<Vec<_>, _>>();
            trashcan_evals_combined.push(trashcan_evals);
            t
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Construct linearization polynomial
    let xn = x.pow([pk.vk.n()]);
    let nr_blinding_factors = pk.vk.cs.nr_blinding_factors();
    let l_evals = pk
        .vk
        .domain
        .l_i_range(x, xn, (-((nr_blinding_factors + 1) as i32))..=0);
    assert_eq!(l_evals.len(), 2 + nr_blinding_factors);
    let l_last = l_evals[0];
    let l_blind: F = l_evals[1..(1 + nr_blinding_factors)]
        .iter()
        .fold(F::ZERO, |acc, eval| acc + eval);
    let l_0 = l_evals[1 + nr_blinding_factors];

    fn construct_linearization_poly<F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
        evaluated_expressions: Vec<(Option<usize>, F)>,
        pk: &plonk::ProvingKey<F, CS>,
        y: F,
        x: F,
        xn: F,
        quotient_limbs: Vec<Polynomial<F, Coeff>>,
    ) -> Polynomial<F, Coeff> {
        // Construct the linearization polynomial:
        //
        //  S_1(X)*id_1(x) + y*S_2(X)*id_2(x) + y^2*S_3(X)*id_3(x) + ... + y^{k-1}*S_k(X)*id_k(x)
        //        - (h_0(X) + x^n*h_1(X) + x^{2n}*h_2(X) + ... + x^{l*n}*h_l(X)) * (x^n-1)
        //
        // where:
        // * S_i(X) are gate selector polys (possibly 1, if no gate selector exists)
        // * id_i(X) are the partially evaluated individual identities,
        // * h_j(X) are the limbs of the quotient polynomial.
        //

        // Construct linearized identities: LHS above
        // Initialize accumulator with zero polynomial
        let mut acc = vec![F::ZERO; pk.vk.domain.n as usize];
        for (column_idx, partial_eval) in evaluated_expressions {
            let poly = match column_idx {
                Some(column_index) => {
                    // Multiply fixed column corresponding to simple selector with partial evaluation of gate
                    // Note: `fixed_polys` of proving key are polynomials in coefficient form
                    let mut fixed_poly = pk.fixed_polys[column_index].clone();
                    for coeff in fixed_poly.values.iter_mut() {
                        *coeff *= partial_eval;
                    }
                    fixed_poly.values
                }
                None => {
                    // Return constant poly with constant term equal to fully evaluated gate
                    let mut constant_poly = vec![F::ZERO; pk.vk.domain.n as usize];
                    constant_poly[0] = partial_eval;
                    constant_poly
                }
            };
            // Multiply current state of accumulator
            // with batching challenge and add new poly
            for (ac, pc) in acc.iter_mut().zip(poly) {
                *ac = *ac * y + pc;
            }
        }
        let vanishing_eval = xn - F::ONE;
        // Construct linearized numerator poly: RHS above
        // (h_0(X) + x^n*h_1(X) + x^{2n}*h_2(X) + ... + x^{ln}*h_k(X)) * (x^n-1),
        // where h_i are commitments to the limbs of the quotient polynomial
        let mut linearized_h = vec![F::ZERO; pk.vk.domain.n as usize];
        for (i, piece) in quotient_limbs.into_iter().enumerate() {
            for (curr_coeff, new_coeff) in linearized_h.iter_mut().zip(piece.values) {
                *curr_coeff += (new_coeff * xn.pow([i as u64])) * vanishing_eval;
            }
        }
        for (lhs_coeff, rhs_coeff) in acc.iter_mut().zip(linearized_h) {
            *lhs_coeff -= rhs_coeff;
        }
        let linearization_poly = Polynomial {
            values: acc,
            _marker: std::marker::PhantomData::<Coeff>,
        };
        assert_eq!(eval_polynomial(&linearization_poly, x), F::ZERO);
        linearization_poly
    }

    let mut evaluated_expressions = Vec::new();
    for ((((advice_evals, instance_evals), permutation_evals), lookup_evals), trashcan_evals) in
        advice_evals_combined
            .iter()
            .zip(instance_evals_combined.iter())
            .zip(permutation_evals_combined.iter())
            .zip(lookup_evals_combined.iter())
            .zip(trashcan_evals_combined.iter())
    {
        let challenges = &challenges;
        let fixed_evals = &fixed_evals;
        // (Partially) evaluate polys from (custom) gates
        for (idx, e) in pk.vk.cs.gates.iter().flat_map(move |gate| {
            gate.polynomials().iter().map(move |poly| {
                let evaluation = poly.evaluate(
                    &|scalar| scalar,
                    &|_| panic!("virtual selectors are removed during optimization"),
                    &|query| fixed_evals[query.index().unwrap()],
                    &|query| advice_evals[query.index.unwrap()],
                    &|query| instance_evals[query.index.unwrap()],
                    &|challenge| challenges[challenge.index()],
                    &|a| -a,
                    &|a, b| a + &b,
                    &|a, b| a * &b,
                    &|a, scalar| a * &scalar,
                );
                (gate.simple_selector_index(), evaluation)
            })
        }) {
            evaluated_expressions.push((idx, e))
        }

        // Evaluate polys from permutation argument
        for e in permutation_evals.expressions(
            &pk.vk,
            &pk.vk.cs.permutation,
            &permutations_common,
            advice_evals,
            fixed_evals,
            instance_evals,
            l_0,
            l_last,
            l_blind,
            beta,
            gamma,
            x,
        ) {
            evaluated_expressions.push((None, e))
        }

        // Evaluate polys from lookup argument
        for e in lookup_evals
            .iter()
            .zip(pk.vk.cs.lookups.iter())
            .flat_map(move |(p, argument)| {
                p.expressions(
                    l_0,
                    l_last,
                    l_blind,
                    argument,
                    theta,
                    beta,
                    gamma,
                    advice_evals,
                    fixed_evals,
                    instance_evals,
                    challenges,
                )
            })
        {
            evaluated_expressions.push((None, e))
        }

        // Evaluate polys from trashcan
        for e in trashcan_evals
            .iter()
            .zip(pk.vk.cs.trashcans.iter())
            .flat_map(move |(p, argument)| {
                p.expressions(
                    argument,
                    trash_challenge,
                    advice_evals,
                    fixed_evals,
                    instance_evals,
                    challenges,
                )
            })
        {
            evaluated_expressions.push((None, e))
        }
    }

    let t = std::time::Instant::now();
    let linearization_poly =
        construct_linearization_poly(evaluated_expressions, pk, y, x, xn, quotient_limbs);
    println!(
        "Linearization poly built in {:?} ms",
        format_args!("{:.1}", t.elapsed().as_secs_f32() * 1000.0)
    );

    let queries = instance_polys
        .iter()
        .zip(advice_polys.iter())
        .zip(permutations.iter())
        .zip(lookups.iter())
        .zip(trashcans.iter())
        .flat_map(|((((instance, advice), permutation), lookups), trash)| {
            iter::empty()
                .chain(
                    pk.vk
                        .cs
                        .instance_queries
                        .iter()
                        .take(nb_committed_instances)
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(x, at),
                            poly: &instance[column.index()],
                        }),
                )
                .chain(
                    pk.vk
                        .cs
                        .advice_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(x, at),
                            poly: &advice[column.index()],
                        }),
                )
                .chain(permutation.open(pk, x))
                .chain(lookups.iter().flat_map(move |p| p.open(pk, x)))
                .chain(trash.iter().flat_map(move |p| p.open(x)))
        })
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                // Filter out fixed queries for simple selectors
                .filter(|(col, _)| !pk.vk.cs.indices_simple_selectors.contains(&col.index()))
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(x, at),
                    poly: &pk.fixed_polys[column.index()],
                }),
        )
        .chain(pk.permutation.open(x))
        // Add prover query of linearization poly at x
        .chain(iter::once(ProverQuery {
            point: domain.rotate_omega(x, Rotation::cur()),
            poly: &linearization_poly,
        }))
        .collect::<Vec<_>>();

    CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
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

#[test]
fn test_create_proof() {
    use halo2curves::bn256::{Bn256, Fr};
    use rand_core::OsRng;

    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
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

    let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(3, OsRng);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
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

//! TODO
#![allow(dead_code)]

use std::{iter, marker::PhantomData, time::Instant};
use std::hash::Hash;

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_chacha::ChaCha8Rng;
use rand_core::{CryptoRng, RngCore, SeedableRng};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{compute_trace, traces::FoldingProverTrace, Circuit, Error, ProvingKey},
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, EvaluationDomain, ExtendedLagrangeCoeff,
        LagrangeCoeff, Polynomial, PolynomialRepresentation,
    },
    protogalaxy::{
        utils::{batch_traces, linear_combination, pow_vec, LiftedFoldingTrace},
        FoldingPk,
    },
    utils::arithmetic::eval_polynomial,
};

/// This prover can perform a 2**K - 1 to one folding
struct ProtogalaxyProver<F: PrimeField, CS: PolynomialCommitmentScheme<F>, const K: usize> {
    folding_pk: FoldingPk<F>,
    folded_trace: FoldingProverTrace<F>,
    error: F,
    beta: [F; K],
    _commitment_scheme: PhantomData<CS>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize> ProtogalaxyProver<F, CS, K> {
    /// Initialise a Protogalaxy prover from a provided trace. Beta powers are
    /// initialised to `1`, while the error term is initialised as `0`.
    pub fn init<C, T>(
        params: &CS::Parameters,
        pk: ProvingKey<F, CS>,
        circuit: C,
        #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
        instance: &[&[F]],
        mut rng: impl CryptoRng + RngCore,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        C: Circuit<F>,
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
        let folded_trace = compute_trace(
            params,
            &pk,
            &[circuit],
            #[cfg(feature = "committed-instances")]
            nb_committed_instances,
            &[instance],
            &mut rng,
            transcript,
        )?
        .into_folding_trace(pk.vk.get_domain(), pk.fixed_values.clone());

        let folding_pk = FoldingPk::from(pk);
        let beta_powers = [F::ONE; K];
        let error_term = Self::compute_error(&folding_pk, &folded_trace, &beta_powers);

        assert_eq!(error_term, F::ZERO);

        Ok(Self {
            folding_pk,
            folded_trace,
            error: error_term,
            beta: beta_powers,
            _commitment_scheme: Default::default(),
        })
    }

    /// Fold
    /// TODO: We assume that circuits.len() + 1 is a power of 2.
    pub fn fold<C, T>(
        mut self,
        params: &CS::Parameters,
        pk: &ProvingKey<F, CS>,
        circuits: Vec<C>,
        #[cfg(feature = "committed-instances")] nb_committed_instances: usize,
        instances: &[&[&[F]]],
        mut rng: impl CryptoRng + RngCore,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        C: Circuit<F>,
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
        assert_eq!(circuits.len(), instances.len());

        let now = Instant::now();
        // TODO: Bunch of optimisations here. We could compute the trace for all
        // circuits at the same time. But the goal eventually is to fold
        // different circuits at a time.
        let traces = circuits
            .into_iter()
            .zip(instances.iter())
            .map(|(c, instance)| {
                let trace = compute_trace(
                    params,
                    pk,
                    &[c],
                    #[cfg(feature = "committed-instances")]
                    nb_committed_instances,
                    &[instance],
                    &mut rng,
                    transcript,
                )?;
                Ok(trace.into_folding_trace(pk.vk.get_domain(), pk.fixed_values.clone()))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        println!("Compute traces: {:?}", now.elapsed());

        let mut delta = transcript.squeeze_challenge();
        let delta_powers: [F; K] = std::array::from_fn(|_| {
            let res = delta;
            delta = delta * delta;
            res
        });

        let now = Instant::now();
        let f_poly = self.compute_f(&delta_powers);
        assert_eq!(self.error, f_poly.values[0]);
        println!("Time poly f: {:?}", now.elapsed());

        // Now we commit to it
        transcript.write(&CS::commit(params, &f_poly))?;
        println!("Time to commit to the zero polynomial (and write to transcript): {:?}", now.elapsed());

        let alpha = transcript.squeeze_challenge();

        let f_at_alpha = eval_polynomial(&f_poly.values, alpha);
        assert_eq!(f_at_alpha, F::ZERO);

        // We include the evaluation of the committed f at alpha
        // We'll need to prove that f at zero is the error term
        transcript.write(&f_at_alpha)?;

        let beta_star = self
            .beta
            .iter()
            .zip(delta_powers.iter())
            .map(|(beta, delta)| *beta + alpha * delta)
            .collect::<Vec<_>>();

        let time = Instant::now();
        let traces = std::iter::once(&self.folded_trace)
            .chain(traces.iter())
            .collect::<Vec<_>>();

        assert!(traces.len().is_power_of_two());

        // We now perform folding of the traces
        let degree = pk.vk.cs().degree() as u32;

        // We must increase the degree, since we need to count y as a variable.
        // Computing the real degree seems hard.
        let dk_domain = EvaluationDomain::new(degree + 3, traces.len().trailing_zeros());

        let lifted_trace = batch_traces(&dk_domain, &traces);
        let lift_trace_time = time.elapsed().as_millis();

        let poly_g = compute_poly_g(&self.folding_pk, &beta_star, &lifted_trace);
        dbg!(&poly_g);
        let poly_g_time = time.elapsed().as_millis() - lift_trace_time;

        let poly_k = dk_domain.divide_by_vanishing_poly(poly_g.clone());
        let poly_k_coeff = Polynomial {
            values: dk_domain.extended_to_coeff(poly_k),
            _marker: PhantomData,
        };

        transcript.write(&CS::commit(params, &poly_k_coeff))?;

        let gamma = transcript.squeeze_challenge();

        // Final check. Eval G(X), K(X) and Z(X) in \gamma
        let poly_to_eval_coeff = dk_domain.extended_to_coeff(poly_g);
        let g_in_gamma = eval_polynomial(&poly_to_eval_coeff, gamma);
        let k_in_gamma = eval_polynomial(&poly_k_coeff.values, gamma);
        let z_in_gamma = gamma.pow_vartime([dk_domain.n]) - F::ONE;

        transcript.write(&k_in_gamma)?;

        assert_ne!(g_in_gamma, F::ZERO);
        assert_eq!(g_in_gamma, k_in_gamma * z_in_gamma);

        // Update error term
        self.error = g_in_gamma;
        self.beta = beta_star.try_into().unwrap();

        self.folded_trace = fold_traces(&dk_domain, &traces, &gamma);
        let rest_time = time.elapsed().as_millis() - poly_g_time - lift_trace_time;

        println!("    Lift trace time      : {:?}ms", lift_trace_time);
        println!("    Poly G time          : {:?}ms", poly_g_time);
        println!("    Rest time            : {:?}ms", rest_time);

        Ok(self)
    }


    fn compute_h(folding_pk: &FoldingPk<F>, folded_trace: &FoldingProverTrace<F>) -> Polynomial<F, LagrangeCoeff> {
        let FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_values,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
            ..
        } = folded_trace;

        folding_pk.ev.evaluate_h::<LagrangeCoeff>(
            &folding_pk.domain,
            &folding_pk.cs,
            &advice_polys
                .iter()
                .map(Vec::as_slice)
                .collect::<Vec<_>>(),
            &instance_values
                .iter()
                .map(|i| i.as_slice())
                .collect::<Vec<_>>(),
            &fixed_polys,
            &challenges,
            *y,
            *beta,
            *gamma,
            *theta,
            *trash_challenge,
            &lookups,
            &trashcans,
            permutations,
            &folding_pk.l0,
            &folding_pk.l_last,
            &folding_pk.l_active_row,
            &folding_pk.permutation_pk_cosets,
        )
    }

    fn compute_error(folding_pk: &FoldingPk<F>, folded_trace: &FoldingProverTrace<F>, beta_pows: &[F; K]) -> F {
        let witness_poly = Self::compute_h(&folding_pk, &folded_trace);
        let beta_powers = pow_vec(beta_pows);

        witness_poly
            .values
            .into_par_iter()
            .zip(beta_powers.par_iter())
            .map(|(witness, beta_pow)| witness * beta_pow)
            .reduce(|| F::ZERO, |a, b| a + b)
    }

    // TODO: This can be optimised. Follow claim 4.4 from paper
    fn compute_f(&self, deltas: &[F; K]
    ) -> Polynomial<F, Coeff> {
        let domain = &EvaluationDomain::new(2, usize::BITS - (K - 1).leading_zeros());

        if self.error == F::ZERO {
            println!("Is zero");
            return Coeff::empty(domain);
        }

        let mut one_poly = Coeff::empty(domain);
        one_poly.values[0] = F::ONE;
        let one_poly = domain.coeff_to_lagrange(one_poly);

        let lagrange_polys = self.beta
            .iter()
            .zip(deltas.iter())
            .map(|(beta, delta)| {
                let mut poly = Coeff::empty(domain);
                poly.values[0] = *beta;
                poly.values[1] = *delta;
                domain.coeff_to_lagrange(poly)
            })
            .collect::<Vec<_>>();

        let witness_poly = Self::compute_h(&self.folding_pk, &self.folded_trace);
        let res = witness_poly
            .values
            .into_iter()
            .enumerate()
            .map(|(index, witness)| {
                let pow_i_poly = pow_i(&lagrange_polys, index + 1, &one_poly);
                pow_i_poly * witness
            })
            .reduce(|a, b| a + b)
            .expect("LEFTOVER - this should be parallelised");

        domain.lagrange_to_coeff(res)
    }
}

// Ugly, but we need to pass one for now. Would be nice if there is an identity
// trait.
// TODO: this could be replaced by pow_vec if we get the identity trait somehow.
fn pow_i<'a, F>(powers: &'a [F], i: usize, one: &'a F) -> F
where
    F: std::iter::Product<&'a F> + 'a,
{
    powers
        .iter()
        .enumerate()
        .filter(|(index, _)| (i >> index) & 1 == 1)
        .map(|(_, power)| power)
        .chain(iter::once(one))
        .product()
}

use crate::transcript::{Hashable, Sampleable, Transcript};

/// TODO: Fold instances
pub fn fold<F>(
    pk: &FoldingPk<F>,
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingProverTrace<F>],
) -> FoldingProverTrace<F>
where
    F: WithSmallOrderMulGroup<3>,
{
    let time = Instant::now();
    let lifted_trace = batch_traces(dk_domain, traces);
    let lift_trace_time = time.elapsed().as_millis();

    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    let mut betas = vec![F::ONE; pk.domain.k() as usize];
    let mut beta_pow = F::random(&mut rng);
    for beta in betas.iter_mut() {
        *beta = beta_pow;
        beta_pow *= beta_pow
    }

    let beta_time = time.elapsed().as_millis() - lift_trace_time;

    let poly_g = compute_poly_g(pk, &betas, &lifted_trace);
    let poly_g_time = time.elapsed().as_millis() - beta_time - lift_trace_time;

    let poly_k = dk_domain.divide_by_vanishing_poly(poly_g.clone());

    let gamma = F::random(&mut rng);

    let poly_k_coeff = dk_domain.extended_to_coeff(poly_k);

    // Final check. Eval G(X), K(X) and Z(X) in \gamma
    let poly_g_coeff = dk_domain.extended_to_coeff(poly_g);
    let g_in_gamma = eval_polynomial(&poly_g_coeff, gamma);
    let k_in_gamma = eval_polynomial(&poly_k_coeff, gamma);
    let z_in_gamma = gamma.pow_vartime([dk_domain.n]) - F::ONE;

    assert_ne!(g_in_gamma, F::ZERO);
    assert_eq!(g_in_gamma, k_in_gamma * z_in_gamma);

    let res = fold_traces(dk_domain, traces, &gamma);
    let rest_time = time.elapsed().as_millis() - poly_g_time - beta_time - lift_trace_time;

    println!("    Lift trace time      : {:?}ms", lift_trace_time);
    println!("    Beta powers time     : {:?}ms", beta_time);
    println!("    Poly G time          : {:?}ms", poly_g_time);
    println!("    Rest time            : {:?}ms", rest_time);

    res
}

/// Tasks to clean this up a bit:
/// We should also start a proper interface for folding. In this way, all
/// instances (meaning all challenges included) can be verified.
///
/// Then the proof verifier would:
/// * Parse the transcript and compute the different challenges.
/// * Perform the linear combination of challenges
/// * Perform the linear combinations of commitments of advice
/// * Perform the linear combination of fixed columns (from the VK)
/// * Verify the plonk proof with these new commitments
/// * Think about what we need to do with the error - unclear where we'll put
///   it.
///
/// Computes:
///
/// ```text
/// G(X) := ∑_{i ∈ [n]} pow_i(β*) · f_i(L₀(X)·ω + ∑_{j ∈ [k]} Lⱼ(X)·ωⱼ)} )
/// ```
///
/// where:
/// - β* are the randomisation challenges,
/// - f_i is the meta-identity (a linear combination of all identities) were i
///   represents each row of the trace,
/// - L₀, Lⱼ are folding lagrange polynomials,
/// - ω are the witness traces,
/// - pow_i denotes the power function.
///
/// We evaluate each `f_i` over a polynomial whose values are given in
/// evaluation form on the *folding domain*, a domain of size `k * n`. In other
/// words, instead of applying `f_i` to a trace represented by field elements
/// directly, we apply it to a trace represented by `k * n` field elements.
///
/// After evaluating `f_i`, we batch the resulting values with powers of β,
/// producing a single vector of size `k * n`. This vector represents the
/// polynomial `g` in evaluation form.
///
/// Since each folded instance corresponds to a different evaluation point of
/// the inner polynomial, we evaluate `f_i` at the *instance level* (i.e., each
/// row for a single trace), and then apply batching with powers of β. This
/// approach is more efficient than evaluating `f_i` row-by-row across all
/// instances at once, as it allows us to take advantage of the
/// `GraphEvaluator`.
///
/// The resulting polynomial `g` is defined over the *folded domain*, which is
/// much smaller. Each evaluation in this domain is obtained from the batched
/// values computed above.
fn compute_poly_g<F: PrimeField + WithSmallOrderMulGroup<3>>(
    pk: &FoldingPk<F>,
    beta: &[F],
    lifted_folding_trace: &LiftedFoldingTrace<F>,
) -> Polynomial<F, ExtendedLagrangeCoeff> {
    let beta_pows = pow_vec(beta);

    let mut g_poly = vec![F::ZERO; lifted_folding_trace.len()];
    for (j, instance) in g_poly.iter_mut().enumerate() {
        let FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_values,
            lookups,
            permutations: permutation,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
            ..
        } = &lifted_folding_trace[j];

        let witness_poly = pk.ev.evaluate_h::<LagrangeCoeff>(
            &pk.domain,
            &pk.cs,
            &advice_polys
                .iter()
                .map(Vec::as_slice)
                .collect::<Vec<_>>(),
            &instance_values
                .iter()
                .map(|i| i.as_slice())
                .collect::<Vec<_>>(),
            fixed_polys,
            challenges,
            *y,
            *beta,
            *gamma,
            *theta,
            *trash_challenge,
            lookups,
            trashcans,
            permutation,
            &pk.l0,
            &pk.l_last,
            &pk.l_active_row,
            &pk.permutation_pk_cosets,
        );

        dbg!(witness_poly[42]);

        *instance = witness_poly
            .values
            .into_par_iter()
            .zip(beta_pows.par_iter())
            .map(|(witness, beta_pow)| witness * beta_pow)
            .reduce(|| F::ZERO, |a, b| a + b);
    }

    Polynomial {
        values: g_poly,
        _marker: Default::default(),
    }
}

/// Function to fold traces over an evaluation `\gamma`
fn fold_traces<F: PrimeField + WithSmallOrderMulGroup<3>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingProverTrace<F>],
    gamma: &F,
) -> FoldingProverTrace<F> {
    let lagrange_polys = (0..traces.len())
        .map(|i| {
            // For the moment we only support batching of traces of dimension one.
            assert_eq!(traces[i].advice_polys.len(), 1);
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            l
        })
        .map(|p| dk_domain.lagrange_to_coeff(p))
        .collect::<Vec<_>>();

    let trace_domain_size = traces[0].fixed_polys[0].num_coeffs();

    let buffer = FoldingProverTrace::init(
        trace_domain_size,
        traces[0].fixed_polys.len(),
        traces[0].advice_polys[0].len(),
        traces[0].instance_polys[0].len(),
        traces[0].lookups[0].len(),
        traces[0].trashcans[0].len(),
        traces[0].permutations[0].sets.len(),
        traces[0].challenges.len(),
    );
    let lagranges_in_gamma = lagrange_polys
        .iter()
        .map(|poly| eval_polynomial(poly, *gamma))
        .collect::<Vec<_>>();

    linear_combination(buffer, traces, &lagranges_in_gamma)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ff::Field;
    use midnight_curves::{Bls12, Fq};
    use rand_chacha::ChaCha8Rng;
    use rand_core::{RngCore, SeedableRng};

    use crate::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            keygen_pk, keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem, Error,
            Expression, Selector, TableColumn,
        },
        poly::{
            kzg::{params::ParamsKZG, KZGCommitmentScheme},
            Rotation,
        },
        protogalaxy::{prover::ProtogalaxyProver, verifier::ProtogalaxyVerifier},
        transcript::{CircuitTranscript, Transcript},
    };
    use crate::plonk::{Constraints, create_proof};

    #[derive(Clone, Copy)]
    struct TestCircuit {
        witness: [Value<Fq>; 1 << 8],
    }

    impl TestCircuit {
        fn from(witness: [Value<Fq>; 1 << 8]) -> Self {
            Self { witness }
        }
    }

    #[derive(Debug, Clone)]
    struct MyConfig {
        mul_selector: Selector,
        table_selector: Selector,
        table: TableColumn,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
    }

    impl Circuit<Fq> for TestCircuit {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                witness: [Value::unknown(); 1 << 8],
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fq>) -> MyConfig {
            let config = MyConfig {
                mul_selector: meta.complex_selector(),
                table_selector: meta.complex_selector(),
                table: meta.lookup_table_column(),
                a: meta.advice_column(),
                b: meta.advice_column(),
                c: meta.advice_column(),
            };

            meta.enable_equality(config.a);
            meta.enable_equality(config.b);

            meta.create_gate("mul", |meta| {
                let a = meta.query_advice(config.a, Rotation::cur());
                let b = meta.query_advice(config.b, Rotation::cur());
                let c = meta.query_advice(config.c, Rotation::cur());
                Constraints::with_selector(config.mul_selector, vec![a * b - c])
            });

            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(config.table_selector);
                let not_selector = Expression::Constant(Fq::ONE) - selector.clone();

                let a = meta.query_advice(config.a, Rotation::cur());
                vec![(selector * a + not_selector, config.table)]
            });

            config
        }

        fn synthesize(
            &self,
            config: MyConfig,
            mut layouter: impl Layouter<Fq>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "8-bit table",
                |mut table| {
                    for row in 0u64..(1 << 8) {
                        table.assign_cell(
                            || format!("row {row}"),
                            config.table,
                            row as usize,
                            || Value::known(Fq::from(row + 1)),
                        )?;
                    }

                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "assign values",
                |mut region| {
                    for (offset, val) in self.witness.into_iter().enumerate() {
                        config.table_selector.enable(&mut region, offset)?;
                        config.mul_selector.enable(&mut region, offset)?;
                        let a = region.assign_advice(|| "a", config.a, offset, || val)?;
                        a.copy_advice(|| "copy a to b", &mut region, config.b, offset)?;
                        // region.assign_advice(|| "b", config.b, offset, || val)?;
                        region.assign_advice(|| "c", config.c, offset, || val.map(|v| v * v))?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn folding_test() {
        const K: usize = 14;
        let k = 4; // number of folding instances

        let rng = ChaCha8Rng::from_seed([0u8; 32]);
        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K as u32, rng);

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        let mut rand_bytes = [0u8; 1 << 8];
        rng.fill_bytes(&mut rand_bytes);

        let witnesses = (0..k)
            .map(|_| {
                rand_bytes
                    .into_iter()
                    .map(|byte| Value::known(Fq::from((byte as u64) + 1)))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let circuits = witnesses
            .into_iter()
            .map(TestCircuit::from)
            .collect::<Vec<_>>();

        let vk =
            keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuits[0], K as u32)
                .expect("keygen_vk should not fail");
        let pk = keygen_pk(vk.clone(), &circuits[0]).expect("keygen_pk should not fail");

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        // Normal proofs. We first generate normal proofs to test performance
        let normal_proving = Instant::now();
        for circuit in circuits.iter() {
            let mut transcript = CircuitTranscript::init();
            create_proof(
                &params,
                &pk,
                &[circuit.clone()],
                #[cfg(feature = "committed-instances")]
                0,
                &[&[]],
                &mut rng,
                &mut transcript,
            ).expect("Failed to produce a proof");
        }
        println!("Time to generate {} proofs: {:?}", circuits.len(), normal_proving.elapsed());

        // Fold proofs. We first initialise folding with the first circuit
        let folding = Instant::now();
        let now = Instant::now();
        let mut transcript = CircuitTranscript::init();
        let protogalaxy = ProtogalaxyProver::<_, _, K>::init(
            &params,
            pk.clone(),
            circuits[0],
            #[cfg(feature = "committed-instances")]
            0,
            &[],
            &mut rng,
            &mut transcript,
        )
        .expect("Failed to initialise folder");

        let protogalaxy = protogalaxy
            .fold(
                &params,
                &pk,
                circuits[1..].to_vec(),
                #[cfg(feature = "committed-instances")]
                0,
                &[&[], &[], &[]],
                &mut rng,
                &mut transcript,
            )
            .expect("Failed to fold many instances");

        let folding_time = folding.elapsed().as_millis();
        println!("Time for folding: {:?}ms", folding_time);

        let mut transcript = CircuitTranscript::init_from_bytes(&transcript.finalize());

        // Now we begin verification
        let protogalaxy_verifier = ProtogalaxyVerifier::<_, _, K>::init(
            &vk,
            #[cfg(feature = "committed-instances")]
            &[&[]],
            &[&[]],
            &mut transcript,
        )
        .expect("Failed - unexpected");

        protogalaxy_verifier
            .fold(
                &vk,
                #[cfg(feature = "committed-instances")]
                &[&[]],
                &[&[], &[], &[]],
                &mut transcript,
            )
            .expect("Failed to fold instances by the verifier")
            .is_sat(
                &params,
                &vk,
                &pk.ev,
                protogalaxy.folded_trace,
                &protogalaxy.folding_pk.l0,
                &protogalaxy.folding_pk.l_last,
                &protogalaxy.folding_pk.l_active_row,
                &protogalaxy.folding_pk.permutation_pk_cosets,
            )
            .expect("Folding finalizer failed");

        println!("Folding was a success");
    }
}

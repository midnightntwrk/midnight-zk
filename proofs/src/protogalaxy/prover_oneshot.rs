//! TODO
#![allow(dead_code)]

use std::{hash::Hash, marker::PhantomData, time::Instant};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{
        compute_queries, compute_trace,
        traces::{FoldingProverTrace, ProverTrace},
        trash, write_evals_to_transcript, Circuit, Error, ProvingKey,
    },
    poly::{
        commitment::PolynomialCommitmentScheme, EvaluationDomain, ExtendedLagrangeCoeff,
        LagrangeCoeff, Polynomial, ProverQuery,
    },
    protogalaxy::{
        utils::{batch_traces, linear_combination},
        FoldingPk,
    },
    utils::arithmetic::eval_polynomial,
};

struct ProtogalaxyProverOneShot<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    const K: usize,
> {
    _phantom_data: PhantomData<(F, CS)>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize>
    ProtogalaxyProverOneShot<F, CS, K>
{
    /// Fold
    /// We assume that circuits.len() is a power of 2.
    pub fn fold<C, T>(
        params: &CS::Parameters,
        pk: ProvingKey<F, CS>,
        circuits: Vec<C>,
        nb_committed_instances: usize,
        instances: &[&[&[F]]],
        mut rng: impl CryptoRng + RngCore,
        transcript: &mut T,
    ) -> Result<(), Error>
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

        let degree = pk.vk.cs().degree() as u32;
        println!("Degree: {:?}", degree);

        let pk_domain_size: usize = pk.vk.get_domain().n as usize;
        println!("PK domain size: {:?}", pk_domain_size);
        assert_eq!(pk_domain_size, 1 << K);

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
                    &pk,
                    &[c],
                    nb_committed_instances,
                    &[instance],
                    &mut rng,
                    transcript,
                )?;
                Ok(trace.into_folding_trace(pk.fixed_values.clone()))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        println!("Compute traces: {:?}", now.elapsed());
        let traces = traces.iter().collect::<Vec<_>>();

        let beta_pg = transcript.squeeze_challenge();

        let time = Instant::now();
        assert!(traces.len().is_power_of_two());

        // We now perform folding of the traces
        let dk_domain = EvaluationDomain::new(
            pk.vk.cs().folding_degree() as u32,
            traces.len().trailing_zeros(),
        );
        let folding_pk = FoldingPk::from(pk.clone());

        // Compute evaluations of lagrange polynomials on beta_pg
        let lagrange_on_beta: Vec<F> = eval_lagrange_on_beta(pk.vk.get_domain(), &beta_pg);
        let lagrange_beta_time = time.elapsed().as_millis();

        let (poly_g, poly_g_unbatched) =
            Self::compute_poly_g(&folding_pk, &dk_domain, &lagrange_on_beta, &traces);
        let poly_g_time = time.elapsed().as_millis() - lagrange_beta_time;

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

        let error_terms =
            compute_error_terms(pk_domain_size, &dk_domain, &poly_g_unbatched, &gamma);

        assert_ne!(g_in_gamma, F::ZERO);
        assert_eq!(g_in_gamma, k_in_gamma * z_in_gamma);

        // Compare error term vector with error term

        let error_sum: F = error_terms
            .par_iter()
            .zip(lagrange_on_beta.par_iter())
            .map(|(&error, &coeff)| error * coeff)
            .reduce(|| F::ZERO, |a, b| a + b);
        assert_eq!(error_sum, g_in_gamma);

        // Update error term
        let folded_trace = Self::fold_traces(&dk_domain, &traces, &gamma);
        let rest_time = time.elapsed().as_millis() - poly_g_time - lagrange_beta_time;

        println!(
            "    Lagrange polynomials on beta      : {:?}ms",
            lagrange_beta_time
        );
        println!("    Poly G time          : {:?}ms", poly_g_time);
        println!("    Rest time            : {:?}ms", rest_time);

        // Now we need to generate the last proof.
        let error_lagrange: Polynomial<F, LagrangeCoeff> = Polynomial {
            values: error_terms.clone(),
            _marker: PhantomData,
        };
        let error_coeff = pk.vk.get_domain().lagrange_to_coeff(error_lagrange.clone());
        let committed_error = CS::commit_lagrange(params, &error_lagrange);

        transcript.write(&committed_error)?;

        // Now we need to create the final proof and verify that the opening of the
        // instance column evaluates at `e` in beta.
        // The PK needs to update the fixed values, as these are now folded
        let fixed_values = folded_trace.fixed_polys.clone();
        let fixed_polys = fixed_values
            .iter()
            .cloned()
            .map(|p| pk.vk.get_domain().lagrange_to_coeff(p))
            .collect::<Vec<_>>();
        let fixed_cosets = fixed_polys
            .iter()
            .cloned()
            .map(|p| pk.vk.get_domain().coeff_to_extended(p))
            .collect::<Vec<_>>();

        // We need to update the fixed polynomials from the proving key.
        let mut pk_final_proof = pk.clone();
        pk_final_proof.fixed_polys = fixed_polys;
        pk_final_proof.fixed_values = fixed_values;
        pk_final_proof.fixed_cosets = fixed_cosets;

        let folded_trace = ProverTrace::from_folding_trace(folded_trace.clone());

        // Now we need to finalise the proof. We do not use the finalise_proof function
        // as we need to 'correct' the plonk identity, with the error term from
        // protogalaxy.

        let domain = pk.get_vk().get_domain();
        let h_poly = crate::plonk::compute_h_poly(&pk_final_proof, &folded_trace);

        let ProverTrace {
            advice_polys,
            instance_polys,
            lookups,
            trashcans,
            permutations,
            vanishing,
            ..
        } = folded_trace;

        // When constructing the vanishing polynomial, we need to correct the identity.
        let correction = domain.coeff_to_extended(error_coeff.clone());
        let h = h_poly - &correction;
        let vanishing = vanishing.construct::<CS, T>(params, domain, h, transcript)?;

        let x: F = transcript.squeeze_challenge();

        let advice_polys = advice_polys
            .into_iter()
            .map(|a| a.into_iter().map(|p| domain.lagrange_to_coeff(p)).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        write_evals_to_transcript(
            &pk_final_proof,
            nb_committed_instances,
            &instance_polys,
            &advice_polys,
            x,
            transcript,
        )?;

        // We also add the evaluation of the correction polynomial
        let correction_eval = eval_polynomial(&error_coeff, x);
        transcript.write(&correction_eval)?;

        let vanishing = vanishing.evaluate(x, domain, transcript)?;
        pk_final_proof.permutation.evaluate(x, transcript)?;

        let permutations = permutations
            .into_iter()
            .map(|permutation| -> Result<_, _> {
                permutation.evaluate(&pk_final_proof, x, transcript)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let lookups = lookups
            .into_iter()
            .map(|lookups| -> Result<Vec<_>, _> {
                lookups
                    .into_iter()
                    .map(|p| p.evaluate(&pk_final_proof, x, transcript))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let trashcans: Vec<Vec<trash::prover::Evaluated<F>>> = trashcans
            .into_iter()
            .map(|trash| -> Result<Vec<_>, _> {
                trash
                    .into_iter()
                    .map(|p| p.evaluate(domain, x, transcript))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut queries = compute_queries(
            &pk_final_proof,
            nb_committed_instances,
            &instance_polys,
            &advice_polys,
            &permutations,
            &lookups,
            &trashcans,
            &vanishing,
            x,
        );

        // We push the query of the error polynomial in X and in Beta
        queries.push(ProverQuery {
            point: x,
            poly: &error_coeff,
        });

        queries.push(ProverQuery {
            point: beta_pg,
            poly: &error_coeff,
        });

        CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
    }

    fn compute_h(
        folding_pk: &FoldingPk<F>,
        folded_trace: &FoldingProverTrace<F>,
    ) -> Polynomial<F, LagrangeCoeff> {
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
            trash_challenge,
            y,
            ..
        } = folded_trace;

        folding_pk.ev.evaluate_h::<LagrangeCoeff>(
            &folding_pk.domain,
            &folding_pk.cs,
            &advice_polys.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &instance_values.iter().map(|i| i.as_slice()).collect::<Vec<_>>(),
            fixed_polys,
            challenges,
            y,
            *beta,
            *gamma,
            theta,
            *trash_challenge,
            lookups,
            trashcans,
            permutations,
            &folding_pk.l0,
            &folding_pk.l_last,
            &folding_pk.l_active_row,
            &folding_pk.permutation_pk_cosets,
        )
    }

    /// Computes:
    ///
    /// ```text
    /// G(X) := ∑_{i ∈ [n]} pow_i(β*) · f_i(L₀(X)·ω + ∑_{j ∈ [k]} Lⱼ(X)·ωⱼ)} )
    /// ```
    ///
    /// where:
    /// - β* are the randomisation challenges,
    /// - f_i is the meta-identity (a linear combination of all identities) were
    ///   i represents each row of the trace,
    /// - L₀, Lⱼ are folding lagrange polynomials,
    /// - ω are the witness traces,
    /// - pow_i denotes the power function.
    ///
    /// We evaluate each `f_i` over a polynomial whose values are given in
    /// evaluation form on the *folding domain*, a domain of size `k * n`. In
    /// other words, instead of applying `f_i` to a trace represented by
    /// field elements directly, we apply it to a trace represented by `k *
    /// n` field elements.
    ///
    /// After evaluating `f_i`, we batch the resulting values with powers of β,
    /// producing a single vector of size `k * n`. This vector represents the
    /// polynomial `g` in evaluation form.
    ///
    /// Since each folded instance corresponds to a different evaluation point
    /// of the inner polynomial, we evaluate `f_i` at the *instance level*
    /// (i.e., each row for a single trace), and then apply batching with
    /// powers of β. This approach is more efficient than evaluating `f_i`
    /// row-by-row across all instances at once, as it allows us to take
    /// advantage of the `GraphEvaluator`.
    ///
    /// The resulting polynomial `g` is defined over the *folded domain*, which
    /// is much smaller. Each evaluation in this domain is obtained from the
    /// batched values computed above.
    /// This returns the aggregated polynomial G, as well as the vector of
    /// errors.
    fn compute_poly_g(
        folding_pk: &FoldingPk<F>,
        domain: &EvaluationDomain<F>,
        beta_coeffs: &Vec<F>,
        traces: &[&FoldingProverTrace<F>],
    ) -> (Polynomial<F, ExtendedLagrangeCoeff>, Vec<Vec<F>>) {
        let lifted_folding_trace = batch_traces(domain, traces);

        // In the future, we'll output simply a commitment to it, but
        // perhaps at an upper level function.
        let mut g_poly_unbatched =
            vec![vec![F::ZERO; folding_pk.domain.n as usize]; lifted_folding_trace.len()];
        let g_poly = g_poly_unbatched
            .iter_mut()
            .zip(lifted_folding_trace.iter())
            .map(|(instance, trace)| {
                let witness_poly = Self::compute_h(folding_pk, trace);
                *instance = witness_poly.values;

                instance
                    .into_par_iter()
                    .zip(beta_coeffs.par_iter())
                    .map(|(witness, beta_coef)| *witness * beta_coef)
                    .reduce(|| F::ZERO, |a, b| a + b)
            })
            .collect();

        (
            Polynomial {
                values: g_poly,
                _marker: Default::default(),
            },
            g_poly_unbatched,
        )
    }

    /// Function to fold traces over an evaluation `\gamma`
    fn fold_traces(
        dk_domain: &EvaluationDomain<F>,
        traces: &[&FoldingProverTrace<F>],
        gamma: &F,
    ) -> FoldingProverTrace<F> {
        let lagrange_polys = (0..traces.len())
            .map(|i| {
                // For the moment we only support batching of traces of dimension one.
                // David: what does this mean?
                assert_eq!(traces[i].advice_polys.len(), 1);
                let mut l = dk_domain.empty_lagrange();
                l[i] = F::ONE;
                l
            })
            .map(|p| dk_domain.lagrange_to_coeff(p))
            .collect::<Vec<_>>();

        let buffer = FoldingProverTrace::with_same_dimensions(traces[0]);
        let lagranges_in_gamma = lagrange_polys
            .iter()
            .map(|poly| eval_polynomial(poly, *gamma))
            .collect::<Vec<_>>();

        linear_combination(buffer, traces, &lagranges_in_gamma)
    }
}

use crate::transcript::{Hashable, Sampleable, Transcript};

/// Computes the error terms t_i = f_i(w(\gamma)) where w(X) = ∑_{j ∈ [k]}
/// Lⱼ(X)·ωⱼ is the polynomial that interpolates the witnesses.
fn compute_error_terms<F: PrimeField + WithSmallOrderMulGroup<3>>(
    pk_domain_size: usize,
    dk_domain: &EvaluationDomain<F>,
    poly_g_unbatched: &[Vec<F>], // use slice instead of &Vec
    gamma_pg: &F,
) -> Vec<F> {
    let n_rows = poly_g_unbatched.len();

    // Parallel over columns j
    (0..pk_domain_size)
        .into_par_iter()
        .map(|j| {
            // Allocate buffer once per iteration
            let mut poly_evals = Vec::with_capacity(n_rows);
            for row in poly_g_unbatched {
                poly_evals.push(row[j]);
            }

            // Convert to coefficient basis
            let coeff_poly = dk_domain.extended_to_coeff(Polynomial {
                values: poly_evals,
                _marker: PhantomData,
            });

            // Evaluate at gamma_pg
            eval_polynomial(&coeff_poly, *gamma_pg)
        })
        .collect::<Vec<F>>() // collect the results into a Vec<F>
}

/// Computes the lagrange polynomials for a domain (with root omega)
/// Then, it evaluates them at 'beta', obtaining a vector of coefficients.
/// It uses the formula: L_i(beta) = Z(beta) * omega^i / (n * (beta - omega^i))
/// We decompose it into a fixed part [Z(beta) / n] and a variable part [omega^i / (beta - omega^i)]
pub fn eval_lagrange_on_beta<F: PrimeField + WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    beta: &F,
) -> Vec<F> {
    let pk_domain_size = domain.n as usize;
    let omega: F = domain.get_omega(); // generator of multiplicative subgroup

    let n_fe = F::from(pk_domain_size as u64);
    
    // fixed_term = Z(beta) / n = (beta^n - 1) / n
    let fixed_term = (beta.pow([pk_domain_size as u64]) - F::ONE) * n_fe.invert().unwrap();

    // Calculate all the omega powers and store them in a vector
    // TODO: parallelize? We could start from powers omega^0, omega^m, omega^2m, ...
    // Where for a domain of size n, m = n / #threads
    let mut omegas: Vec<F> = Vec::with_capacity(pk_domain_size);
    omegas.push(F::ONE);
    for _ in 0..(pk_domain_size - 1) {
        omegas.push(*omegas.last().unwrap() * omega);
    }

    let result = omegas.into_par_iter()
        .map(|omega_i| {
            fixed_term * omega_i * (*beta - omega_i).invert().unwrap()
        })
        .collect();
    result
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
            create_proof, keygen_pk, keygen_vk_with_k, prepare, Advice, Circuit, Column,
            ConstraintSystem, Constraints, Error, Expression, Selector, TableColumn,
        },
        poly::{
            kzg::{params::ParamsKZG, KZGCommitmentScheme},
            Rotation,
        },
        protogalaxy::{
            prover_oneshot::{ProtogalaxyProverOneShot, eval_lagrange_on_beta}, 
            verifier_oneshot::ProtogalaxyVerifierOneShot,
        },
        transcript::{CircuitTranscript, Transcript},
        utils::arithmetic::eval_polynomial,
    };

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
                Constraints::with_selector(
                    config.mul_selector,
                    vec![a.clone() * a * b.clone() * b - c],
                )
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
                        region.assign_advice(
                            || "c",
                            config.c,
                            offset,
                            || val.map(|v| v * v * v * v),
                        )?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }
    use crate::poly::commitment::Guard;

    #[test]
    fn lagrange_poly_test() {

        const K: usize = 9;
        let k = 1; // number of folding instances

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
        let circuits = witnesses.into_iter().map(TestCircuit::from).collect::<Vec<_>>();

        let vk =
            keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuits[0], K as u32)
                .expect("keygen_vk should not fail");

        let pk_domain_size = 1 << K;

        let beta = Fq::from(rand::random::<u64>());

        let lagrange_on_beta = eval_lagrange_on_beta(&vk.get_domain(), &beta);

        // Now we compute the same values using lagrange polynomials
        let mut lagrange_polys = Vec::with_capacity(pk_domain_size);
        for i in 0..pk_domain_size {
            let mut l_i = vk.get_domain().empty_lagrange();
            l_i[i] = Fq::ONE;

            let l_coeff = vk.get_domain().lagrange_to_coeff(l_i);
            lagrange_polys.push(l_coeff);
        }

            let pk_domain_size = vk.get_domain().n as usize;

        for i in 0..pk_domain_size {
            let eval = eval_polynomial(&lagrange_polys[i], beta);
            assert_eq!(eval, lagrange_on_beta[i]);
        }
    }


    #[test]
    fn folding_test_oneshot() {
        const K: usize = 9;
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
        let circuits = witnesses.into_iter().map(TestCircuit::from).collect::<Vec<_>>();

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
                &[*circuit],
                0,
                &[&[]],
                &mut rng,
                &mut transcript,
            )
            .expect("Failed to produce a proof");

            let proof = transcript.finalize();
            let mut transcript = CircuitTranscript::init_from_bytes(&proof);
            prepare(&vk, &[&[]], &[&[]], &mut transcript)
                .unwrap()
                .verify(&params.verifier_params())
                .unwrap();
        }
        println!(
            "Time to generate {} proofs: {:?}",
            circuits.len(),
            normal_proving.elapsed()
        );

        // Fold proofs. We first initialise folding with the first circuit
        let folding = Instant::now();
        let mut transcript = CircuitTranscript::init();

        ProtogalaxyProverOneShot::<_, _, K>::fold(
            &params,
            pk.clone(),
            circuits,
            0,
            &[&[], &[], &[], &[]],
            &mut rng,
            &mut transcript,
        )
        .expect("Failed to fold many instances");
        println!("Time to fold: {:?}", folding.elapsed());

        let mut transcript = CircuitTranscript::init_from_bytes(&transcript.finalize());
        // Now we begin verification
        ProtogalaxyVerifierOneShot::<_, _, K>::fold(
            &vk,
            &[&[], &[], &[], &[]],
            &[&[], &[], &[], &[]],
            &mut transcript,
        )
        .expect("Failed to fold instances by the verifier")
        .verify(&params.verifier_params())
        .expect("Verification failed");

        println!("Folding was a success");
    }
}

//! TODO
#![allow(dead_code)]

use ff::{PrimeField, WithSmallOrderMulGroup};
use rand_chacha::ChaCha8Rng;
use rand_core::SeedableRng;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::traces::FoldingTrace,
    poly::{EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial},
    protogalaxy::{
        utils::{batch_traces, linear_combination, pow_vec, LiftedFoldingTrace},
        FoldingPk,
    },
    utils::arithmetic::eval_polynomial,
};

fn fold<F: WithSmallOrderMulGroup<3>>(
    pk: &FoldingPk<F>,
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingTrace<F>],
) -> FoldingTrace<F> {
    let lifted_trace = batch_traces(dk_domain, traces);

    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    let mut betas = vec![F::ONE; pk.domain.k() as usize];
    let mut beta_pow = F::random(&mut rng);
    for beta in betas.iter_mut() {
        *beta = beta_pow;
        beta_pow *= beta_pow
    }

    let poly_g = compute_poly_g(pk, &betas, &lifted_trace);

    let poly_k = dk_domain.divide_by_vanishing_poly(poly_g.clone());

    let gamma = F::random(&mut rng);

    let poly_k_coeff = dk_domain.extended_to_coeff(poly_k);

    // Final check. Eval G(X), K(X) and Z(X) in \gamma
    let g_in_gamma = dk_domain.eval_extended_lagrange(poly_g, gamma);
    let k_in_gamma = eval_polynomial(&poly_k_coeff, gamma);
    let z_in_gamma = gamma.pow_vartime([dk_domain.n]) - F::ONE;

    assert_eq!(g_in_gamma, k_in_gamma * z_in_gamma);

    fold_traces(dk_domain, traces, &gamma)
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
/// ```ignore
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
        let FoldingTrace {
            fixed_polys,
            advice_polys,
            instance_values,
            lookups,
            permutations: permutation,
            challenges,
            beta,
            gamma,
            theta,
            y,
            ..
        } = &lifted_folding_trace[j];

        let advice_lagrange = advice_polys
            .iter()
            .map(|a| {
                a.iter()
                    .map(|p| pk.domain.coeff_to_lagrange(p.clone()))
                    .collect()
            })
            .collect::<Vec<_>>();

        let witness_poly = pk.ev.evaluate_h::<LagrangeCoeff>(
            &pk.domain,
            &pk.cs,
            &advice_lagrange
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
            lookups,
            permutation,
            &pk.l0,
            &pk.l_last,
            &pk.l_active_row,
            &pk.permutation_pk_cosets,
        );

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
    traces: &[&FoldingTrace<F>],
    gamma: &F,
) -> FoldingTrace<F> {
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

    let buffer = FoldingTrace::init(
        trace_domain_size,
        traces[0].fixed_polys.len(),
        traces[0].advice_polys[0].len(),
        traces[0].instance_polys[0].len(),
        traces[0].lookups[0].len(),
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
            compute_trace, finalise_proof, keygen_pk, keygen_vk_with_k, Advice, Circuit, Column,
            ConstraintSystem, Error, Expression, Selector, TableColumn,
        },
        poly::{
            kzg::{params::ParamsKZG, KZGCommitmentScheme},
            EvaluationDomain, Rotation,
        },
        protogalaxy::prover::{fold, FoldingPk},
        transcript::{CircuitTranscript, Transcript},
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
                let q = meta.query_selector(config.mul_selector);
                vec![q * (a * b - c)]
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
        const K: u32 = 16;
        let k = 4; // number of folding instances

        let rng = ChaCha8Rng::from_seed([0u8; 32]);
        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, rng);

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        let mut rand_bytes = [0u8; 1 << 8];
        rng.fill_bytes(&mut rand_bytes);

        let witnesses = (0..4)
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

        let vk = keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuits[0], K)
            .expect("keygen_vk should not fail");
        let pk = keygen_pk(vk.clone(), &circuits[0]).expect("keygen_pk should not fail");

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

        // Compute traces
        let folding = Instant::now();
        let now = Instant::now();
        let mut transcript = CircuitTranscript::init();

        let traces = circuits
            .into_iter()
            .map(|c| {
                compute_trace(
                    &params,
                    &pk,
                    &[c],
                    #[cfg(feature = "committed-instances")]
                    0,
                    &[&[]],
                    &mut rng,
                    &mut transcript,
                )
                .expect("Failed to compute the folding trace")
                .into_folding_trace(pk.fixed_values.clone())
            })
            .collect::<Vec<_>>();

        let traces_time = now.elapsed().as_millis();

        // We now perform folding of the traces
        let degree = pk.vk.cs.degree() as u32;

        let k_log2_ceil = (k as f64 - 1.).log2() as u32 + 1;
        // We must increase the degree, since we need to count y as a variable.
        // Computing the real degree seems hard.
        let dk_domain = EvaluationDomain::new(degree + 3, k_log2_ceil);
        let folding_pk = FoldingPk::from(pk.clone());
        let folded_trace = fold(
            &folding_pk,
            &dk_domain,
            &[&traces[0], &traces[1], &traces[2], &traces[3]],
        );

        // Now we create the final proof
        let final_pk = folding_pk.into_proving_key(&folded_trace, &vk);
        finalise_proof(
            &params,
            &final_pk,
            #[cfg(feature = "committed-instances")]
            0,
            folded_trace.into(),
            &mut transcript,
        )
        .expect("Failed to finalise proof");

        let folding_time = folding.elapsed().as_millis();

        // Now we see how long it would have taken to produce four normal proofs
        let now = Instant::now();
        let mut finalise_transcript = transcript.clone();

        traces
            .into_iter()
            .try_for_each(|t| {
                finalise_proof(
                    &params,
                    &pk,
                    #[cfg(feature = "committed-instances")]
                    0,
                    t.into(),
                    &mut finalise_transcript,
                )
            })
            .expect("Failed to finalise proofs");

        let full_proof_time = now.elapsed().as_millis();
        println!("Compute four traces      :  {:?}ms", traces_time);
        println!(
            "Compute four full proofs : {:?}ms",
            traces_time + full_proof_time
        );
        println!("Protogalaxy              : {:?}ms", folding_time);
    }
}

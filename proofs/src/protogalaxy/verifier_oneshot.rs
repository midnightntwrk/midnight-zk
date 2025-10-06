//! TODO: We have a lot of duplicated code here. We can simplify this.

use std::{hash::Hash, iter};

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{
        parse_trace,
        traces::{FoldingProverTrace, VerifierFoldingTrace},
        Error, Evaluator, VerifyingKey,
    },
    poly::{
        commitment::PolynomialCommitmentScheme, EvaluationDomain, LagrangeCoeff, Polynomial,
        VerifierQuery,
    },
    protogalaxy::{prover_oneshot::eval_lagrange_on_beta, utils::linear_combination},
    transcript::{read_n, Hashable, Sampleable, Transcript},
    utils::arithmetic::{compute_inner_product, eval_polynomial},
};

/// This verifier can perform a 2**K - 1 to one folding
#[derive(Debug)]
pub struct ProtogalaxyVerifierOneShot<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    const K: usize,
> {
    pub(crate) verifier_folding_trace: VerifierFoldingTrace<F, CS>,
    pub(crate) error_term: F,
    pub(crate) beta: F,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize>
    ProtogalaxyVerifierOneShot<F, CS, K>
{
    /// Fold the given traces. Concretely, the verifier receives [Transcript]s
    /// from [K] proofs, parses them to extract the [VerifierTrace], and
    /// folds them following the protogalaxy protocol.
    /// TODO: We assume that nr of proofs is a power of 2.
    /// TODO: PCS not verified
    pub fn fold<T>(
        vk: &VerifyingKey<F, CS>,
        committed_instances: &[&[CS::Commitment]],
        instances: &[&[&[F]]],
        transcript: &mut T,
    ) -> Result<CS::VerificationGuard, Error>
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
        // We must increase the degree, since we need to count y as a variable.
        // TODO: We'll use independent challenges, instead of powers of y.
        let dk_domain = EvaluationDomain::new(
            vk.cs().degree() as u32 + 3,
            instances.len().trailing_zeros(),
        );

        // TODO: Is this sufficient to check H-consistency? I'm not 'checking' anything,
        // but I'm computing the challenges myself - I believe that is enough.
        // David: yes, i think so too
        let traces = instances
            .iter()
            .zip(committed_instances)
            .map(|(instance, committed_instance)| {
                let trace = parse_trace(vk, &[committed_instance], &[instance], transcript)?;

                Ok(trace.into_folding_trace(vk.fixed_commitments()))
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let beta_pg: F = transcript.squeeze_challenge();

        let _poly_k: CS::Commitment = transcript.read()?;
        let gamma: F = transcript.squeeze_challenge();
        let k_at_gamma: F = transcript.read()?;
        let z_in_gamma: F = gamma.pow_vartime([dk_domain.n]) - F::ONE;

        let error_term: F = z_in_gamma * k_at_gamma;

        let traces = traces.iter().collect::<Vec<_>>();

        println!("Number of traces - verifier: {:?}", traces.len());
        assert!(traces.len().is_power_of_two());

        let nb_committed_instances = committed_instances[0].len();
        let VerifierFoldingTrace {
            advice_commitments,
            fixed_commitments,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            trash_challenge,
            theta,
            y,
        } = fold_traces(&dk_domain, &traces, &gamma);

        let mut final_vk = vk.clone();
        final_vk.fixed_commitments = fixed_commitments.clone();

        let committed_error = transcript.read::<CS::Commitment>()?;

        // For the final verification we are verifying a single proof
        let num_proofs = 1;
        let vanishing = vanishing.read_commitments_after_y(vk, transcript)?;

        // Sample x challenge, which is used to ensure the circuit is
        // satisfied with high probability.
        let x: F = transcript.squeeze_challenge();
        let xn = x.pow_vartime([vk.n()]);

        let instance_evals = {
            let (min_rotation, max_rotation) =
                vk.cs.instance_queries.iter().fold((0, 0), |(min, max), (_, rotation)| {
                    if rotation.0 < min {
                        (rotation.0, max)
                    } else if rotation.0 > max {
                        (min, rotation.0)
                    } else {
                        (min, max)
                    }
                });
            let max_instance_len = instances
                .iter()
                .flat_map(|instance| instance.iter().map(|instance| instance.len()))
                .max_by(Ord::cmp)
                .unwrap_or_default();
            let l_i_s = &vk.get_domain().l_i_range(
                x,
                xn,
                -max_rotation..max_instance_len as i32 + min_rotation.abs(),
            );
            instances
                .iter()
                .map(|instances| {
                    vk.cs
                        .instance_queries
                        .iter()
                        .map(|(column, rotation)| {
                            if column.index() < nb_committed_instances {
                                transcript.read()
                            } else {
                                let instances = instances[column.index() - nb_committed_instances];
                                let offset = (max_rotation - rotation.0) as usize;
                                Ok(compute_inner_product(
                                    instances,
                                    &l_i_s[offset..offset + instances.len()],
                                ))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?
        };

        let advice_evals = (0..num_proofs)
            .map(|_| -> Result<Vec<F>, _> { read_n(transcript, vk.cs.advice_queries.len()) })
            .collect::<Result<Vec<Vec<F>>, _>>()?;
        let fixed_evals: Vec<F> = read_n(transcript, vk.cs.fixed_queries.len())?;
        let correction_eval: F = transcript.read()?;
        let vanishing = vanishing.evaluate_after_x(transcript)?;

        let permutations_common = vk.permutation.evaluate(transcript)?;

        let permutations_evaluated = permutations
            .into_iter()
            .map(|permutation| permutation.evaluate(transcript))
            .collect::<Result<Vec<_>, _>>()?;

        let lookups_evaluated = lookups
            .into_iter()
            .map(|lookups| -> Result<Vec<_>, _> {
                lookups
                    .into_iter()
                    .map(|lookup| lookup.evaluate(transcript))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let trashcans_evaluated = trashcans
            .into_iter()
            .map(|trashcans| -> Result<Vec<_>, _> {
                trashcans
                    .into_iter()
                    .map(|trash| trash.evaluate(transcript))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        // This check ensures the circuit is satisfied so long as the polynomial
        // commitments open to the correct values.
        let vanishing = {
            let blinding_factors = vk.cs.blinding_factors();
            let l_evals = vk.get_domain().l_i_range(x, xn, (-((blinding_factors + 1) as i32))..=0);
            assert_eq!(l_evals.len(), 2 + blinding_factors);
            let l_last = l_evals[0];
            let l_blind: F =
                l_evals[1..(1 + blinding_factors)].iter().fold(F::ZERO, |acc, eval| acc + eval);
            let l_0 = l_evals[1 + blinding_factors];

            // Compute the expected value of h(x)
            let expressions = advice_evals
                .iter()
                .zip(instance_evals.iter())
                .zip(permutations_evaluated.iter())
                .zip(lookups_evaluated.iter())
                .zip(trashcans_evaluated.iter())
                .flat_map(
                    |((((advice_evals, instance_evals), permutation), lookups), trash)| {
                        let challenges = &challenges;
                        let fixed_evals = &fixed_evals;
                        iter::empty()
                            // Evaluate the circuit using the custom gates provided
                            .chain(vk.cs.gates.iter().flat_map(move |gate| {
                                gate.polynomials().iter().map(move |poly| {
                                    poly.evaluate(
                                        &|scalar| scalar,
                                        &|_| {
                                            panic!(
                                                "virtual selectors are removed during optimization"
                                            )
                                        },
                                        &|query| fixed_evals[query.index.unwrap()],
                                        &|query| advice_evals[query.index.unwrap()],
                                        &|query| instance_evals[query.index.unwrap()],
                                        &|challenge| challenges[challenge.index()],
                                        &|a| -a,
                                        &|a, b| a + &b,
                                        &|a, b| a * &b,
                                        &|a, scalar| a * &scalar,
                                    )
                                })
                            }))
                            .chain(permutation.expressions(
                                vk,
                                &vk.cs.permutation,
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
                            ))
                            .chain(lookups.iter().zip(vk.cs.lookups.iter()).flat_map({
                                let theta = theta.clone();
                                move |(p, argument)| {
                                    p.expressions(
                                        l_0,
                                        l_last,
                                        l_blind,
                                        argument,
                                        &theta,
                                        beta,
                                        gamma,
                                        advice_evals,
                                        fixed_evals,
                                        instance_evals,
                                        challenges,
                                    )
                                }
                            }))
                            .chain(trash.iter().zip(vk.cs.trashcans.iter()).flat_map(
                                move |(p, argument)| {
                                    p.expressions(
                                        argument,
                                        trash_challenge,
                                        advice_evals,
                                        fixed_evals,
                                        instance_evals,
                                        challenges,
                                    )
                                },
                            ))
                    },
                );

            assert_eq!(y.len(), 1);
            // let flattened_y = y.into_iter().flatten().collect::<Vec<_>>();
            vanishing.verify_corrected(expressions, y[0].clone(), correction_eval, xn)
        };

        let queries = committed_instances
            .iter()
            .zip(instance_evals.iter())
            .zip(advice_commitments.iter())
            .zip(advice_evals.iter())
            .zip(permutations_evaluated.iter())
            .zip(lookups_evaluated.iter())
            .zip(trashcans_evaluated.iter())
            .flat_map(
                |(
                    (
                        (
                            (
                                ((committed_instances, instance_evals), advice_commitments),
                                advice_evals,
                            ),
                            permutation,
                        ),
                        lookups,
                    ),
                    trash,
                )| {
                    iter::empty()
                        .chain(vk.cs.instance_queries.iter().enumerate().filter_map(
                            move |(query_index, &(column, at))| {
                                if column.index() < nb_committed_instances {
                                    Some(VerifierQuery::new(
                                        vk.get_domain().rotate_omega(x, at),
                                        &committed_instances[column.index()],
                                        instance_evals[query_index],
                                    ))
                                } else {
                                    None
                                }
                            },
                        ))
                        .chain(vk.cs.advice_queries.iter().enumerate().map(
                            move |(query_index, &(column, at))| {
                                VerifierQuery::new(
                                    vk.get_domain().rotate_omega(x, at),
                                    &advice_commitments[column.index()],
                                    advice_evals[query_index],
                                )
                            },
                        ))
                        .chain(permutation.queries(vk, x))
                        .chain(lookups.iter().flat_map(move |p| p.queries(vk, x)))
                        .chain(trash.iter().flat_map(move |p| p.queries(x)))
                },
            )
            .chain(
                vk.cs.fixed_queries.iter().enumerate().map(|(query_index, &(column, at))| {
                    VerifierQuery::new(
                        vk.get_domain().rotate_omega(x, at),
                        &vk.fixed_commitments[column.index()],
                        fixed_evals[query_index],
                    )
                }),
            )
            .chain(permutations_common.queries(&vk.permutation, x))
            .chain(vanishing.queries(x, vk.n()))
            .chain(iter::once(VerifierQuery::new(
                x,
                &committed_error,
                correction_eval,
            )))
            .chain(iter::once(VerifierQuery::new(
                beta_pg,
                &committed_error,
                error_term,
            )))
            .collect::<Vec<_>>();

        // We are now convinced the circuit is satisfied so long as the
        // polynomial commitments open to the correct values.
        CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
    }

    /// This function verifies that a folde trace satisfies the relaxed
    /// relation.
    // TODO: need to verify that the commitment is correct as well.
    #[allow(clippy::too_many_arguments)]
    pub fn is_sat(
        &self,
        params: &CS::Parameters,
        vk: &VerifyingKey<F, CS>,
        evaluator: &Evaluator<F>,
        folded_witness: FoldingProverTrace<F>,
        l0: &Polynomial<F, LagrangeCoeff>,
        l_last: &Polynomial<F, LagrangeCoeff>,
        l_active_row: &Polynomial<F, LagrangeCoeff>,
        permutation_pk_cosets: &[Polynomial<F, LagrangeCoeff>],
    ) -> Result<(), Error> {
        // First we check that the committed folded witness corresponds to the folded
        // instance
        let committed_folded_witness = folded_witness.commit(params);

        assert_eq!(committed_folded_witness, self.verifier_folding_trace);

        // Next, we evaluate the f_i function over the folded trace, to see it
        // corresponds with the computed error.
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
            trash_challenge,
            y,
            ..
        } = folded_witness;

        let witness_poly = evaluator.evaluate_h::<LagrangeCoeff>(
            vk.get_domain(),
            vk.cs(),
            &advice_polys.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &instance_values.iter().map(|i| i.as_slice()).collect::<Vec<_>>(),
            &fixed_polys,
            &challenges,
            &y,
            beta,
            gamma,
            &theta,
            trash_challenge,
            &lookups,
            &trashcans,
            &permutation,
            l0,
            l_last,
            l_active_row,
            permutation_pk_cosets,
        );

        // let beta_coeffs: Vec<F> = vec![self.beta.clone(); 1 << K];
        let beta_coeffs: Vec<F> = eval_lagrange_on_beta(vk.get_domain(), &self.beta);

        let expected_result = witness_poly
            .values
            .into_par_iter()
            .zip(beta_coeffs.par_iter())
            .map(|(witness, beta_coeffs)| witness * beta_coeffs)
            .reduce(|| F::ZERO, |a, b| a + b);

        if expected_result == self.error_term {
            Ok(())
        } else {
            Err(Error::Opening)
        }
    }
}

/// Function to fold traces over an evaluation `\gamma`
fn fold_traces<F: WithSmallOrderMulGroup<3>, PCS: PolynomialCommitmentScheme<F>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&VerifierFoldingTrace<F, PCS>],
    gamma: &F,
) -> VerifierFoldingTrace<F, PCS> {
    let lagrange_polys = (0..traces.len())
        .map(|i| {
            // For the moment we only support batching of traces of dimension one.
            assert_eq!(traces[i].advice_commitments.len(), 1);
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            l
        })
        .map(|p| dk_domain.lagrange_to_coeff(p))
        .collect::<Vec<_>>();

    let buffer = VerifierFoldingTrace::init(
        traces[0].fixed_commitments.len(),
        traces[0].advice_commitments[0].len(),
        traces[0].lookups[0].len(),
        traces[0].trashcans[0].len(),
        traces[0].permutations[0].permutation_product_commitments.len(),
        traces[0].challenges.len(),
        traces[0].theta.len(),
        traces[0].y[0].len(),
    );
    let lagranges_in_gamma = lagrange_polys
        .iter()
        .map(|poly| eval_polynomial(poly, *gamma))
        .collect::<Vec<_>>();

    linear_combination(buffer, traces, &lagranges_in_gamma)
}

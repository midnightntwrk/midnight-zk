use std::{hash::Hash, iter};

use ff::{FromUniformBytes, WithSmallOrderMulGroup};

use super::{vanishing, Error, VerifyingKey};
use crate::{
    plonk::traces::VerifierTrace,
    poly::{commitment::PolynomialCommitmentScheme, VerifierQuery},
    transcript::{read_n, Hashable, Sampleable, Transcript},
    utils::arithmetic::compute_inner_product,
};

/// Given a plonk proof, this function parses it to extract the verifying trace.
/// This function computes all Fiat-Shamir challenges, with the exception of
/// `x`, which is computed in [verify_algebraic_constraints]
pub fn parse_trace<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<VerifierTrace<F, CS>, Error>
where
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
{
    #[cfg(not(feature = "committed-instances"))]
    let committed_instances: Vec<Vec<CS::Commitment>> = vec![vec![]; instances.len()];

    let nb_committed_instances = committed_instances[0].len();
    for committed_instances in committed_instances.iter() {
        if committed_instances.len() != nb_committed_instances {
            println!(
                "Here? with {} and {nb_committed_instances}",
                committed_instances.len()
            );
            return Err(Error::InvalidInstances);
        }
    }

    // Check that instances matches the expected number of instance columns
    for (committed_instances, instances) in committed_instances.iter().zip(instances.iter()) {
        if committed_instances.len() + instances.len() != vk.cs.num_instance_columns {
            println!("Or here");
            return Err(Error::InvalidInstances);
        }
    }

    let num_proofs = instances.len();

    // Hash verification key into transcript
    vk.hash_into(transcript)?;

    for committed_instances in committed_instances.iter() {
        for commitment in committed_instances.iter() {
            transcript.common(commitment)?
        }
    }
    for instance in instances.iter() {
        for instance in instance.iter() {
            transcript.common(&F::from_u128(instance.len() as u128))?;
            for value in instance.iter() {
                transcript.common(value)?;
            }
        }
    }

    // Hash the prover's advice commitments into the transcript and squeeze
    // challenges
    let (advice_commitments, challenges) = {
        let mut advice_commitments =
            vec![vec![CS::Commitment::default(); vk.cs.num_advice_columns]; num_proofs];
        let mut challenges = vec![F::ZERO; vk.cs.num_challenges];

        for current_phase in vk.cs.phases() {
            for advice_commitments in advice_commitments.iter_mut() {
                for (phase, commitment) in
                    vk.cs.advice_column_phase.iter().zip(advice_commitments.iter_mut())
                {
                    if current_phase == *phase {
                        *commitment = transcript.read()?;
                    }
                }
            }
            for (phase, challenge) in vk.cs.challenge_phase.iter().zip(challenges.iter_mut()) {
                if current_phase == *phase {
                    *challenge = transcript.squeeze_challenge();
                }
            }
        }

        (advice_commitments, challenges)
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    // We also need to get as many theta as we would use powers, to avoid increasing
    // the degree of the identity. We need max of lookup.input_expressions =
    // lookup.table_expressions len Do check that they are equal
    let nb_theta = vk
        .cs
        .lookups
        .iter()
        .map(|l| {
            assert_eq!(l.input_expressions.len(), l.table_expressions.len());
            l.input_expressions.len()
        })
        .max()
        .unwrap_or(1);

    // let theta: F = transcript.squeeze_challenge();
    let theta: Vec<F> = (0..nb_theta).map(|_| transcript.squeeze_challenge()).collect();

    let lookups_permuted = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            // Hash each lookup permuted commitment
            vk.cs
                .lookups
                .iter()
                .map(|argument| argument.read_permuted_commitments(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    let permutations_committed = (0..num_proofs)
        .map(|_| {
            // Hash each permutation product commitment
            vk.cs.permutation.read_product_commitments(vk, transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lookups_committed = lookups_permuted
        .into_iter()
        .map(|lookups| {
            // Hash each lookup product commitment
            lookups
                .into_iter()
                .map(|lookup| lookup.read_product_commitment(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let trash_challenge: F = transcript.squeeze_challenge();

    let trashcans_committed = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            vk.cs
                .trashcans
                .iter()
                .map(|argument| argument.read_committed::<CS, _>(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let vanishing = vanishing::Argument::read_commitments_before_y(transcript)?;

    // To avoid increasing the degree in folding, we need to sample one commit for
    // each expression that we batch (instead of using powers).
    let mut nb_y = 0;

    // We need one challenge per polynomial, per gate.
    vk.cs.gates.iter().for_each(|g| nb_y += g.polynomials().len());

    // We need two for the permutation argument (1 for the first, 1 for the last),
    // sets.len() - 1 for linking each column, and sets.len() for the product rule
    nb_y += 2;
    nb_y += permutations_committed[0].permutation_product_commitments.len() - 1;
    nb_y += permutations_committed[0].permutation_product_commitments.len();

    // We need five for each lookup argument
    nb_y += lookups_committed[0].len() * 5;

    // let y: F = transcript.squeeze_challenge();
    // let y: Vec<F> = vec![y; nb_y];
    let y: Vec<F> = (0..nb_y).map(|_| transcript.squeeze_challenge()).collect();

    Ok(VerifierTrace {
        advice_commitments,
        vanishing,
        lookups: lookups_committed,
        trashcans: trashcans_committed,
        permutations: permutations_committed,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    })
}

/// Given a VerifierTrace, this function computes the opening challenge, x,
/// and proceeds to verify the algebraic constraints with the claimed
/// evaluations. This function does not verify the PCS proof.
///
/// The verifier will error if there are trailing bits in the transcript.
pub fn verify_algebraic_constraints<F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    vk: &VerifyingKey<F, CS>,
    trace: VerifierTrace<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
    correction: &(CS::Commitment, F, F),
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
{
    #[cfg(not(feature = "committed-instances"))]
    let committed_instances: Vec<Vec<CS::Commitment>> = vec![vec![]; instances.len()];
    let nb_committed_instances = committed_instances[0].len();
    let num_proofs = instances.len();

    let VerifierTrace {
        advice_commitments,
        vanishing,
        lookups,
        trashcans,
        permutations,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    } = trace;

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
        let l_i_s = &vk.domain.l_i_range(
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
        let l_evals = vk.domain.l_i_range(x, xn, (-((blinding_factors + 1) as i32))..=0);
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
                                        panic!("virtual selectors are removed during optimization")
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

        vanishing.verify(expressions, y, correction_eval, xn)
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
                        (((committed_instances, instance_evals), advice_commitments), advice_evals),
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
                                    vk.domain.rotate_omega(x, at),
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
                                vk.domain.rotate_omega(x, at),
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
                    vk.domain.rotate_omega(x, at),
                    &vk.fixed_commitments[column.index()],
                    fixed_evals[query_index],
                )
            }),
        )
        .chain(permutations_common.queries(&vk.permutation, x))
        .chain(vanishing.queries(x, vk.n()))
        .chain(iter::once(VerifierQuery::new(
            x,
            &correction.0,
            correction_eval,
        )))
        .chain(iter::once(VerifierQuery::new(
            correction.1,
            &correction.0,
            correction.2,
        )))
        .collect::<Vec<_>>();

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.
    CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
}

/// Prepares a plonk proof into a PCS instance that can be finalized or
/// batched. It is responsibility of the verifier to check the validity of the
/// instance columns.
///
/// The verifier will error if there are trailing bytes in the transcript.
pub fn prepare<F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    vk: &VerifyingKey<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
{
    let trace = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        committed_instances,
        instances,
        transcript,
    )
    .unwrap();

    Ok(verify_algebraic_constraints(
        vk,
        trace,
        #[cfg(feature = "committed-instances")]
        committed_instances,
        instances,
        // TODO: is this always the identity?
        &(CS::Commitment::default(), F::ZERO, F::ZERO),
        transcript,
    )
    .unwrap())
}

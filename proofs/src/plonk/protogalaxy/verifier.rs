use std::{hash::Hash, iter};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{
        linearization::verifier::compute_linearization_commitment,
        logup, partially_evaluate_identities, permutation, trash,
        traces::VerifierTrace,
        verifier::parse_trace,
        Error, VerifyingKey,
    },
    poly::{
        commitment::{Labelable, PolynomialCommitmentScheme},
        EvaluationDomain, PolynomialLabel, VerifierQuery,
    },
    transcript::{read_n, Hashable, Sampleable, Transcript},
    utils::arithmetic::{compute_inner_product, eval_polynomial},
};

/// A verifier-side folding trace: all polynomial commitments plus challenges.
struct VerifierFoldingTrace<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    advice_commitments: Vec<CS::Commitment>,
    instance_polys: Vec<Vec<F>>,
    lookup_mult_commitments: Vec<CS::Commitment>,
    lookup_helper_commitments: Vec<Vec<CS::Commitment>>,
    lookup_agg_commitments: Vec<CS::Commitment>,
    trash_commitments: Vec<CS::Commitment>,
    perm_commitments: Vec<CS::Commitment>,
    beta: F,
    gamma: F,
    theta: Vec<F>,
    trash_challenge: F,
    y: Vec<F>,
}

/// Extract a `VerifierFoldingTrace` from a standard `VerifierTrace`.
fn into_verifier_folding_trace<F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    trace: VerifierTrace<F, CS>,
    instance_polys: Vec<Vec<F>>,
) -> VerifierFoldingTrace<F, CS> {
    let lookup_parts: Vec<_> =
        trace.lookups.into_iter().map(|l| l.into_parts()).collect();
    let lookup_mult_commitments = lookup_parts.iter().map(|(m, _, _)| m.clone()).collect();
    let lookup_helper_commitments = lookup_parts.iter().map(|(_, h, _)| h.clone()).collect();
    let lookup_agg_commitments = lookup_parts.into_iter().map(|(_, _, a)| a).collect();
    let trash_commitments: Vec<CS::Commitment> =
        trace.trashcans.into_iter().map(|t| t.into_commitment()).collect();
    let perm_commitments = trace.permutations.into_commitments();

    VerifierFoldingTrace {
        advice_commitments: trace.advice_commitments,
        instance_polys,
        lookup_mult_commitments,
        lookup_helper_commitments,
        lookup_agg_commitments,
        trash_commitments,
        perm_commitments,
        beta: trace.beta,
        gamma: trace.gamma,
        theta: trace.theta,
        trash_challenge: trace.trash_challenge,
        y: trace.y,
    }
}

/// Fold a slice of verifier traces via Lagrange combination at `gamma`.
fn fold_verifier_traces<F, CS>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[VerifierFoldingTrace<F, CS>],
    gamma: &F,
) -> VerifierFoldingTrace<F, CS>
where
    F: PrimeField + WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Clone
        + std::ops::Add<CS::Commitment, Output = CS::Commitment>
        + std::ops::Mul<F, Output = CS::Commitment>
        + Default,
{
    let k = traces.len();

    // Compute L_i(gamma) for each i using Lagrange basis polynomials over dk_domain.
    let lagrange_at_gamma: Vec<F> = (0..k)
        .map(|i| {
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            let coeff = dk_domain.lagrange_to_coeff(l);
            eval_polynomial(&coeff.values, *gamma)
        })
        .collect();

    // Linear combination of all commitment vectors.
    let lc_commits = |get: &dyn Fn(&VerifierFoldingTrace<F, CS>) -> Vec<CS::Commitment>| {
        let first = get(&traces[0]);
        (0..first.len())
            .map(|j| {
                traces
                    .iter()
                    .zip(lagrange_at_gamma.iter())
                    .fold(CS::Commitment::default(), |acc, (t, &li)| {
                        acc + (get(t)[j].clone() * li)
                    })
            })
            .collect::<Vec<_>>()
    };

    let advice_commitments = lc_commits(&|t| t.advice_commitments.clone());
    let lookup_mult_commitments = lc_commits(&|t| t.lookup_mult_commitments.clone());
    let lookup_agg_commitments = lc_commits(&|t| t.lookup_agg_commitments.clone());
    let trash_commitments = lc_commits(&|t| t.trash_commitments.clone());
    let perm_commitments = lc_commits(&|t| t.perm_commitments.clone());

    // Helper commitments: each lookup may have multiple helpers.
    let lookup_helper_commitments: Vec<Vec<CS::Commitment>> = if traces[0]
        .lookup_helper_commitments
        .is_empty()
    {
        vec![]
    } else {
        (0..traces[0].lookup_helper_commitments.len())
            .map(|i| {
                let n_helpers = traces[0].lookup_helper_commitments[i].len();
                (0..n_helpers)
                    .map(|j| {
                        traces
                            .iter()
                            .zip(lagrange_at_gamma.iter())
                            .fold(CS::Commitment::default(), |acc, (t, &li)| {
                                acc + (t.lookup_helper_commitments[i][j].clone() * li)
                            })
                    })
                    .collect()
            })
            .collect()
    };

    // Linear combination of instance polys and scalar challenges.
    let instance_polys: Vec<Vec<F>> = if traces[0].instance_polys.is_empty() {
        vec![]
    } else {
        (0..traces[0].instance_polys.len())
            .map(|i| {
                let len = traces[0].instance_polys[i].len();
                (0..len)
                    .map(|j| {
                        traces
                            .iter()
                            .zip(lagrange_at_gamma.iter())
                            .map(|(t, &li)| t.instance_polys[i][j] * li)
                            .sum()
                    })
                    .collect()
            })
            .collect()
    };

    let lc_scalar = |get: &dyn Fn(&VerifierFoldingTrace<F, CS>) -> F| -> F {
        traces
            .iter()
            .zip(lagrange_at_gamma.iter())
            .map(|(t, &li)| get(t) * li)
            .sum()
    };
    let lc_vec = |get: &dyn Fn(&VerifierFoldingTrace<F, CS>) -> Vec<F>| -> Vec<F> {
        let len = get(&traces[0]).len();
        (0..len)
            .map(|i| {
                traces
                    .iter()
                    .zip(lagrange_at_gamma.iter())
                    .map(|(t, &li)| get(t)[i] * li)
                    .sum()
            })
            .collect()
    };

    VerifierFoldingTrace {
        advice_commitments,
        instance_polys,
        lookup_mult_commitments,
        lookup_helper_commitments,
        lookup_agg_commitments,
        trash_commitments,
        perm_commitments,
        beta: lc_scalar(&|t| t.beta),
        gamma: lc_scalar(&|t| t.gamma),
        theta: lc_vec(&|t| t.theta.clone()),
        trash_challenge: lc_scalar(&|t| t.trash_challenge),
        y: lc_vec(&|t| t.y.clone()),
    }
}

/// Protogalaxy verifier: folds `NB_FOLDED` instances and verifies the accumulator.
#[derive(Debug)]
pub struct ProtogalaxyVerifier<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    const NB_FOLDED: usize,
> {
    _phantom: std::marker::PhantomData<(F, CS)>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const NB_FOLDED: usize>
    ProtogalaxyVerifier<F, CS, NB_FOLDED>
{
    /// Verify a protogalaxy folded proof, returning a `VerificationGuard`.
    pub fn fold<T>(
        vk: &VerifyingKey<F, CS>,
        instances: &[&[&[F]]],
        transcript: &mut T,
    ) -> Result<CS::VerificationGuard, Error>
    where
        T: Transcript,
        CS::Commitment: Hashable<T::Hash>
            + Clone
            + Default
            + std::ops::Add<CS::Commitment, Output = CS::Commitment>
            + std::ops::Mul<F, Output = CS::Commitment>,
        F: WithSmallOrderMulGroup<3>
            + Sampleable<T::Hash>
            + Hashable<T::Hash>
            + Hash
            + Ord
            + FromUniformBytes<64>,
    {
        assert_eq!(instances.len(), NB_FOLDED);
        assert!(NB_FOLDED.is_power_of_two());

        let domain = vk.get_domain();
        let folding_degree = vk.cs.degree() as u32;
        let dk_domain = EvaluationDomain::new(folding_degree, NB_FOLDED.trailing_zeros());

        // ── Step 1: parse k standard PLONK verifier traces ───────────────────
        let verifier_traces: Vec<VerifierTrace<F, CS>> = instances
            .iter()
            .map(|inst| parse_trace(
                vk,
                #[cfg(feature = "committed-instances")] &[],
                inst,
                transcript,
            ))
            .collect::<Result<Vec<_>, _>>()?;

        let folding_traces: Vec<VerifierFoldingTrace<F, CS>> = verifier_traces
            .into_iter()
            .zip(instances.iter())
            .map(|(trace, inst)| {
                let instance_polys: Vec<Vec<F>> = inst.iter().map(|col| col.to_vec()).collect();
                into_verifier_folding_trace(trace, instance_polys)
            })
            .collect();

        // ── Step 2: protogalaxy challenges ────────────────────────────────────
        let beta_pg: F = transcript.squeeze_challenge();
        let _k_commitment: CS::Commitment = transcript.read()?;
        let folding_gamma: F = transcript.squeeze_challenge();
        let k_at_gamma: F = transcript.read()?;

        // Compute error term from K(gamma) * Z_dk(gamma).
        let z_dk_at_gamma = folding_gamma.pow([dk_domain.n]) - F::ONE;
        let _error_term = z_dk_at_gamma * k_at_gamma;

        // ── Step 3: fold verifier traces ──────────────────────────────────────
        let folded =
            fold_verifier_traces(&dk_domain, &folding_traces, &folding_gamma);

        // ── Step 4: read error commitment ─────────────────────────────────────
        let error_commitment: CS::Commitment = transcript.read()?;

        // ── Step 5: run final plonk verification with folded commitments ──────
        verify_folded(
            vk,
            &folded,
            beta_pg,
            error_commitment,
            &dk_domain,
            folding_gamma,
            k_at_gamma,
            transcript,
        )
    }
}

/// Run the final PLONK verification with folded commitments and error correction.
#[allow(clippy::too_many_arguments)]
fn verify_folded<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    folded: &VerifierFoldingTrace<F, CS>,
    beta_pg: F,
    error_commitment: CS::Commitment,
    dk_domain: &EvaluationDomain<F>,
    folding_gamma: F,
    k_at_gamma: F,
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    CS::Commitment: Hashable<T::Hash>
        + Clone
        + Default
        + std::ops::Add<CS::Commitment, Output = CS::Commitment>
        + std::ops::Mul<F, Output = CS::Commitment>,
{
    // Read quotient commitments (h limbs).
    #[cfg(not(feature = "single-h-commitment"))]
    let nb_quotient_coms = vk.domain.get_quotient_poly_degree();
    #[cfg(feature = "single-h-commitment")]
    let nb_quotient_coms = 1;
    let quotient_limb_coms: Vec<CS::Commitment> = read_n(transcript, nb_quotient_coms)?;

    let x: F = transcript.squeeze_challenge();

    let splitting_factor = x.pow_vartime([vk.n() - 1]);
    let xn = splitting_factor * x;

    // ── Compute instance evals from folded instance polys ─────────────────────
    let instance_evals: Vec<F> = {
        let (min_rotation, max_rotation) =
            vk.cs.instance_queries.iter().fold((0, 0), |(mn, mx), (_, r)| {
                (mn.min(r.0), mx.max(r.0))
            });
        let max_len = folded
            .instance_polys
            .iter()
            .map(|col| col.len())
            .max()
            .unwrap_or(0);
        let l_i_s = &vk.domain.l_i_range(
            x,
            xn,
            -max_rotation..max_len as i32 + min_rotation.abs(),
        );
        vk.cs
            .instance_queries
            .iter()
            .map(|(col, rot)| {
                let instance = &folded.instance_polys[col.index()];
                let offset = (max_rotation - rot.0) as usize;
                Ok(compute_inner_product(instance, &l_i_s[offset..offset + instance.len()]))
            })
            .collect::<Result<Vec<_>, Error>>()?
    };

    let advice_evals: Vec<F> = read_n(transcript, vk.cs.advice_queries.len())?;
    let mut fixed_evals = read_n(
        transcript,
        vk.cs.fixed_queries().len() - vk.cs.num_simple_selectors(),
    )?;
    for (idx, (col, _)) in vk.cs.fixed_queries().iter().enumerate() {
        if vk.cs.has_simple_selector_col(col.index()) {
            fixed_evals.insert(idx, F::ONE);
        }
    }

    // Error eval at x (written by prover).
    let error_at_x: F = transcript.read()?;

    let permutations_common = vk.permutation.evaluate(transcript)?;

    // ── Reconstruct evaluated permutation/lookup/trash from folded commitments ─
    let perm_committed = permutation::verifier::Committed::<F, CS>::from_commitments(
        folded.perm_commitments.clone(),
    );
    let permutations_evaluated = perm_committed.evaluate(transcript)?;

    let lookups_evaluated: Vec<_> = folded
        .lookup_mult_commitments
        .iter()
        .zip(folded.lookup_helper_commitments.iter())
        .zip(folded.lookup_agg_commitments.iter())
        .map(|((mult, helpers), agg)| {
            let committed = logup::verifier::Committed::from_parts(
                mult.clone(),
                helpers.clone(),
                agg.clone(),
            );
            committed.evaluate(transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let trashcans_evaluated: Vec<_> = folded
        .trash_commitments
        .iter()
        .map(|tcom| {
            let committed = trash::verifier::Committed::from_commitment(tcom.clone());
            committed.evaluate(transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let expressions = partially_evaluate_identities(
        vk,
        &fixed_evals,
        &instance_evals,
        &advice_evals,
        &permutations_evaluated.sets,
        lookups_evaluated.iter().map(|inner| &inner.evaluated),
        trashcans_evaluated.iter().map(|inner| &inner.evaluated),
        &permutations_common,
        x,
        xn,
        folded.beta,
        folded.gamma,
        &folded.theta,
        folded.trash_challenge,
    );

    let mut lin_com = compute_linearization_commitment(
        expressions,
        vk,
        x,
        &folded.y,
        &xn,
        &splitting_factor,
        &quotient_limb_coms,
    );
    // In protogalaxy, h(X)*Z_n(X) = nu(X) - E(X), so L(x) = expected + E(x).
    lin_com.1 += error_at_x;

    // ── Build verifier queries (must match compute_queries order in prover) ───
    // Order: advice, perm-products, lookups, trash, fixed, perm-sigmas, lin,
    //        error@x, error@beta_pg.
    let e_at_beta_pg = folding_gamma.pow([dk_domain.n]) - F::ONE;
    let e_at_beta_pg = e_at_beta_pg * k_at_gamma;
    let error_commitment =
        error_commitment.label(PolynomialLabel::Custom("protogalaxy_error".into()));
    let queries: Vec<VerifierQuery<F, CS>> = iter::empty()
        .chain(
            vk.cs
                .advice_queries
                .iter()
                .enumerate()
                .map(|(qi, &(col, at))| {
                    VerifierQuery::new(
                        vk.domain.rotate_omega(x, at),
                        &folded.advice_commitments[col.index()],
                        advice_evals[qi],
                    )
                }),
        )
        .chain(permutations_evaluated.queries(vk, x))
        .chain(lookups_evaluated.iter().flat_map(|p| p.queries(vk, x)))
        .chain(trashcans_evaluated.iter().flat_map(|p| p.queries(x)))
        .chain(
            vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                .filter(|(_, (col, _))| !vk.cs.has_simple_selector_col(col.index()))
                .map(|(qi, &(col, at))| {
                    VerifierQuery::new(
                        vk.domain.rotate_omega(x, at),
                        &vk.fixed_commitments[col.index()],
                        fixed_evals[qi],
                    )
                }),
        )
        .chain(permutations_common.queries(&vk.permutation, x))
        .chain(iter::once(VerifierQuery::new(x, &lin_com.0, lin_com.1)))
        .chain(iter::once(VerifierQuery::new(x, &error_commitment, error_at_x)))
        .chain(iter::once(VerifierQuery::new(beta_pg, &error_commitment, e_at_beta_pg)))
        .collect();

    CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
}

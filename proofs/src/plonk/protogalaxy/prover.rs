use std::{hash::Hash, marker::PhantomData, time::Instant};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use crate::{
    plonk::{
        compute_h_poly, compute_nu_poly, compute_queries, logup, partially_evaluate_identities,
        permutation, trash, write_evals_to_transcript, Circuit, Error, ProvingKey,
    },
    plonk::{
        linearization::prover::compute_linearization_poly,
        protogalaxy::utils::{
            batch_traces, eval_lagrange_on_beta, fold_traces, FoldingLogupTrace,
            FoldingProverTrace,
        },
        prover::compute_raw_trace,
        traces::ProverTrace,
    },
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, EvaluationDomain, ExtendedLagrangeCoeff,
        LagrangeCoeff, Polynomial, PolynomialLabel, ProverQuery,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// Protogalaxy prover: folds `NB_FOLDED` instances into a single accumulator.
#[derive(Debug)]
pub struct ProtogalaxyProver<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    const NB_FOLDED: usize,
> {
    _phantom: PhantomData<(F, CS)>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const NB_FOLDED: usize>
    ProtogalaxyProver<F, CS, NB_FOLDED>
{
    /// Fold `NB_FOLDED` circuit instances into one accumulator.
    ///
    /// Each circuit in `circuits` is proved using `compute_trace` and then all
    /// traces are folded via the protogalaxy protocol. A final corrected plonk
    /// proof is written to `transcript`.
    pub fn fold<C, T>(
        params: &CS::Parameters,
        pk: ProvingKey<F, CS>,
        circuits: Vec<C>,
        instances: &[&[&[F]]],
        mut rng: impl CryptoRng + RngCore,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        C: Circuit<F>,
        T: Transcript,
        CS::Commitment: Hashable<T::Hash>,
        F: WithSmallOrderMulGroup<3>
            + Sampleable<T::Hash>
            + Hashable<T::Hash>
            + Hash
            + Ord
            + FromUniformBytes<64>,
    {
        assert_eq!(circuits.len(), NB_FOLDED);
        assert_eq!(instances.len(), NB_FOLDED);
        assert!(NB_FOLDED.is_power_of_two());

        let domain = pk.vk.get_domain();

        // ── Step 1: compute k standard PLONK traces (advice stays Lagrange) ──
        let t0 = Instant::now();
        let folding_traces: Vec<FoldingProverTrace<F>> = circuits
            .into_iter()
            .zip(instances.iter())
            .map(|(circuit, inst)| -> Result<FoldingProverTrace<F>, Error> {
                let raw = compute_raw_trace(
                    params,
                    &pk,
                    &circuit,
                    #[cfg(feature = "committed-instances")] 0,
                    inst,
                    transcript,
                    &mut rng,
                )?;
                Ok(FoldingProverTrace {
                    advice_polys: raw.advice_lagrange,
                    instance_polys: raw.instance_values,
                    lookups: raw.lookups.into_iter().map(|l| FoldingLogupTrace {
                        multiplicities: l.multiplicities,
                        helper_polys: l.helper_polys,
                        aggregator_poly: l.aggregator_poly,
                    }).collect(),
                    trash_polys: raw.trashcans.into_iter().map(|t| t.trash_poly).collect(),
                    perm_polys: raw.permutations.sets.into_iter()
                        .map(|s| s.permutation_product_poly).collect(),
                    beta: raw.beta,
                    gamma: raw.gamma,
                    theta: raw.theta,
                    trash_challenge: raw.trash_challenge,
                    y: raw.y,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let traces_refs: Vec<&FoldingProverTrace<F>> = folding_traces.iter().collect();
        eprintln!("[protogalaxy] step1 compute_traces:     {:>8.2?}", t0.elapsed());

        // ── Step 2: protogalaxy challenges ────────────────────────────────────
        let beta_pg: F = transcript.squeeze_challenge();

        // ── Step 3: precompute Lagrange-form proving-key data ─────────────────
        let l0_lag = domain.extended_to_lagrange(pk.l0.clone());
        let l_last_lag = domain.extended_to_lagrange(pk.l_last.clone());
        let l_active_lag = domain.extended_to_lagrange(pk.l_active_row.clone());
        let perm_pk_lag: Vec<Polynomial<F, LagrangeCoeff>> = pk
            .permutation
            .polys
            .iter()
            .map(|p| domain.coeff_to_lagrange(p.clone()))
            .collect();

        let beta_coeffs = eval_lagrange_on_beta(domain, &beta_pg);

        // ── Step 4: set up the dk-domain ──────────────────────────────────────
        let folding_degree = pk.vk.cs.degree() as u32;
        let dk_domain = EvaluationDomain::new(folding_degree, NB_FOLDED.trailing_zeros());
        let dk_ext_len = dk_domain.extended_len();

        // ── Step 5: batch traces over dk-domain ───────────────────────────────
        let t1 = Instant::now();
        let lifted = batch_traces(&dk_domain, &traces_refs);
        eprintln!("[protogalaxy] step5 batch_traces:        {:>8.2?}", t1.elapsed());

        // ── Step 6: evaluate circuit identity at each extended dk-point ───────
        let t2 = Instant::now();
        // g_poly[t] = G(x_t) = ⟨nu_t, beta_coeffs⟩
        let mut g_poly = vec![F::ZERO; dk_ext_len];

        for (t, trace_t) in lifted.iter().enumerate() {
            let logup_committed: Vec<logup::prover::Committed<F>> = trace_t
                .lookups
                .iter()
                .map(|l| logup::prover::Committed {
                    multiplicities: l.multiplicities.clone(),
                    helper_polys: l.helper_polys.clone(),
                    aggregator_poly: l.aggregator_poly.clone(),
                })
                .collect();
            let trash_committed: Vec<trash::prover::Committed<F>> = trace_t
                .trash_polys
                .iter()
                .map(|p| trash::prover::Committed { trash_poly: p.clone() })
                .collect();
            let perm_committed = permutation::prover::Committed {
                sets: trace_t
                    .perm_polys
                    .iter()
                    .map(|p| permutation::prover::CommittedSet {
                        permutation_product_poly: p.clone(),
                    })
                    .collect(),
            };

            let nu_t: Polynomial<F, LagrangeCoeff> = pk.ev.evaluate_numerator(
                domain,
                &pk.vk.cs,
                &trace_t.advice_polys,
                &trace_t.instance_polys,
                &pk.fixed_values,
                &trace_t.y,
                trace_t.beta,
                trace_t.gamma,
                &trace_t.theta,
                trace_t.trash_challenge,
                &logup_committed,
                &trash_committed,
                &perm_committed,
                &l0_lag,
                &l_last_lag,
                &l_active_lag,
                &perm_pk_lag,
            );

            g_poly[t] = nu_t
                .values
                .iter()
                .zip(beta_coeffs.iter())
                .map(|(v, b)| *v * b)
                .sum();
        }

        eprintln!("[protogalaxy] step6 eval_G_poly:         {:>8.2?}", t2.elapsed());

        // ── Step 7: compute K = G / Z_dk and commit ───────────────────────────
        let t3 = Instant::now();
        let g_ext: Polynomial<F, ExtendedLagrangeCoeff> = Polynomial {
            values: g_poly,
            _marker: PhantomData,
        };
        let k_ext = dk_domain.divide_by_vanishing_poly(g_ext);
        let k_coeff_vals = dk_domain.extended_to_coeff(k_ext);
        let k_poly: Polynomial<F, Coeff> = Polynomial {
            values: k_coeff_vals,
            _marker: PhantomData,
        };

        let k_commitment = CS::commit(params, &k_poly, PolynomialLabel::Custom("protogalaxy_K".into()));
        transcript.write(&k_commitment)?;

        let gamma: F = transcript.squeeze_challenge();
        eprintln!("[protogalaxy] step7 K_commit:            {:>8.2?}", t3.elapsed());

        // ── Step 8-9: fold traces at gamma, compute nu(folded) ────────────────
        // E[j] = nu(folded)(ω^j) by the Protogalaxy identity.
        let t4 = Instant::now();
        let folded = fold_traces(&dk_domain, &traces_refs, &gamma);

        let logup_committed_f: Vec<logup::prover::Committed<F>> = folded
            .lookups
            .iter()
            .map(|l| logup::prover::Committed {
                multiplicities: l.multiplicities.clone(),
                helper_polys: l.helper_polys.clone(),
                aggregator_poly: l.aggregator_poly.clone(),
            })
            .collect();
        let trash_committed_f: Vec<trash::prover::Committed<F>> = folded
            .trash_polys
            .iter()
            .map(|p| trash::prover::Committed { trash_poly: p.clone() })
            .collect();
        let perm_committed_f = permutation::prover::Committed {
            sets: folded
                .perm_polys
                .iter()
                .map(|p| permutation::prover::CommittedSet {
                    permutation_product_poly: p.clone(),
                })
                .collect(),
        };
        let nu_folded: Polynomial<F, LagrangeCoeff> = pk.ev.evaluate_numerator(
            domain,
            &pk.vk.cs,
            &folded.advice_polys,
            &folded.instance_polys,
            &pk.fixed_values,
            &folded.y,
            folded.beta,
            folded.gamma,
            &folded.theta,
            folded.trash_challenge,
            &logup_committed_f,
            &trash_committed_f,
            &perm_committed_f,
            &l0_lag,
            &l_last_lag,
            &l_active_lag,
            &perm_pk_lag,
        );
        let error_terms = nu_folded.values;
        eprintln!("[protogalaxy] step8-9 fold+nu_folded:   {:>8.2?}", t4.elapsed());

        // k_at_gamma = E(beta_pg) / Z_dk(gamma).
        // degree(K) may exceed ext_len for large NB_FOLDED, making eval_polynomial
        // on the IFFT'd k_poly aliased.  Since E(beta_pg) = G(gamma) = K(gamma)*Z_dk(gamma)
        // and we know E exactly, we derive K(gamma) from E instead.
        let z_dk_at_gamma = gamma.pow([dk_domain.n]) - F::ONE;
        let e_at_beta_pg: F = error_terms.iter().zip(beta_coeffs.iter()).map(|(e, b)| *e * b).sum();
        let k_at_gamma = e_at_beta_pg * z_dk_at_gamma.invert().expect("Z_dk(gamma) must be nonzero");
        transcript.write(&k_at_gamma)?;

        // ── Step 10: commit to error polynomial ───────────────────────────────
        let t5 = Instant::now();
        let error_lagrange: Polynomial<F, LagrangeCoeff> = Polynomial {
            values: error_terms,
            _marker: PhantomData,
        };
        let error_coeff = domain.lagrange_to_coeff(error_lagrange.clone());
        let error_commitment =
            CS::commit(params, &error_lagrange, PolynomialLabel::Custom("protogalaxy_error".into()));
        transcript.write(&error_commitment)?;
        eprintln!("[protogalaxy] step10 error_commit:      {:>8.2?}", t5.elapsed());

        // ── Step 11: finalise proof with error correction ─────────────────────
        let t6 = Instant::now();
        let folded_trace = into_prover_trace(domain, folded);
        let result = finalise_folded_proof(
            params, &pk, folded_trace, beta_pg, error_coeff, transcript,
        );
        eprintln!("[protogalaxy] step11 finalise_proof:    {:>8.2?}", t6.elapsed());
        result
    }
}



/// Convert a `FoldingProverTrace` back to a `ProverTrace`.
fn into_prover_trace<F: PrimeField + WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    folded: FoldingProverTrace<F>,
) -> ProverTrace<F> {
    let advice_polys: Vec<Polynomial<F, Coeff>> = folded
        .advice_polys
        .iter()
        .map(|p| domain.lagrange_to_coeff(p.clone()))
        .collect();

    let instance_values = folded.instance_polys.clone();
    let instance_polys: Vec<Polynomial<F, Coeff>> = folded
        .instance_polys
        .into_iter()
        .map(|p| domain.lagrange_to_coeff(p))
        .collect();

    let lookups = folded
        .lookups
        .into_iter()
        .map(|l| logup::prover::Committed {
            multiplicities: l.multiplicities,
            helper_polys: l.helper_polys,
            aggregator_poly: l.aggregator_poly,
        })
        .collect();

    let trashcans = folded
        .trash_polys
        .into_iter()
        .map(|p| trash::prover::Committed { trash_poly: p })
        .collect();

    let permutations = permutation::prover::Committed {
        sets: folded
            .perm_polys
            .into_iter()
            .map(|p| permutation::prover::CommittedSet {
                permutation_product_poly: p,
            })
            .collect(),
    };

    ProverTrace {
        advice_polys,
        instance_polys,
        instance_values,
        lookups,
        trashcans,
        permutations,
        beta: folded.beta,
        gamma: folded.gamma,
        theta: folded.theta,
        trash_challenge: folded.trash_challenge,
        y: folded.y,
    }
}

/// Finalise the protogalaxy proof: same as `finalise_proof` but subtracts the
/// error polynomial from `nu` before dividing, and adds extra PCS queries.
#[allow(clippy::too_many_arguments)]
fn finalise_folded_proof<F, CS, T>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    trace: ProverTrace<F>,
    beta_pg: F,
    error_coeff: Polynomial<F, Coeff>,
    transcript: &mut T,
) -> Result<(), Error>
where
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    CS::Commitment: Hashable<T::Hash>,
{
    let domain = pk.vk.get_domain();

    // Compute nu(folded_witness) and subtract error correction.
    let nu = compute_nu_poly(pk, &trace);
    let error_ext = domain.coeff_to_extended(error_coeff.clone());
    let nu_corrected = nu - &error_ext;

    // Commit to corrected quotient h = (nu - E) / Z_n.
    let quotient_limbs = compute_h_poly::<F, CS, T>(params, domain, nu_corrected, transcript)?;

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

    let crate::plonk::prover::Evals {
        fixed_evals,
        instance_evals,
        advice_evals,
        ..
    } = write_evals_to_transcript(pk, 0, &instance_polys, &advice_polys, x, transcript)?;

    // Write the error polynomial evaluation at x.
    let error_at_x = eval_polynomial(&error_coeff.values, x);
    transcript.write(&error_at_x)?;

    let permutations_common = pk.permutation.evaluate(x, transcript)?;
    let permutations_eval = permutations.evaluate(pk, x, transcript)?;
    let lookups_eval: Vec<logup::prover::Evaluated<F>> = lookups
        .into_iter()
        .map(|p| p.evaluate(pk, x, transcript))
        .collect::<Result<Vec<_>, _>>()?;
    let trashcans_eval: Vec<trash::prover::Evaluated<F>> = trashcans
        .into_iter()
        .map(|p| p.evaluate(x, transcript))
        .collect::<Result<Vec<_>, _>>()?;

    let splitting_factor = x.pow_vartime([pk.vk.n() - 1]);
    let xn = splitting_factor * x;

    let expressions = partially_evaluate_identities(
        &pk.vk,
        &fixed_evals,
        &instance_evals,
        &advice_evals,
        &permutations_eval.evaluated,
        lookups_eval.iter().map(|inner| &inner.evaluated),
        trashcans_eval.iter().map(|inner| &inner.evaluated),
        &permutations_common,
        x,
        xn,
        beta,
        gamma,
        &theta,
        trash_challenge,
    );

    let (lin_poly_non_constant_part, _) =
        compute_linearization_poly(expressions, pk, &y, xn, splitting_factor, quotient_limbs);

    let mut queries = compute_queries(
        pk,
        0,
        &instance_polys,
        &advice_polys,
        &permutations_eval,
        &lookups_eval,
        &trashcans_eval,
        x,
        &lin_poly_non_constant_part,
    );

    // Extra queries for the error polynomial.
    queries.push(ProverQuery::new(x, &error_coeff));
    queries.push(ProverQuery::new(beta_pg, &error_coeff));

    CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

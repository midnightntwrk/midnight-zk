//! Decider prover: a proof that the final accumulator satisfies its relaxed
//! relation `Σᵢ powᵢ(β⃗)·fᵢ = e`, bound to the accumulator's (folded)
//! commitments.
//!
//! Grand-sum formulation. With `W(X) = Σᵢ powᵢ(β⃗)·Lᵢ(X)` and `f(X)` the
//! `y⃗`-combined identity polynomial of the folded trace (folded challenges
//! as constants), the prover commits to `S` with `S(ω⁰) = 0` and
//! `S(ω^{i+1}) = S(ωⁱ) + W(ωⁱ)·f(ωⁱ)`, and proves on all of `H`:
//! - `L₀(X)·S(X) = 0`,
//! - `S(ωX) − S(X) − W(X)·f(X) + e·L_{n−1}(X) = 0`, with the true first and
//!   last Lagrange polynomials of `H`.
//!
//! The second identity at `i < n − 1` is the recurrence; at `i = n − 1`, as
//! `ω^n = ω⁰`, it reads `S(ω⁰) = S(ω^{n−1}) + W·f − e`, i.e.
//! `S(ω^{n−1}) + W(ω^{n−1})·f(ω^{n−1}) = e` (the plan's
//! `(1 − L_{n−1})(…)` and `L_{n−1}(…)` identities in one). Summed over `H`
//! the left-hand side telescopes, so it implies `Σᵢ W(ωⁱ)·f(ωⁱ) = e` with no
//! degree bound on any polynomial. Both identities are combined with a fresh
//! `ζ` into `N(X)`, and `h = N/(Xⁿ − 1)` is committed and opened as in a
//! plonk proof. `deg N = (cs.degree() + 1)(n − 1)`: one more limb than a
//! plonk proof of the same circuit.
//!
//! Transcript: verifying key, accumulator (as in folding), `[S]`, `ζ`,
//! quotient limbs, `x`, phase-0/1/2 evaluations, `S(x)`, `S(ωx)`,
//! multi-open. The decider is not zero-knowledge (`S` is not blinded).

use std::{borrow::Cow, hash::Hash, slice};

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rayon::prelude::*;

use super::{poly::pow_vector, prover::ProverAccumulator, trace::evaluate_rows};
use crate::{
    plonk::{
        Error, ProvingKey, argument,
        keygen::compute_lagrange_polys,
        prover::{compute_h_poly, compute_queries, scaled_quotient_poly},
        traces::ProverTrace,
    },
    poly::{
        Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, PolynomialLabel,
        ProverQuery, Rotation, commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// Label of the grand-sum polynomial `S`.
pub(crate) fn grand_sum_label() -> PolynomialLabel {
    PolynomialLabel::Custom("grand_sum".into())
}

/// `S` in Lagrange form: `S₀ = 0`, `S_{i+1} = Sᵢ + wᵢ·fᵢ`.
fn grand_sum<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    w: &[F],
    f: &[F],
) -> Polynomial<F, LagrangeCoeff> {
    let mut s = domain.empty_lagrange();
    for i in 1..s.len() {
        s[i] = s[i - 1] + w[i - 1] * f[i - 1];
    }
    s
}

/// `N(X) = L₀·S + ζ·(S(ωX) − S − W·f + e·L_{n−1})` on the extended domain of
/// `dd`, where `f` is evaluated from the coefficient-form folded `trace`.
#[allow(clippy::too_many_arguments)]
fn relaxed_numerator<F, CS>(
    pk: &ProvingKey<F, CS>,
    dd: &EvaluationDomain<F>,
    trace: &ProverTrace<'_, F, Coeff>,
    w: Polynomial<F, LagrangeCoeff>,
    s: &Polynomial<F, Coeff>,
    zeta: F,
    e: F,
) -> Polynomial<F, ExtendedLagrangeCoeff>
where
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
{
    let cs = &pk.vk.cs;
    let n = dd.n as usize;
    let to_ext = |p: &Polynomial<F, Coeff>| dd.coeff_to_extended(p.clone());
    let lagrange_to_ext =
        |p: &Polynomial<F, LagrangeCoeff>| dd.coeff_to_extended(dd.lagrange_to_coeff(p.clone()));

    let advice: Vec<_> = trace
        .phase1_committed
        .polys_of(&cs.advice_labels())
        .par_iter()
        .map(to_ext)
        .collect();
    let instance: Vec<_> = trace.instance_polys.par_iter().map(to_ext).collect();
    let fixed: Vec<_> = pk.fixed_values.par_iter().map(lagrange_to_ext).collect();
    let sigmas: Vec<_> = pk.sigmas.values.par_iter().map(lagrange_to_ext).collect();
    let [l0, l_last, l_active_row] = compute_lagrange_polys(dd, cs);

    let f = pk.ev.evaluate_numerator::<ExtendedLagrangeCoeff, Coeff>(
        dd,
        cs,
        &advice,
        &instance,
        &fixed,
        &trace.y,
        trace.beta,
        trace.gamma,
        &trace.theta,
        &trace.trash_powers,
        &trace.phase1_committed,
        &trace.phase2_committed,
        |p| Cow::Owned(to_ext(p)),
        &l0,
        &l_last,
        &l_active_row,
        &sigmas,
    );

    let w = lagrange_to_ext(&w);
    let s = to_ext(s);
    let mut l_final = dd.empty_lagrange();
    l_final[n - 1] = F::ONE;
    let l_final = lagrange_to_ext(&l_final);

    // S(ωX) on the extended coset: ω is `rot` extended steps.
    let rot = 1 << (dd.extended_k() - dd.k());
    let len = dd.extended_len();
    let mut numerator = dd.empty_extended();
    numerator.par_iter_mut().enumerate().for_each(|(i, v)| {
        let s_next = s[(i + rot) % len];
        *v = l0[i] * s[i] + zeta * (s_next - s[i] - w[i] * f[i] + e * l_final[i]);
    });
    numerator
}

/// Proves that the final accumulator `acc` satisfies its relaxed relation,
/// writing the proof to `transcript`. Verify with
/// [`verify_relaxed_trace`](super::verify_relaxed_trace).
pub fn prove_relaxed_trace<F, CS, T>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    acc: ProverAccumulator<'_, F, CS>,
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
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    let vk = &pk.vk;
    let cs = &vk.cs;
    let domain = &vk.domain;
    let e = acc.public.error;

    vk.absorb_into(transcript)?;
    acc.public.absorb(transcript)?;

    // Grand sum S over H, committed after β⃗ and e are fixed.
    let f = evaluate_rows(pk, &acc.trace);
    let w = domain.lagrange_from_vec(pow_vector(&acc.public.betas));
    let s = domain.lagrange_to_coeff(grand_sum(domain, &w, &f));
    transcript.write(&CS::commit(params, &s, grand_sum_label()))?;
    let zeta: F = transcript.squeeze_challenge();

    // Quotient of N(X) by Xⁿ − 1, on a domain one degree larger than the
    // circuit's (N has the extra factor W).
    let trace = acc.trace.into_coeff(domain);
    let dd = EvaluationDomain::new(cs.degree() as u32 + 1, domain.k());
    let numerator = relaxed_numerator(pk, &dd, &trace, w, &s, zeta, e);
    let quotient_limbs = compute_h_poly::<F, CS, T>(params, &dd, numerator, transcript)?;

    let x: F = CS::squeeze_evaluation_point(transcript);
    let x_rotations = argument::rotations(cs)
        .into_iter()
        .map(|rotation| (rotation, domain.rotate_omega(x, rotation)))
        .collect();
    let phase0_evaluated = trace.phase0_committed.evaluate(cs, &x_rotations, transcript)?;
    let phase1_evaluated = trace.phase1_committed.evaluate(cs, &x_rotations, transcript)?;
    let phase2_evaluated = trace.phase2_committed.evaluate(cs, &x_rotations, transcript)?;
    let x_next = domain.rotate_omega(x, Rotation::next());
    transcript.write(&eval_polynomial(&s, x))?;
    transcript.write(&eval_polynomial(&s, x_next))?;

    let quotient_poly = scaled_quotient_poly(quotient_limbs, x, vk.n());
    let s_labels = [grand_sum_label()];
    let mut queries = compute_queries(
        pk,
        &[],
        &trace.instance_polys,
        &phase0_evaluated,
        &phase1_evaluated,
        &phase2_evaluated,
        &x_rotations,
        &quotient_poly,
    );
    queries.extend(
        [x, x_next].map(|point| {
            ProverQuery::new(&s_labels, slice::from_ref(&s), point, s_labels[0].clone())
        }),
    );

    CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure)
}

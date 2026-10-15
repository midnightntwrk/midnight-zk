//! Prover-side traces in Lagrange form: folding two traces and evaluating
//! the `y⃗`-combined identities `fᵢ` on every row `i` of the domain `H`.

use std::borrow::Cow;

use ff::WithSmallOrderMulGroup;

use super::{instance::fold_scalar, sparse_gates::SparseGates};
use crate::{
    plonk::{ProvingKey, traces::ProverTrace},
    poly::{LagrangeCoeff, Polynomial, commitment::PolynomialCommitmentScheme},
};

fn fold_polys<F: WithSmallOrderMulGroup<3>, B: Clone + Send + Sync>(
    a: &[Polynomial<F, B>],
    b: &[Polynomial<F, B>],
    x: F,
) -> Vec<Polynomial<F, B>> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| a.fold(b, x)).collect()
}

/// The trace `acc + x·(fresh − acc)`: witness and public-input polynomials
/// and challenges, all folded with the same `x`.
pub(crate) fn fold_trace<'a, F: WithSmallOrderMulGroup<3>>(
    acc: &ProverTrace<'a, F, LagrangeCoeff>,
    fresh: &ProverTrace<'a, F, LagrangeCoeff>,
    x: F,
) -> ProverTrace<'a, F, LagrangeCoeff> {
    let fold_vec = |a: &[F], b: &[F]| -> Vec<F> {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b).map(|(a, b)| fold_scalar(*a, *b, x)).collect()
    };
    ProverTrace {
        instance_polys: fold_polys(&acc.instance_polys, &fresh.instance_polys, x),
        instance_values: fold_polys(&acc.instance_values, &fresh.instance_values, x),
        phase0_committed: acc.phase0_committed,
        phase1_committed: acc.phase1_committed.fold(&fresh.phase1_committed, x),
        phase2_committed: acc.phase2_committed.fold(&fresh.phase2_committed, x),
        beta: fold_scalar(acc.beta, fresh.beta, x),
        gamma: fold_scalar(acc.gamma, fresh.gamma, x),
        theta: fold_vec(&acc.theta, &fresh.theta),
        trash_challenge: fold_scalar(acc.trash_challenge, fresh.trash_challenge, x),
        y: fold_vec(&acc.y, &fresh.y),
    }
}

/// `l₀`, `l_last` (first blinding row minus one) and `l_active_row` on `H`,
/// in Lagrange form: the selector polynomials the evaluator expects.
fn lagrange_selectors<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
) -> [Polynomial<F, LagrangeCoeff>; 3] {
    let domain = &pk.vk.domain;
    let n = domain.n as usize;
    let last = n - pk.vk.cs.blinding_factors() - 1;
    let mut l0 = domain.empty_lagrange();
    l0[0] = F::ONE;
    let mut l_last = domain.empty_lagrange();
    l_last[last] = F::ONE;
    let mut l_active_row = domain.empty_lagrange();
    for i in 0..last {
        l_active_row[i] = F::ONE;
    }
    [l0, l_last, l_active_row]
}

/// `fᵢ = Σ_k y_k·id_k(row i)` for every row `i` of `H`, with the trace's own
/// (possibly folded) challenges, public inputs and witness. Lagrange form
/// throughout: no FFT. The custom gates are evaluated only on the rows where
/// they are active.
pub(crate) fn evaluate_rows<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<'_, F, LagrangeCoeff>,
    sparse: &SparseGates<F>,
) -> Polynomial<F, LagrangeCoeff> {
    let t = std::time::Instant::now();
    let values = sparse.evaluate(
        &pk.vk.domain,
        trace.phase1_committed.polys_of(&pk.vk.cs.advice_labels()),
        &trace.instance_values,
        &pk.fixed_values,
        &trace.y,
    );
    let gates = t.elapsed().as_secs_f64() * 1e3;
    let (values, [perm, pre, fin]) = add_non_gate_rows(pk, trace, values);
    eprintln!(
        "[evaluate_numerator] gates={gates:.2} perm={perm:.2} lookup_precomp={pre:.2} lookup+trash={fin:.2}"
    );
    values
}

/// [`evaluate_rows`] with every gate evaluated on every row (the evaluator
/// of the plain prover); reference for [`evaluate_rows`].
#[cfg(test)]
pub(crate) fn evaluate_rows_dense<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<'_, F, LagrangeCoeff>,
) -> Polynomial<F, LagrangeCoeff> {
    let values = pk.ev.evaluate_custom_gates::<LagrangeCoeff>(
        &pk.vk.domain,
        &pk.vk.cs,
        trace.phase1_committed.polys_of(&pk.vk.cs.advice_labels()),
        &trace.instance_values,
        &pk.fixed_values,
        &trace.y,
        trace.beta,
        &trace.theta,
        trace.trash_challenge,
    );
    add_non_gate_rows(pk, trace, values).0
}

/// Adds the permutation, lookup and trash identities to the custom-gate
/// `values`; also returns the timings of the three parts in ms.
fn add_non_gate_rows<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<'_, F, LagrangeCoeff>,
    mut values: Polynomial<F, LagrangeCoeff>,
) -> (Polynomial<F, LagrangeCoeff>, [f64; 3]) {
    let [l0, l_last, l_active_row] = lagrange_selectors(pk);
    let times = pk.ev.add_non_gate_identities::<LagrangeCoeff, LagrangeCoeff>(
        &mut values,
        &pk.vk.domain,
        &pk.vk.cs,
        trace.phase1_committed.polys_of(&pk.vk.cs.advice_labels()),
        &trace.instance_values,
        &pk.fixed_values,
        &trace.y,
        trace.beta,
        trace.gamma,
        &trace.theta,
        trace.trash_challenge,
        &trace.phase1_committed,
        &trace.phase2_committed,
        Cow::Borrowed,
        &l0,
        &l_last,
        &l_active_row,
        &pk.sigmas.values,
    );
    (values, times)
}

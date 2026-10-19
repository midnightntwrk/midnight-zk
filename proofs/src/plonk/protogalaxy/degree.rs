//! The degree `d` of the folded identity `fᵢ`.
//!
//! A round folds the accumulator `ω₀` and the `k` fresh instances `ω₁, …, ω_k`
//! into `Σⱼ Lⱼ(X)·ωⱼ`, every witness value, public input and challenge
//! weighted by the Lagrange basis `Lⱼ` of `{0, …, k}` (degree `k`). With `d`
//! the total degree of the `y⃗`-combined identity `fᵢ` in all folded
//! variables (advice and instance values and the challenges
//! `θ⃗, β, γ, trash⃗, y⃗`; fixed columns, and selectors, which become fixed
//! columns, are constants), `fᵢ(Σⱼ Lⱼ(X)·ωⱼ)` has degree `d·k` in `X`. So
//! `G(X) = Σᵢ powᵢ(β⃗*)·fᵢ(Σⱼ Lⱼ(X)·ωⱼ)` has degree `d·k`, and
//! `K = (G − F(α)·L₀)/Z`, with `Z` of degree `k + 1`, has degree
//! `d·k − k − 1`: the folding proof carries its `d·k − k` coefficients.

use ff::Field;

use crate::plonk::{ConstraintSystem, Expression};

/// Degree of `expr` in the folded variables: advice and instance queries
/// count 1; fixed queries, selectors and constants count 0.
fn expression_degree<F: Field>(expr: &Expression<F>) -> usize {
    expr.evaluate(
        &|_| 0,
        &|_| 0,
        &|_| 0,
        &|_| 1,
        &|_| 1,
        &|a| a,
        &|a, b| a.max(b),
        &|a, b| a + b,
        &|a, _| a,
    )
}

/// Degree of `Σ θᵢ·eᵢ` (a lookup tuple compressed with `θ⃗`).
fn compressed_degree<F: Field>(tuple: &[Expression<F>]) -> usize {
    1 + tuple.iter().map(expression_degree).max().unwrap_or(0)
}

/// Degree of each identity of `cs` (before the `y⃗` factor), in the order of
/// [`ConstraintSystem::nb_y_challenges`].
fn identity_degrees<F: Field>(cs: &ConstraintSystem<F>) -> Vec<usize> {
    let mut degrees: Vec<usize> = cs
        .gates
        .iter()
        .flat_map(|g| g.polynomials().iter().map(expression_degree))
        .collect();

    // Permutation: `l₀(1 − z₀)`, `l_last(z_l² − z_l)`, `l₀(z_i − z_{i−1}(ω^last
    // X))` and, per set, `z(ωX)·Π(v + β·s + γ) − z(X)·Π(v + β·δʲX + γ)`,
    // where every factor `(v + β·s + γ)` has degree 1 (also for fixed `v`).
    let num_sets = cs.permutation.num_sets(cs.degree());
    if num_sets > 0 {
        let chunk_len = cs.degree() - 2;
        degrees.extend([1, 2]);
        degrees.extend(std::iter::repeat_n(1, num_sets - 1));
        degrees.extend(cs.permutation.columns.chunks(chunk_len).map(|chunk| 1 + chunk.len()));
    }

    // Logup, per argument: boundary `(l₀ + l_last)·Z`; per chunk the helper
    // `h·Πⱼ(fⱼ + β) − Σⱼ Π_{k≠j}(f_k + β)`; the accumulator
    // `(Z(ωX) − Z − s·Σh)·(t + β) + m`.
    for lookup in &cs.lookups {
        let chunked = lookup.chunk_by_degree(cs.lookup_chunk_bound());
        degrees.push(1);
        for chunk in chunked.input_expression_chunks() {
            degrees.push(1 + chunk.iter().map(|tuple| compressed_degree(tuple)).sum::<usize>());
        }
        let selector = expression_degree(chunked.selector_expression());
        let table = compressed_degree(chunked.table_expressions());
        degrees.push((1 + selector) + table);
    }

    // Trash: `Σⱼ cⱼ·eⱼ − (1 − q)·trash`, with an independent (folded)
    // challenge `cⱼ` per term.
    for trash in &cs.trashcans {
        let compressed =
            trash.constraint_expressions().iter().map(expression_degree).max().unwrap_or(0);
        degrees.push(1 + compressed);
    }

    debug_assert_eq!(degrees.len(), cs.nb_y_challenges());
    degrees
}

/// `d`: the degree of `fᵢ` in the folded witness values, public inputs and
/// challenges, i.e. the maximum over the identities of their degree in the
/// folded variables plus one (the `y⃗` factor). Folding `k` fresh instances,
/// `G` has degree `d·k` and `K` has degree `d·k − k − 1`. At least 2 (an upper
/// bound is enough).
pub fn folding_degree<F: Field>(cs: &ConstraintSystem<F>) -> usize {
    identity_degrees(cs).into_iter().map(|d| d + 1).max().unwrap_or(0).max(2)
}

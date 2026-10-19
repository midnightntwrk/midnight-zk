//! Protogalaxy folding of plonk instances: the building blocks.
//!
//! A *fresh instance* `ω` is the commit phases of a plonk proof
//! ([`commit_instance`] / [`read_instance`]): the phase-1 and phase-2
//! commitments, the public inputs and the challenges `θ⃗, β, γ, trash⃗, y⃗`.
//! No quotient, no opening. Committed instance columns are not supported (an
//! instance has none).
//!
//! For a row `i` of the domain `H` (all `n` rows, blinding rows included),
//! `fᵢ(ω) = Σ_m y_m·id_m(row i)` is the `y⃗`-combined identity of the circuit
//! (gates, permutation, lookups, trash), evaluated with `ω`'s own witness,
//! public inputs and challenges. An honest fresh instance has `fᵢ(ω) = 0` on
//! every row.
//!
//! An [`Accumulator`] `(ω, β⃗, e)`, with `β⃗ ∈ F^{log n}`, satisfies the
//! relaxed relation `Σᵢ powᵢ(β⃗)·fᵢ(ω) = e`, where `powᵢ(β⃗) = Π_b β_b^{i_b}`
//! and `i_b` is bit `b` of `i`. Folding combines instances linearly: every
//! commitment, public input and challenge (and, for the prover, every
//! witness polynomial) with the same weights. Fixed (verifying-key)
//! commitments are never folded.
//!
//! This module provides the instances, their linear combinations, the
//! evaluation of `fᵢ` on every row, its degree [`folding_degree`] and the
//! polynomial helpers of the protocol.
//!
//! # Folding
//!
//! Let `t = log n`, `d = `[`folding_degree`], `k ≥ 1` the number of fresh
//! instances folded per round, `{0, …, k}` the folding domain, `Lⱼ` its
//! Lagrange basis and `Z` its vanishing polynomial.
//!
//! [`Accumulator::init`], on a fresh instance `ω`:
//! - absorb `ω` (commitments, public inputs) and squeeze `β`;
//! - the accumulator is `(ω, β⃗ = (β, β², β⁴, …), e = 0)`.
//!
//! One round, [`Accumulator::fold`], with the accumulator `(ω₀, β⃗, e)` and
//! the fresh instances `ω₁, …, ω_k`:
//! 1. absorb the accumulator, then `ω₁, …, ω_k` (commitments, public inputs);
//! 2. squeeze `δ`, `δ⃗ = (δ, δ², δ⁴, …)`;
//! 3. read `F₁, …, F_t`: the perturbator is `F = (e, F₁, …, F_t)`;
//! 4. squeeze `α`, `β⃗* = β⃗ + α·δ⃗`;
//! 5. read the `d·k − k` coefficients of `K`, constant term first;
//! 6. squeeze `γ`;
//! 7. `ω* = Σⱼ Lⱼ(γ)·ωⱼ` and `e* = F(α)·L₀(γ) + Z(γ)·K(γ)`; the new accumulator
//!    is `(ω*, β⃗*, e*)`.
//!
//! For an honest prover, `G(X) = Σᵢ powᵢ(β⃗*)·fᵢ(Σⱼ Lⱼ(X)·ωⱼ)` satisfies
//! `G(0) = F(α)` and `G(j) = 0` for `j = 1, …, k`, so `K = (G − F(α)·L₀)/Z`
//! is a polynomial and `e* = G(γ)`. Each round uses a fresh transcript,
//! supplied by the caller.

mod poly;

mod instance;

pub use instance::{Accumulator, Challenges, FoldingInstance};

mod degree;
mod trace;

pub use degree::folding_degree;

mod decider_prover;
mod decider_verifier;
mod prover;
mod verifier;

pub use decider_prover::prove_relaxed_trace;
pub use decider_verifier::verify_relaxed_trace;
pub use prover::{ProverAccumulator, ProverInstance, commit_instance};
pub use verifier::read_instance;

#[cfg(test)]
mod tests;

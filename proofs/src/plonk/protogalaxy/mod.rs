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
//! polynomial helpers of the protocol. The fold itself (`init` and the k-ary
//! `fold`, prover and verifier) is built on them.

// Used by the fold (next commit).
#![allow(dead_code)]

mod poly;

mod instance;

pub use instance::{Accumulator, Challenges, FoldingInstance};

mod degree;
mod trace;

pub use degree::folding_degree;

mod prover;
mod verifier;

pub use prover::{ProverAccumulator, ProverInstance, commit_instance};
pub use verifier::read_instance;

#[cfg(test)]
mod tests;

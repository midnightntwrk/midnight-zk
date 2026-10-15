//! Running-accumulator Protogalaxy folding (scalar error term) and its
//! decider.
//!
//! An IVC step produces a *fresh instance* only: the commit phases of a
//! plonk proof ([`commit_instance`] / [`read_instance`]), no quotient and no
//! opening. Fresh instances are folded 2-to-1 into an [`Accumulator`]
//! satisfying the relaxed relation `Σᵢ powᵢ(β⃗)·fᵢ(ω) = e`, where `fᵢ` is the
//! `y⃗`-combined identity at row `i` of the domain `H` (all rows, blinding
//! rows included), with the accumulator's folded witness, public inputs and
//! challenges, and `powᵢ(β⃗) = Π_b β_b^{i_b}`.
//!
//! Fixed (verifying-key) commitments are never folded. Witness commitments
//! are folded per phase: with fflonk each phase commitment is a vector of
//! chunk commitments, folded chunk by chunk.
//!
//! # Initialisation
//! The first fresh instance becomes the accumulator ([`Accumulator::init`]):
//! fresh `init` transcript, absorb the instance (phase-1 commitment, phase-2
//! commitment, public inputs column by column), squeeze `β`, set
//! `β⃗ = (β, β², β⁴, …)` (`log n` entries) and `e = 0`.
//!
//! # Folding round ([`Accumulator::fold`], fresh transcript per round)
//! 1. Absorb the accumulator: phase-1 commitment, phase-2 commitment, public
//!    inputs (column by column), `θ⃗`, `β`, `γ`, `trash`, `y⃗`, then `β⃗`, `e`.
//! 2. Absorb the fresh instance: phase-1 commitment, phase-2 commitment, public
//!    inputs (column by column). Its challenges are not absorbed: they are
//!    derived from its own transcript (verifying key, public inputs,
//!    commitments).
//! 3. Squeeze `δ`; `δ⃗ = (δ, δ², δ⁴, …)`.
//! 4. Prover writes `F_1, …, F_{log n}`, the coefficients of the perturbator
//!    `F(X) = Σᵢ powᵢ(β⃗ + X·δ⃗)·fᵢ(acc)` except `F_0`, which is `e`.
//! 5. Squeeze `α`; `β⃗* = β⃗ + α·δ⃗`.
//! 6. Prover writes `K_0, …, K_{d−2}`, the coefficients of
//!    `K = (G − F(α)·L₀)/Z`, where
//!    `G(X) = Σᵢ powᵢ(β⃗*)·fᵢ(L₀(X)·acc + L₁(X)·fresh)`,
//!    `L₀ = 1 − X`, `L₁ = X`, `Z = X(X − 1)` and `d = d_total`
//!    ([`folding_degree`]).
//! 7. Squeeze `γ` (truncated under `truncated-challenges`).
//! 8. New accumulator: `β⃗*`, `e' = F(α)·(1 − γ) + γ(γ − 1)·K(γ)`, and every
//!    commitment, public input and challenge `acc + γ·(fresh − acc)`.
//!
//! # Decider
//! [`prove_relaxed_trace`] / [`verify_relaxed_trace`] prove the relaxed
//! relation of the final accumulator with a grand-sum column; see
//! `decider_prover.rs`.

mod decider_prover;
mod decider_verifier;
mod degree;
mod instance;
mod poly;
mod prover;
mod sparse_gates;
mod trace;
mod verifier;

#[cfg(test)]
mod tests;

pub use decider_prover::prove_relaxed_trace;
pub use decider_verifier::verify_relaxed_trace;
pub use degree::folding_degree;
pub use instance::{Accumulator, Challenges, FoldingInstance};
pub use prover::{ProverAccumulator, ProverInstance, commit_instance};
pub use verifier::read_instance;

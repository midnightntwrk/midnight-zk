//! Representation of a Trace for a single proof being generated.

use ff::PrimeField;

use crate::{
    plonk::{logup, permutation, trash},
    poly::{commitment::PolynomialCommitmentScheme, Coeff, LagrangeCoeff, Polynomial},
};

/// Prover's trace of a proof.
#[derive(Debug)]
pub struct ProverTrace<F: PrimeField> {
    pub(crate) advice_polys: Vec<Polynomial<F, Coeff>>,
    pub(crate) instance_polys: Vec<Polynomial<F, Coeff>>,
    #[allow(dead_code)]
    // This field will be useful for split accumulation
    pub(crate) instance_values: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) lookups: Vec<logup::prover::Committed<F>>,
    pub(crate) trashcans: Vec<trash::prover::Committed<F>>,
    pub(crate) permutations: permutation::prover::Committed<F>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) trash_challenge: F,
    pub(crate) y: F,
}

/// Verifier's trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) advice_commitments: Vec<PCS::Commitment>,
    pub(crate) lookups: Vec<logup::verifier::Committed<F, PCS>>,
    pub(crate) trashcans: Vec<trash::verifier::Committed<F, PCS>>,
    pub(crate) permutations: permutation::verifier::Committed<F, PCS>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) trash_challenge: F,
    pub(crate) y: F,
}

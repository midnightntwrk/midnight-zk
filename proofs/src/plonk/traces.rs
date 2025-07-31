//! Representation of a Trace for a batch of proofs that are being generated
//! simultaneously.

use ff::PrimeField;

use crate::{
    plonk::{lookup, permutation, vanishing},
    poly::{commitment::PolynomialCommitmentScheme, Coeff, LagrangeCoeff, Polynomial},
};

/// Prover's trace of a set of proofs. This type guarantees that the size of the
/// outer vector of its fields has the same size.
#[derive(Debug)]
pub struct ProverTrace<F: PrimeField> {
    pub(crate) advice_polys: Vec<Vec<Polynomial<F, Coeff>>>,
    pub(crate) instance_polys: Vec<Vec<Polynomial<F, Coeff>>>,
    #[allow(dead_code)]
    // This field will be useful for split accumulation
    pub(crate) instance_values: Vec<Vec<Polynomial<F, LagrangeCoeff>>>,
    pub(crate) vanishing: vanishing::prover::Committed<F>,
    pub(crate) lookups: Vec<Vec<lookup::prover::Committed<F>>>,
    pub(crate) permutations: Vec<permutation::prover::Committed<F>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) y: F,
}

/// Verifier's trace of a set of proofs. This type guarantees that the size of
/// the outer vector of its fields has the same size.
#[derive(Debug)]
pub struct VerifierTrace<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) advice_commitments: Vec<Vec<PCS::Commitment>>,
    pub(crate) vanishing: vanishing::verifier::Committed<F, PCS>,
    pub(crate) lookups: Vec<Vec<lookup::verifier::Committed<F, PCS>>>,
    pub(crate) permutations: Vec<permutation::verifier::Committed<F, PCS>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) y: F,
}

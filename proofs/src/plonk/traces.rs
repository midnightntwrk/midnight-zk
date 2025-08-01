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

/// Trace of a set of proofs folded with folding. This type guarantees that the
/// size of the outer vector of its fields has the same size. It contains the
/// folded fixed_polynomials, allowing for folding of different circuits.
#[derive(Debug)]
pub struct FoldingProverTrace<F: PrimeField> {
    pub(crate) fixed_polys: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) advice_polys: Vec<Vec<Polynomial<F, Coeff>>>,
    pub(crate) instance_polys: Vec<Vec<Polynomial<F, Coeff>>>,
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

impl<F: PrimeField> ProverTrace<F> {
    /// Convert a plonk trace, into a folding trace. This includes the
    /// fixed_polynomials, enabling folding of circuits with different fixed
    /// polynomials.
    pub fn into_folding_trace(
        self,
        fixed_polys: Vec<Polynomial<F, LagrangeCoeff>>,
    ) -> FoldingProverTrace<F> {
        let ProverTrace {
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
        } = self;
        FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
        }
    }
}

impl<F: PrimeField> From<FoldingProverTrace<F>> for ProverTrace<F> {
    fn from(value: FoldingProverTrace<F>) -> Self {
        let FoldingProverTrace {
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
            ..
        } = value;
        Self {
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
        }
    }
}

/// Verifier's trace of a set of proofs. This type guarantees that the size of
/// the outer vector of its fields has the same size.
// TODO: Missing the instances here :thinking-face:
#[derive(Debug)]
pub struct VerifierFoldingTrace<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) advice_commitments: Vec<Vec<PCS::Commitment>>,
    pub(crate) fixed_commitments: Vec<PCS::Commitment>,
    pub(crate) vanishing: vanishing::verifier::Committed<F, PCS>,
    pub(crate) lookups: Vec<Vec<lookup::verifier::Committed<F, PCS>>>,
    pub(crate) permutations: Vec<permutation::verifier::Committed<F, PCS>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) y: F,
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> VerifierTrace<F, PCS> {
    /// Convert a plonk trace, into a folding trace. This includes the
    /// fixed_polynomials, enabling folding of circuits with different fixed
    /// polynomials.
    pub fn into_folding_trace(
        self,
        fixed_commitments: &Vec<PCS::Commitment>,
    ) -> VerifierFoldingTrace<F, PCS> {
        let VerifierTrace {
            advice_commitments,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
        } = self;
        VerifierFoldingTrace {
            advice_commitments,
            fixed_commitments: fixed_commitments.clone(),
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
        }
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> From<VerifierFoldingTrace<F, PCS>>
    for VerifierTrace<F, PCS>
{
    fn from(value: VerifierFoldingTrace<F, PCS>) -> Self {
        let VerifierFoldingTrace {
            advice_commitments,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
            ..
        } = value;
        Self {
            advice_commitments,
            vanishing,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
        }
    }
}

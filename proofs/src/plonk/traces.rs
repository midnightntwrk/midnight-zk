//! Representation of a Trace for a single proof being generated.

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::argument,
    poly::{
        Coeff, EvaluationDomain, LagrangeCoeff, Polynomial, PolynomialRepresentation,
        commitment::PolynomialCommitmentScheme,
    },
};

/// Prover's trace of a proof.
///
/// `B` is the representation of the phase-1 and phase-2 polynomials: Lagrange
/// right after the commit phases (see `CommittedTrace`), coefficients for the
/// rest of the proof.
#[derive(Debug)]
pub struct ProverTrace<'a, F: PrimeField, B: PolynomialRepresentation = Coeff> {
    pub(crate) instance_polys: Vec<Polynomial<F, Coeff>>,
    #[allow(dead_code)]
    // This field will be useful for split accumulation
    pub(crate) instance_values: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) phase0_committed: &'a argument::prover::Committed<F, Coeff>,
    pub(crate) phase1_committed: argument::prover::Committed<F, B>,
    pub(crate) phase2_committed: argument::prover::Committed<F, B>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: Vec<F>,
    pub(crate) trash_challenge: F,
    pub(crate) y: Vec<F>,
}

impl<'a, F: WithSmallOrderMulGroup<3>> ProverTrace<'a, F, LagrangeCoeff> {
    /// Converts the phase-1 and phase-2 polynomials to coefficient form.
    pub(crate) fn into_coeff(self, domain: &EvaluationDomain<F>) -> ProverTrace<'a, F> {
        ProverTrace {
            instance_polys: self.instance_polys,
            instance_values: self.instance_values,
            phase0_committed: self.phase0_committed,
            phase1_committed: self.phase1_committed.into_coeff(domain),
            phase2_committed: self.phase2_committed.into_coeff(domain),
            beta: self.beta,
            gamma: self.gamma,
            theta: self.theta,
            trash_challenge: self.trash_challenge,
            y: self.y,
        }
    }
}

/// Prover's trace after the commit phases only (see
/// [`commit_phases`](crate::plonk::prover::commit_phases)): the phase-1 and
/// phase-2 polynomials in Lagrange form, the challenges, and the commitments
/// written to the transcript. This is a fresh instance for folding.
#[derive(Debug)]
pub(crate) struct CommittedTrace<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
    // The commitments are read by the folding prover (Phase C).
    #[allow(dead_code)]
    pub(crate) phase1_commitment: CS::Commitment,
    #[allow(dead_code)]
    pub(crate) phase2_commitment: CS::Commitment,
}

/// Verifier's trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) phase0_committed: argument::verifier::Committed<F, PCS>,
    pub(crate) phase1_committed: argument::verifier::Committed<F, PCS>,
    pub(crate) phase2_committed: argument::verifier::Committed<F, PCS>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: Vec<F>,
    pub(crate) trash_challenge: F,
    pub(crate) y: Vec<F>,
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> VerifierTrace<F, PCS> {
    /// Commitment to the phase-1 polynomials (advice columns and logup
    /// multiplicities), as read from the transcript.
    pub fn phase1_commitment(&self) -> &PCS::Commitment {
        self.phase1_committed.commitment()
    }

    /// Commitment to the phase-2 polynomials (permutation, logup and trash
    /// columns), as read from the transcript.
    pub fn phase2_commitment(&self) -> &PCS::Commitment {
        self.phase2_committed.commitment()
    }
}

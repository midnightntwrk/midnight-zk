use crate::{
    field::AssignedNative,
    verifier::{SelfEmulation, pcs::InCircuitPCS},
};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    pub(crate) advice_commitments: Vec<PCS::AssignedCommitment>,
    /// `None` when the group holds no polynomials, which the prover does not
    /// commit to.
    pub(crate) phase1_committed: Option<super::argument::Committed<S, PCS>>,
    /// `None` when the group holds no polynomials, which the prover does not
    /// commit to.
    pub(crate) phase2_committed: Option<super::argument::Committed<S, PCS>>,
    pub(crate) permutations: super::permutation::Committed<S, PCS>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) theta: AssignedNative<S::F>,
    pub(crate) trash_challenge: AssignedNative<S::F>,
    pub(crate) y: AssignedNative<S::F>,
}

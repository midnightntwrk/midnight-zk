use crate::{
    field::AssignedNative,
    verifier::{pcs::InCircuitPCS, SelfEmulation},
};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    pub(crate) advice_commitments: Vec<PCS::AssignedCommitment>,
    pub(crate) lookups: Vec<super::lookup::Committed<S, PCS>>,
    pub(crate) trashcans: Vec<super::trash::Committed<S, PCS>>,
    pub(crate) permutations: super::permutation::Committed<S, PCS>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) theta: AssignedNative<S::F>,
    pub(crate) trash_challenge: AssignedNative<S::F>,
    pub(crate) y: AssignedNative<S::F>,
}

use crate::{field::AssignedNative, verifier::SelfEmulation};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<S: SelfEmulation> {
    pub(crate) advice_commitments: Vec<S::AssignedPoint>,
    pub(crate) vanishing: super::vanishing::Committed<S>,
    pub(crate) lookups: Vec<super::lookup::Committed<S>>,
    pub(crate) trashcans: Vec<super::trash::Committed<S>>,
    pub(crate) permutations: super::permutation::Committed<S>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) theta: AssignedNative<S::F>,
    pub(crate) trash_challenge: AssignedNative<S::F>,
    pub(crate) y: AssignedNative<S::F>,
}

use crate::{field::AssignedNative, verifier::SelfEmulation};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<S: SelfEmulation> {
    pub(crate) phase0_committed: super::argument::Committed<S>,
    pub(crate) phase1_committed: super::argument::Committed<S>,
    pub(crate) phase2_committed: super::argument::Committed<S>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) theta: Vec<AssignedNative<S::F>>,
    pub(crate) trash_challenges: Vec<AssignedNative<S::F>>,
    pub(crate) y: Vec<AssignedNative<S::F>>,
}

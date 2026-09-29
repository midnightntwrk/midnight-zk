use crate::{
    field::AssignedNative,
    verifier::{SelfEmulation, pcs::InCircuitPCS},
};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    pub(crate) phase0_committed: super::argument::Committed<S, PCS>,
    pub(crate) phase1_committed: super::argument::Committed<S, PCS>,
    pub(crate) phase2_committed: super::argument::Committed<S, PCS>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) theta: AssignedNative<S::F>,
    pub(crate) trash_challenge: AssignedNative<S::F>,
    pub(crate) y: AssignedNative<S::F>,
}

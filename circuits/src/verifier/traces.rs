use crate::{CircuitField, field::AssignedNative, verifier::InCircuitPCS};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<F: CircuitField, PCS: InCircuitPCS<F>> {
    pub(crate) phase0_committed: super::argument::Committed<F, PCS>,
    pub(crate) phase1_committed: super::argument::Committed<F, PCS>,
    pub(crate) phase2_committed: super::argument::Committed<F, PCS>,
    pub(crate) beta: AssignedNative<F>,
    pub(crate) gamma: AssignedNative<F>,
    pub(crate) theta: AssignedNative<F>,
    pub(crate) trash_challenge: AssignedNative<F>,
    pub(crate) y: AssignedNative<F>,
}

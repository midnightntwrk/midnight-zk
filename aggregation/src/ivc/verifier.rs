//! IVC verifier.
//!
//! Given an [`IvcInstance`] and the corresponding proof bytes, the
//! [`IvcVerifier`] checks that a valid chain of transitions from genesis
//! to the claimed state exists. Verification is constant-time regardless
//! of how many steps the prover has performed.

use group::Group;
use midnight_circuits::{hash::poseidon::PoseidonState, verifier::Accumulator};
use midnight_proofs::{
    plonk::{self},
    poly::kzg::{params::ParamsVerifierKZG, KZGCommitmentScheme},
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{MidnightVK, Relation};

use super::{IvcCircuit, IvcError, IvcInstance, IvcTransition, C, E, F, S};

/// Lightweight IVC verifier carrying only:
/// - the self-verifying key,
/// - the SRS verifier parameters (for the pairing check).
///
/// Returned by [`super::setup()`].
#[derive(Clone, Debug)]
pub struct IvcVerifier {
    pub(crate) vk: MidnightVK,
    pub(crate) params_verifier: ParamsVerifierKZG<E>,
}

impl IvcVerifier {
    /// Verifies an IVC proof against the given instance.
    ///
    /// Checks that the proof is valid with respect to the given instance by:
    /// 1. Preparing the proof to obtain a proof accumulator.
    /// 2. Accumulating it with the instance's accumulator.
    /// 3. Checking the pairing invariant on the result.
    ///
    /// This method checks that `instance.vk_repr` matches the canonical
    /// verifying key held by this verifier (derived from
    /// [`setup`](super::setup())). Without this check, a proof generated
    /// under a different (potentially malicious) circuit could pass
    /// verification.
    pub fn verify<T: IvcTransition>(
        &self,
        instance: &IvcInstance<T>,
        proof: &[u8],
    ) -> Result<(), IvcError> {
        // Reject proofs whose instance claims a different verifying key.
        if instance.vk_repr != self.vk.vk().transcript_repr() {
            return Err(IvcError::VkMismatch);
        }

        let fixed_bases = midnight_circuits::verifier::fixed_bases::<S>("self_vk", self.vk.vk());

        let pi =
            IvcCircuit::<T>::format_instance(instance).map_err(|_| IvcError::InvalidInstance)?;

        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(proof);
        let dual_msm =
            plonk::prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                self.vk.vk(),
                &[&[C::identity()]],
                &[&[&pi]],
                &mut transcript,
            )
            .map_err(|_| IvcError::InvalidProof)?;

        let proof_acc = Accumulator::from_dual_msm(dual_msm, "self_vk", &fixed_bases);

        // Verify that both `proof_acc` and `instance.acc` satisfy the pairing
        // invariant, with a single pairing, by accumulating them first.
        let final_acc = Accumulator::<S>::accumulate(&[proof_acc, instance.acc.clone()]);
        if !final_acc.check(&self.params_verifier, &fixed_bases) {
            return Err(IvcError::InvalidProof);
        };
        transcript.assert_empty().map_err(|_| IvcError::TranscriptNotEmpty)?;
        Ok(())
    }
}

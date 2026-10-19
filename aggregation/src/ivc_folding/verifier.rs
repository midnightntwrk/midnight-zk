//! Folding-IVC verifier: native fold of the last instance and the decider.

use midnight_proofs::{
    plonk::{
        VerifyingKey,
        protogalaxy::{Accumulator, read_instance, verify_relaxed_trace},
    },
    poly::commitment::{Guard, PolynomialCommitmentScheme},
    transcript::Transcript,
};

use super::{
    FoldingPCS,
    types::{FoldingIvcInstance, FoldingIvcProof, Tr, accumulator_hash, step_public_inputs},
};
use crate::ivc::{F, Ivc, IvcError};

/// Folding-IVC verifier carrying the application context, the step
/// circuit's verifying key and the PCS verifier parameters.
#[derive(Clone, Debug)]
pub struct FoldingIvcVerifier<T: Ivc> {
    pub(crate) ctx: T::Context,
    pub(crate) vk: VerifyingKey<F, FoldingPCS>,
    pub(crate) params_verifier: <FoldingPCS as PolynomialCommitmentScheme<F>>::VerifierParameters,
}

impl<T: Ivc> FoldingIvcVerifier<T> {
    /// The step circuit's verifying key.
    pub fn vk(&self) -> &VerifyingKey<F, FoldingPCS> {
        &self.vk
    }

    /// Verifies `proof` for `instance`:
    /// 1. the application-level decider on the state;
    /// 2. reads the last step's instance for the public inputs `[vk_repr,
    ///    H(state ‖ H(acc))]`, so that it is bound to `instance`;
    /// 3. folds it into the accumulator (or initialises the accumulator with it
    ///    if the accumulator is the default one);
    /// 4. verifies the decider proof of the result.
    pub fn verify(
        &self,
        instance: &FoldingIvcInstance<T>,
        proof: &FoldingIvcProof,
    ) -> Result<(), IvcError> {
        if !T::decider(&self.ctx, &instance.state) {
            return Err(IvcError::DeciderFailed);
        }
        let acc_hash = accumulator_hash(instance.acc.as_ref());
        let pi = step_public_inputs::<T>(&self.vk, &instance.state, acc_hash);

        let mut transcript = Tr::init_from_bytes(&proof.partial_proof);
        let fresh = read_instance(&self.vk, &[&[], &pi], &mut transcript)
            .map_err(|_| IvcError::InvalidProof)?;
        transcript.assert_empty().map_err(|_| IvcError::TranscriptNotEmpty)?;

        let mut transcript = Tr::init_from_bytes(&proof.folding_proof);
        let acc = match &instance.acc {
            None => Accumulator::init(&self.vk, fresh, &mut transcript),
            Some(acc) => acc.fold(&self.vk, &[fresh], Some(acc_hash), &mut transcript),
        }
        .map_err(|_| IvcError::InvalidProof)?;
        transcript.assert_empty().map_err(|_| IvcError::TranscriptNotEmpty)?;

        let mut transcript = Tr::init_from_bytes(&proof.decider_proof);
        let guard = verify_relaxed_trace(&self.vk, &acc, &mut transcript)
            .map_err(|_| IvcError::InvalidProof)?;
        transcript.assert_empty().map_err(|_| IvcError::TranscriptNotEmpty)?;
        guard.verify(&self.params_verifier).map_err(|_| IvcError::InvalidProof)
    }
}

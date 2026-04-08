// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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

use super::{Ivc, IvcCircuit, IvcError, IvcInstance, C, E, F, S};

/// Lightweight IVC verifier carrying:
/// - the application context (for the decider check),
/// - the self-verifying key,
/// - the SRS verifier parameters (for the pairing check).
///
/// Returned by [`super::setup()`].
#[derive(Clone, Debug)]
pub struct IvcVerifier<T: Ivc> {
    pub(crate) ctx: T::Context,
    pub(crate) vk: MidnightVK,
    pub(crate) params_verifier: ParamsVerifierKZG<E>,
}

impl<T: Ivc> IvcVerifier<T> {
    /// Verifies an IVC proof against the given instance.
    ///
    /// Checks that the proof is valid with respect to the given instance by:
    /// 1. Preparing the proof to obtain a proof accumulator.
    /// 2. Accumulating it with the instance's accumulator.
    /// 3. Checking the pairing invariant on the result.
    /// 4. Running the application-level [`decider`](super::IvcState::decider)
    ///    on the instance state.
    ///
    /// This method checks that `instance.vk_repr` matches the canonical
    /// verifying key held by this verifier (derived from
    /// [`setup`](super::setup())). Without this check, a proof generated
    /// under a different (potentially malicious) circuit could pass
    /// verification.
    pub fn verify(&self, instance: &IvcInstance<T>, proof: &[u8]) -> Result<(), IvcError> {
        // Reject proofs whose instance claims a different verifying key.
        if instance.vk_repr != self.vk.vk().transcript_repr() {
            return Err(IvcError::VkMismatch);
        }

        if !T::decider(&self.ctx, &instance.state) {
            return Err(IvcError::DeciderFailed);
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

        transcript.assert_empty().map_err(|_| IvcError::TranscriptNotEmpty)?;

        let proof_acc = Accumulator::from_dual_msm(dual_msm, "self_vk", &fixed_bases);

        // Verify that both `proof_acc` and `instance.acc` satisfy the pairing
        // invariant, with a single pairing, by accumulating them first.
        let final_acc = Accumulator::<S>::accumulate(&[proof_acc, instance.acc.clone()]);
        if !final_acc.check(&self.params_verifier, &fixed_bases) {
            return Err(IvcError::InvalidProof);
        };

        Ok(())
    }
}

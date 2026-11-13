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

//! An assigned verifying key that has been absorbed into a transcript.

use midnight_proofs::{
    circuit::Layouter, plonk::Error, poly::PolynomialLabel, transcript::Hashable,
};

use super::{
    AssignedVk, ScalarChip,
    pcs::{AssignedCommitment, InCircuitPCS},
    transcript_gadget::InCircuitTranscript,
};
use crate::CircuitField;

/// An assigned verifying key whose `transcript_repr` has been absorbed into a
/// transcript.
///
/// The `transcript_repr` hashes every commitment the key holds, so those
/// commitments are bound to the transcript as much as the ones read from the
/// proof. The field is private to this module, so the only way to obtain one is
/// through [`AssignedVk::absorb_into`].
#[derive(Debug)]
pub(crate) struct AbsorbedVk<'a, F: CircuitField, PCS: InCircuitPCS<F>>(&'a AssignedVk<F, PCS>);

impl<'a, F: CircuitField, PCS: InCircuitPCS<F>> AbsorbedVk<'a, F, PCS> {
    /// The commitment the absorbed key holds to its phase-0 group: every fixed
    /// column and the fixed permutation polynomials.
    pub(crate) fn phase0_commitment(&self) -> &'a AssignedCommitment<F, PCS> {
        &self.0.phase0_commitment
    }

    /// The labels of the polynomials committed to by
    /// [`Self::phase0_commitment`].
    pub(crate) fn phase0_labels(&self) -> Vec<PolynomialLabel> {
        self.0.cs.fixed_polys_labels()
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> AssignedVk<F, PCS> {
    /// Absorbs this verifying key into `transcript`, returning the witness that
    /// it was.
    pub(crate) fn absorb_into<T>(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar_chip: &ScalarChip<F>,
        transcript: &mut T,
    ) -> Result<AbsorbedVk<'_, F, PCS>, Error>
    where
        F: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
        transcript.common(layouter, scalar_chip, &self.transcript_repr)?;
        Ok(AbsorbedVk(self))
    }
}

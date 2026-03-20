// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

//! Variable-length vector type for scanner operations.
//!
//! A [`ScannerVec`] is built from an [`AssignedVector`] of [`AssignedByte`]s
//! with the following guarantees enforced in-circuit:
//!
//!  - **Payload elements are range-checked** to `[0, 255]` (they originate from
//!    [`AssignedByte`]s).
//!  - **Filler elements are constrained to 256**
//!    ([`ALPHABET_MAX_SIZE`](super::ALPHABET_MAX_SIZE)), making them
//!    unmatchable in substring lookup arguments.
//!  - **Length is anchored**: constrained to equal the number of non-filler
//!    elements in the buffer.
//!  - **Padding flags and limits are cached** and available at no extra cost
//!    after construction.
//!
//! The chunk size `A` of the source [`AssignedVector`] determines filler
//! placement and is preserved in the type.
//!
//! These properties make [`ScannerVec`] safe for use in both automaton parsing
//! ([`ScannerChip::parse_varlen`](super::ScannerChip::parse_varlen)) and
//! variable-length substring checks
//! ([`ScannerChip::check_bytes_varlen`](super::ScannerChip::check_bytes_varlen)).

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use super::{ScannerChip, ALPHABET_MAX_SIZE};
use crate::{
    field::{native::AssignedBit, AssignedNative},
    instructions::{
        AssignmentInstructions, ControlFlowInstructions, RangeCheckInstructions, VectorInstructions,
    },
    types::{AssignedByte, AssignedVector},
    CircuitField,
};

/// A variable-length vector with filler elements constrained to
/// [`ALPHABET_MAX_SIZE`](super::ALPHABET_MAX_SIZE).
///
/// Stores a promoted buffer where filler positions are constrained to 256,
/// along with the effective payload length. The chunk size `A` of the
/// original [`AssignedVector`] is preserved in the type for alignment
/// purposes. The padding flags and limits are computed once at construction
/// time and cached.
#[derive(Debug, Clone)]
pub struct ScannerVec<F: CircuitField, const M: usize, const A: usize> {
    /// The effective length of the payload (constrained during construction).
    length: AssignedNative<F>,
    /// Buffer with filler positions constrained to 256.
    pub(crate) buffer: [AssignedNative<F>; M],
    /// (start, end) positions of the payload in the buffer.
    pub(crate) limits: (AssignedNative<F>, AssignedNative<F>),
    /// Per-element padding flags (1 = filler, 0 = payload).
    pub(crate) padding_flags: [AssignedBit<F>; M],
}

impl<F: CircuitField, const M: usize, const A: usize> ScannerVec<F, M, A> {
    /// Returns the (start, end) positions of the payload in the buffer.
    ///
    /// # Cost
    ///
    /// Free: the value was computed during construction and cached.
    pub fn get_limits(&self) -> &(AssignedNative<F>, AssignedNative<F>) {
        &self.limits
    }

    /// Returns the per-element padding flags (1 = filler, 0 = payload).
    ///
    /// # Cost
    ///
    /// Free: the value was computed during construction and cached.
    pub fn padding_flags(&self) -> &[AssignedBit<F>; M] {
        &self.padding_flags
    }

    /// Returns the effective length of the payload.
    ///
    /// # Cost
    ///
    /// Free: the value was computed and constrained during construction and
    /// cached.
    pub fn len(&self) -> &AssignedNative<F> {
        &self.length
    }
}

impl<F: CircuitField, const M: usize, const A: usize> From<ScannerVec<F, M, A>>
    for AssignedVector<F, AssignedNative<F>, M, A>
{
    fn from(value: ScannerVec<F, M, A>) -> Self {
        AssignedVector {
            buffer: value.buffer,
            len: value.length,
        }
    }
}

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord,
{
    /// Assigns a variable-length byte vector as a [`ScannerVec`].
    ///
    /// The input bytes are assigned as [`AssignedByte`]s (range-checked to
    /// `[0, 255]`), promoted to [`AssignedNative`] elements, and filler
    /// positions are constrained to [`ALPHABET_MAX_SIZE`] in-circuit.
    pub fn assign_scanner_vec<const M: usize, const A: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<u8>>,
    ) -> Result<ScannerVec<F, M, A>, Error> {
        let byte_vec: AssignedVector<F, AssignedByte<F>, M, A> =
            self.vector_gadget.assign_with_filler(layouter, value, None)?;
        self.scanner_vec_from_byte_vec(layouter, byte_vec)
    }

    /// Builds a [`ScannerVec`] from a slice of already-assigned bytes.
    /// The bytes are placed into an `M`-sized buffer with filler padding,
    /// and the length is assigned and range-checked. Delegates to
    /// [`scanner_vec_from_byte_vec`](`Self::scanner_vec_from_byte_vec`).
    pub fn scanner_vec_from_assigned<const M: usize, const A: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<ScannerVec<F, M, A>, Error> {
        assert!(M >= A && A > 0 && M.is_multiple_of(A));
        assert!(bytes.len() <= M);

        // Build the padded buffer: filler | payload | filler, aligned to A. The filler
        // can be anything, it will be replaced during the call to
        // `scanner_vec_from_byte_vec` below anyway.
        let lims = crate::vec::vector::get_lims::<M, A>(bytes.len());
        let filler: AssignedByte<F> = if let Some(b) = bytes.first() {
            b.clone()
        } else {
            self.native_gadget.assign(layouter, Value::known(0u8))?
        };
        let mut buffer: Vec<AssignedByte<F>> = vec![filler; M];
        buffer[lims].clone_from_slice(bytes);
        let buffer: [AssignedByte<F>; M] = buffer.try_into().unwrap();

        let len = self.native_gadget.assign_lower_than_fixed(
            layouter,
            Value::known(F::from(bytes.len() as u64)),
            &(M + 1).into(),
        )?;
        let vec = AssignedVector { buffer, len };
        self.scanner_vec_from_byte_vec(layouter, vec)
    }

    /// Converts an existing [`AssignedVector`] of [`AssignedByte`]s into a
    /// [`ScannerVec`], constraining filler positions to [`ALPHABET_MAX_SIZE`]
    /// and anchoring the length.
    ///
    /// The input elements are already range-checked (they are
    /// [`AssignedByte`]s). This function computes padding flags and constrains
    /// fillers via [`select`](`ControlFlowInstructions::select`).
    pub fn scanner_vec_from_byte_vec<const M: usize, const A: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        vec: AssignedVector<F, AssignedByte<F>, M, A>,
    ) -> Result<ScannerVec<F, M, A>, Error> {
        // Compute padding flags and limits in one call.
        let (padding_flags, limits) = self.vector_gadget.padding_flag(layouter, &vec)?;

        // Constrain filler positions to ALPHABET_MAX_SIZE.
        let filler =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;
        let buffer: [AssignedNative<F>; M] = (vec.buffer.iter().zip(padding_flags.iter()))
            .map(|(elem, is_padding)| {
                let native_elem = AssignedNative::from(elem);
                self.native_gadget.select(layouter, is_padding, &filler, &native_elem)
            })
            .collect::<Result<Vec<_>, Error>>()?
            .try_into()
            .expect("Length mismatch in ScannerVec buffer");

        Ok(ScannerVec {
            length: vec.len,
            buffer,
            limits,
            padding_flags,
        })
    }
}

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

//! Substring verification via packed lookup arguments.
//!
//! Each `(index, byte)` pair is packed into a single field element
//! `index * (ALPHABET_MAX_SIZE + 1) + byte` (see
//! [`ScannerChip::index_and_pack_sequence`]). Because indexes start at 1, zero
//! is never a valid packed value and can safely be used for padding.
//!
//! Calls to [`ScannerChip::check_bytes`] are deferred and grouped by
//! `sequence` argument in the [`SequenceCache`](super::SequenceCache). At
//! synthesis end, [`ScannerChip::finalise_substring_checks`] drains the
//! cache, packs both table and query entries, builds a row plan, and assigns
//! the region.

use itertools::Itertools;
use midnight_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::Error,
};
use num_bigint::BigUint;

use super::{ScannerChip, NB_SUBSTRING_COLS, PARSING_MAX_LEN_BITS};
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions, RangeCheckInstructions},
    parsing::scanner::{Sequence, ALPHABET_MAX_SIZE},
    types::AssignedByte,
    CircuitField,
};

/// Structure of assigned cells for verifying substring checks.
type SubstringCheckLayout<F> = Vec<[Sequence<F>; NB_SUBSTRING_COLS]>;

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    F: CircuitField + Ord,
{
    /// Asserts that `sub` is a contiguous subsequence of `sequence` starting at
    /// index `idx` (0-indexed). In practice, this function queues the call
    /// (grouping those with the same `sequence` argument) for batch
    /// finalisation in `Self::finalise_substring_checks`.
    ///
    /// # Cost
    ///
    /// The cost of one call is of the order of `|sequence| + |sub|` rows.
    /// Due to caching, multiple calls with the same `sequence` argument only
    /// pay the `sequence`-related cost once. Up to `SUBSTRING_PARALLELISM`
    /// calls with different `sequence` arguments share the same rows through
    /// parallel lookups.
    ///
    /// # Range check
    ///
    /// The starting index is range-checked (`idx < 2^PARSING_MAX_LEN_BITS`)
    /// so that the packed lookup value `(idx + i) * (ALPHABET_MAX_SIZE + 1) +
    /// byte` is injective over the field.
    pub fn check_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedByte<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedByte<F>],
    ) -> Result<(), Error> {
        let sequence: Sequence<F> = sequence.iter().map(AssignedNative::from).collect();
        let sub: Sequence<F> = sub.iter().map(AssignedNative::from).collect();
        self.check_subsequence(layouter, &sequence, idx, &sub)
    }

    /// Generic version of `check_bytes`. Cannot be exposed publicly because
    /// it is unsound without range-checks on the elements of `sequence` and
    /// `sub` (they are packed with indexes, so values outside `[0, 255]`
    /// would break injectivity).
    fn check_subsequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        if sub.is_empty() {
            // The circuit logic will assume `sub` is not empty for padding purposes, hence
            // handling it separately.
            return Ok(());
        }
        // Range-check idx to ensure packing injectivity.
        self.native_gadget.assert_lower_than_fixed(
            layouter,
            idx,
            &(BigUint::from(1u8) << PARSING_MAX_LEN_BITS),
        )?;

        self.sequence_cache
            .borrow_mut()
            .entry(sequence.to_vec())
            .and_modify(|(calls, len)| {
                *len += sub.len();
                calls.push((idx.clone(), sub.to_vec()))
            })
            .or_insert_with(|| (vec![(idx.clone(), sub.to_vec())], sub.len()));

        Ok(())
    }
}


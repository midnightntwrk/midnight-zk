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

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    F: CircuitField,
{
    /// Packs a sequence of assigned bytes into indexed field elements:
    /// `packed[i] = (start_idx + i) * (ALPHABET_MAX_SIZE + 1) +
    /// byte[i]`
    fn index_and_pack_sequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        start_idx: &AssignedNative<F>,
    ) -> Result<Sequence<F>, Error> {
        let shift = F::from(ALPHABET_MAX_SIZE as u64 + 1);
        (sequence.iter().enumerate())
            .map(|(i, byte)| {
                let constant = F::from(i as u64);
                self.native_gadget.linear_combination(
                    layouter,
                    &[(shift, start_idx.clone()), (F::ONE, byte.clone())],
                    constant * shift,
                )
            })
            .collect()
    }

    /// Drains the sequence cache, sorts entries by decreasing sequence length
    /// (then decreasing cumulative sub length), and packs query entries with
    /// their index. Returns one `(packed_sequence, flattened_packed_subs)` per
    /// unique sequence. Each sequences and subs have been padded and organised
    /// so that it only remains to assign them in circuit.
    fn index_and_pack_calls(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<SubstringCheckLayout<F>, Error> {
        let mut calls: Vec<_> = self.sequence_cache.borrow_mut().drain().collect();
        calls.sort_by(|a, b| b.0.len().cmp(&a.0.len()).then(b.1 .1.cmp(&a.1 .1)));
        if calls.is_empty() {
            // Ensures we can access the last element of `calls` without panicking.
            return Ok(vec![]);
        }

        // Padding tables with a value that cannot be a valid byte.
        let sequence_padding: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;

        let mut layout: SubstringCheckLayout<F> = Vec::with_capacity(calls.len());
        for (sequence, (indexes_and_subs, len)) in calls {
            let region_size = sequence.len().max(len);
            let mut padded_sequence: Sequence<F> = sequence.to_vec();
            padded_sequence.resize(region_size, sequence_padding.clone());
            let subs_packed: Sequence<F> = (indexes_and_subs.iter())
                .map(|(idx, sub)| self.index_and_pack_sequence(layouter, sub, idx))
                .collect::<Result<Vec<Sequence<F>>, _>>()?
                .into_iter()
                .flatten()
                .collect();
            // Padding by repeating the first element, which never panics
            // since `check_subsequence` rejects empty `sub` arguments.
            let mut padded_subs_packed = subs_packed.clone();
            padded_subs_packed.resize(region_size, subs_packed[0].clone());
            layout.push([padded_sequence, padded_subs_packed]);
        }
        Ok(layout)
    }

    /// Assigns a single row of the substring region.
    fn assign_substring_row(
        &self,
        region: &mut Region<'_, F>,
        lookups: &[AssignedNative<F>; NB_SUBSTRING_COLS],
        offset: usize,
        index: usize,
        tag: usize,
    ) -> Result<(), Error> {
        self.config.q_substring.enable(region, offset)?;
        region.assign_fixed(
            || "substring check (index)",
            self.config.index_col,
            offset,
            || Value::known(F::from(index as u64)),
        )?;
        region.assign_fixed(
            || "substring check (tag)",
            self.config.tag_col,
            offset,
            || Value::known(F::from(tag as u64)),
        )?;
        lookups[0].copy_advice(
            || format!("substring check (table {offset})"),
            region,
            self.config.state_col,
            offset,
        )?;
        lookups[1].copy_advice(
            || format!("substring check (query {offset})"),
            region,
            self.config.letter_col,
            offset,
        )?;
        Ok(())
    }

    /// Finalises all deferred `check_bytes` calls. Called from
    /// `ComposableChip::load` at the end of circuit synthesis.
    ///
    /// The sequence cache is drained and each unique sequence, together with
    /// all its associated `(idx, sub)` pairs, is packed into indexed field
    /// elements. The packed entries are then chunked into groups of
    /// `SUBSTRING_PARALLELISM` (each group assigned a fresh non-zero tag) and
    /// laid out row by row:
    ///
    /// - **sel=ON rows**: contribute table entries (packed sequence values) and
    ///   carry queries (packed sub values). Shorter sequences within a chunk
    ///   are zero-padded, which adds `(tag, 0)` to the lookup table.
    /// - **sel=OFF rows** (if subs overflow): carry remaining queries, which
    ///   are still verified against the same tag's table entries.
    ///
    /// Each chunk contains one extra sel=ON row beyond the longest sequence,
    /// guaranteeing that `(tag, 0)` is always in the table so that
    /// zero-padded queries always pass.
    pub(super) fn finalise_substring_checks(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        // Pack all cached calls into indexed field elements.
        let packed_calls = self.index_and_pack_calls(layouter)?;

        // Build the row layout and assign in a single region.
        layouter.assign_region(
            || "substring checks",
            |mut region| {
                let mut offset = 1;
                for (tag, parallel_calls) in packed_calls.iter().enumerate() {
                    for row in 0..parallel_calls[0].len() {
                        let lookups = core::array::from_fn(|col| parallel_calls[col][row].clone());
                        self.assign_substring_row(&mut region, &lookups, offset, row, tag + 1)?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}


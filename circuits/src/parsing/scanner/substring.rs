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

//! Substring verification using dynamic lookups.

use std::hash::Hash;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use super::ScannerChip;
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    types::AssignedByte,
};

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: PrimeField + Ord,
{
    /// Asserts that `sub` is a contiguous subsequence of `sequence` starting at
    /// index `idx` (0-indexed). More efficient than extracting the subsequence
    /// with `fetch_bytes` and asserting equality with `sub`.
    pub fn check_subsequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        // Check if the sequence is already cached; if not, allocate a fresh tag
        // and copy the sequence into the tag/byte columns.
        let seq_key = sequence.to_vec();
        let cached_tag = self.sequence_cache.borrow().get(&seq_key).copied();
        let tag = if let Some(t) = cached_tag {
            F::from(t)
        } else {
            let new_tag = {
                let mut counter = self.substring_tag_counter.borrow_mut();
                let t = *counter;
                *counter += 1;
                t
            };
            self.sequence_cache.borrow_mut().insert(seq_key, new_tag);
            let tag = F::from(new_tag);

            // Precompute all `sequence` indices.
            let seq_indices: Vec<AssignedNative<F>> = (0..sequence.len() as u64)
                .map(|i| self.native_gadget.assign_fixed(layouter, F::from(i)))
                .collect::<Result<_, Error>>()?;

            // Copy sequence into the tag/byte columns (only on first use).
            layouter.assign_region(
                || "substring sequence table",
                |mut region| {
                    for ((offset, byte), offset_assigned) in
                        sequence.iter().enumerate().zip(seq_indices.iter())
                    {
                        region.assign_fixed(
                            || format!("sequence tag {}", offset),
                            self.config.substring_tag_col,
                            offset,
                            || Value::known(tag),
                        )?;
                        offset_assigned.copy_advice(
                            || format!("sequence index {}", offset),
                            &mut region,
                            self.config.index_col,
                            offset,
                        )?;
                        byte.copy_advice(
                            || format!("sequence byte {}", offset),
                            &mut region,
                            self.config.byte_col,
                            offset,
                        )?;
                    }
                    Ok(())
                },
            )?;

            tag
        };

        // Precompute all `sub` indices.
        let sub_indices = (sub.iter().enumerate())
            .map(|(i, _)| self.native_gadget.add_constant(layouter, idx, F::from(i as u64)))
            .collect::<Result<Vec<_>, Error>>()?;

        // Assign `sub` as lookup rows (selector ON) with the (possibly cached) tag.
        layouter.assign_region(
            || "substring lookup",
            |mut region| {
                for (offset, (byte, idx)) in sub.iter().zip(sub_indices.iter()).enumerate() {
                    self.config.q_substring.enable(&mut region, offset)?;

                    region.assign_fixed(
                        || format!("sub tag {}", offset),
                        self.config.substring_tag_col,
                        offset,
                        || Value::known(tag),
                    )?;
                    idx.copy_advice(
                        || format!("sub index {}", offset),
                        &mut region,
                        self.config.index_col,
                        offset,
                    )?;
                    byte.copy_advice(
                        || format!("sub byte {}", offset),
                        &mut region,
                        self.config.byte_col,
                        offset,
                    )?;
                }

                Ok(())
            },
        )
    }

    /// Wrapper of `check_subsequence` for `AssignedByte` inputs. More efficient
    /// than using `fetch_bytes` and asserting equality with `sub`.
    pub fn check_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedByte<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedByte<F>],
    ) -> Result<(), Error> {
        let sequence: Vec<AssignedNative<F>> = sequence.iter().map(AssignedNative::from).collect();
        let sub: Vec<AssignedNative<F>> = sub.iter().map(AssignedNative::from).collect();
        self.check_subsequence(layouter, &sequence, idx, &sub)
    }
}

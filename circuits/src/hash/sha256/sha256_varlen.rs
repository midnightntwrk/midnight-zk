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

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use super::{sha256_chip::IV, Sha256Chip};
use crate::{
    field::{
        decomposition::chip::P2RDecompositionChip, AssignedBounded, AssignedNative, NativeChip,
        NativeGadget,
    },
    hash::sha256::{
        sha256_chip::ROUND_CONSTANTS,
        types::{AssignedPlain, CompressionState},
    },
    instructions::{
        ArithInstructions, AssignmentInstructions, BinaryInstructions, ComparisonInstructions,
        ControlFlowInstructions, DecompositionInstructions, DivisionInstructions,
        EqualityInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedByte},
    vec::AssignedVector,
};

/// Gadget for SHA256 with variable-length input.
#[derive(Clone, Debug)]
pub struct VarLenSha256Gadget<F: PrimeField> {
    pub(super) sha256chip: Sha256Chip<F>,
}

impl<F: PrimeField> VarLenSha256Gadget<F> {
    fn ng(&self) -> &NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>> {
        &self.sha256chip.native_gadget
    }
}

impl<F> VarLenSha256Gadget<F>
where
    F: PrimeField,
{
    // Returns the length of the final chunk and if this length needs an extra block
    // or not. If len=0, then the final block length is 0 and no extra block is
    // needed. Otherwise, the final block length is in (0, 64]. Due to the
    // allowing of value 64, the returned `AssignedBounded` has bound 2^7.
    // An extra block is needed if final_block_len >= (64 - 8).
    fn final_block_len<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        len: &AssignedNative<F>, // Total input length in bytes.
    ) -> Result<(AssignedBounded<F>, AssignedBit<F>), Error> {
        let ng = &self.ng();

        // Final block length in [0, 64].
        let final_block_len = {
            // Final block length in [0, 64).
            let fb_len = ng.rem(layouter, len, 64u64.into(), Some(M.into()))?;

            // The final block is full if len % 64 = 0; and the input length is not 0.
            let full_final_block = {
                let len_is_zero = ng.is_zero(layouter, len)?;
                let fb_is_zero = ng.is_zero(layouter, &fb_len)?;
                ng.xor(layouter, &[len_is_zero, fb_is_zero])?
            };

            let max_block_len = ng.assign_fixed(layouter, F::from(64u64))?;
            ng.select(layouter, &full_final_block, &max_block_len, &fb_len)?
        };

        // Limit on the final block length: If exceeded, an extra block will be needed.
        let len_lim: u64 = 56;

        // Need to use 7 since we use the range (0, 64], instead of [0, 64);
        let final_block_len = ng.bounded_of_element(layouter, 7, &final_block_len)?;
        let not_extra = ng.lower_than_fixed(layouter, &final_block_len, F::from(len_lim))?;
        let extra = ng.not(layouter, &not_extra)?;

        Ok((final_block_len, extra))
    }

    // TODO Maybe move this somewhere else (VectorGadget? )
    // Inserts `elem` in position `idx` of `array`.
    // Idx values outside [0, L) are allowed but, in thta case, the array will
    // remain unchanged.
    fn insert_in_array<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        idx: &AssignedNative<F>,
        array: &mut [AssignedByte<F>; L],
        elem: AssignedByte<F>,
    ) -> Result<(), Error> {
        let ng = self.ng();
        for (i, item) in array.iter_mut().enumerate() {
            let at_idx = ng.is_equal_to_fixed(layouter, idx, F::from(i as u64))?;
            *item = ng.select(layouter, &at_idx, &elem, item)?;
        }
        Ok(())
    }

    // Given 2 slices of AssignedBytes, merges them into 1 by selecting the
    // first `len` bytes of the fist chunk, and the remaining bytes of second
    // chunk.
    // If `len` >= L, the output will be equal to `chunk_1`. If `len` = 0,
    // the output will be equal to `chunk_2`.
    fn merge_chunks<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        chunk_1: &[AssignedByte<F>; L],
        chunk_2: &[AssignedByte<F>; L],
        len: &AssignedNative<F>,
    ) -> Result<[AssignedByte<F>; L], Error> {
        let ng = &self.ng();
        let mut first_chunk: AssignedBit<F> = ng.assign_fixed(layouter, true)?;
        let result = chunk_1
            .iter()
            .zip(chunk_2.iter())
            .enumerate()
            .map(|(i, (a, b))| {
                let switch = ng.is_equal_to_fixed(layouter, len, F::from(i as u64))?;
                first_chunk = ng.xor(layouter, &[first_chunk.clone(), switch])?;
                ng.select(layouter, &first_chunk, a, b)
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(result.try_into().expect("Chunks of equal length."))
    }

    // Computes the last 2 blocks of padding.
    fn compute_padding(
        &self,
        layouter: &mut impl Layouter<F>,
        input_len: &AssignedNative<F>,        // in bytes
        final_chunk_len: &AssignedBounded<F>, // in bytes
        final_chunk: &[AssignedByte<F>; 64],
        extra_block: &AssignedBit<F>,
    ) -> Result<[AssignedByte<F>; 2 * 64], Error> {
        let ng = self.ng();
        let zero: AssignedByte<F> = ng.assign_fixed(layouter, 0u8)?;

        let final_chunk_len = &ng.element_of_bounded(layouter, final_chunk_len)?;
        let not_extra_block: AssignedNative<F> = ng.not(layouter, extra_block)?.into();

        let block_1 = {
            let zeros = &vec![zero.clone(); 64].try_into().unwrap();

            // We merge unconditionally in block_1 because:
            //  * if the extra block is needed, final will be placed here.
            //  * if no extra block is needed, this block will not update the state.
            self.merge_chunks(layouter, final_chunk, zeros, final_chunk_len)?
        };

        let block_2 = {
            let zeros = &vec![zero; 56].try_into().unwrap();
            let final_chunk: &[_; 56] = (&final_chunk[..56]).try_into().unwrap();

            let cond_len = ng.mul(layouter, final_chunk_len, &not_extra_block, None)?;
            // We merge conditionally here. If an extra block is needed
            // `cond_len` = 0 and the merge will result in the original block_2.
            self.merge_chunks(layouter, final_chunk, zeros, &cond_len)?
        };

        let len_bytes = {
            let len_in_bits = ng.mul_by_constant(layouter, input_len, F::from(8u64))?;
            ng.assigned_to_be_bytes(layouter, &len_in_bits, Some(8usize))?
        };

        let mut padding = [block_1.as_slice(), &block_2, &len_bytes].concat();

        // Place the 1 (0x80) at the end of the input data.
        {
            let one: AssignedByte<F> = ng.assign_fixed(layouter, 0x80)?;

            // The valid range for idx in block_1 || block_2 is [56, 120].
            // We offset with -56 since the array we will be indexing contains only
            // the positions where the 1 may be placed.
            let idx = {
                // idx = final_chunk_len + 64 * not_extra_block - 56
                ng.linear_combination(
                    layouter,
                    &[
                        (F::ONE, final_chunk_len.clone()),
                        (F::from(64u64), not_extra_block),
                    ],
                    -F::from(56u64),
                )?
            };

            self.insert_in_array::<64>(
                layouter,
                &idx,
                (&mut padding[56..120]).try_into().unwrap(),
                one,
            )?;
        }

        Ok(padding.try_into().unwrap())
    }
}

impl<F: PrimeField> VarLenSha256Gadget<F> {
    // Updates the `state` with `block`.
    fn update_state(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &CompressionState<F>,
        block: &[AssignedByte<F>; 64],
    ) -> Result<CompressionState<F>, Error> {
        let sha256 = &self.sha256chip;
        let block = sha256.block_from_bytes(layouter, block)?;
        let message_blocks = sha256.message_schedule(layouter, &block)?;
        let mut compression_state = state.clone();
        for i in 0..64 {
            compression_state = sha256.compression_round(
                layouter,
                &compression_state,
                ROUND_CONSTANTS[i],
                &message_blocks[i],
            )?;
        }
        state.add(sha256, layouter, &compression_state)
    }

    // Updates the `state` with `block` if `update` is true.
    // Otherwise returns the input state unchanged.
    fn conditional_update_state(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &CompressionState<F>,
        block: &[AssignedByte<F>; 64],
        update: &AssignedBit<F>,
    ) -> Result<CompressionState<F>, Error> {
        let new_state = self.update_state(layouter, state, block)?;

        // State gets updated if updating is enabled.
        CompressionState::select(layouter, self.ng(), update, &new_state, state)
    }

    /// In-circuit variable input-length SHA256 computation, the protagonist of
    /// this chip.
    pub(super) fn sha256_varlen<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &AssignedVector<F, AssignedByte<F>, M, 64>,
    ) -> Result<[AssignedPlain<F, 32>; 8], Error> {
        let ng = self.ng();

        // Compute the block where the effective data starts.
        let (final_block_len, extra_block) = self.final_block_len::<M>(layouter, &inputs.len)?;

        // Length of the input rounded up to the chunk size.
        let rounded_len = {
            let fc_len = ng.element_of_bounded(layouter, &final_block_len)?;
            let is_zero = ng.is_zero(layouter, &fc_len)?;
            let len_round = ng.sub(layouter, &inputs.len, &fc_len)?;
            let len_round_extra = ng.add_constant(layouter, &len_round, F::from(64u64))?;
            ng.select(layouter, &is_zero, &len_round, &len_round_extra)
        }?;

        // Variable that signals the start of effective data in the input buffer
        // and activates the update mechanism in the hash internal state.
        let mut updating: AssignedBit<F> = ng.assign_fixed(layouter, false)?;

        let mut state = CompressionState::<F>::fixed(layouter, ng, IV)?;

        // Process input in chunks.
        let mut block_iter = inputs.buffer.chunks_exact(64);
        let mut block = block_iter.next().expect("At least one block.");

        // Conditional update loop. Stops 1 chunk before the end.
        for i in 0..(M / 64) - 1 {
            // Have we arrived to the start of the input to be hashed.
            let b = ng.is_equal_to_fixed(layouter, &rounded_len, F::from((M - (i * 64)) as u64))?;

            // Switch on the updating variable if we got to the start.
            updating = ng.xor(layouter, &[b, updating])?;

            // Compute the (potential) new state.
            let block_array = block.try_into().unwrap();
            state = self.conditional_update_state(layouter, &state, block_array, &updating)?;

            block = block_iter.next().expect("One more block.");
        }

        assert!(block_iter.next().is_none());

        let final_block: &[_; 64] = block.try_into().unwrap();

        // Padding
        let padding_data = self.compute_padding(
            layouter,
            &inputs.len,
            &final_block_len,
            final_block,
            &extra_block,
        )?;

        let final_block_1 = (&padding_data[..64]).try_into().unwrap();
        let final_block_2 = (&padding_data[64..]).try_into().unwrap();

        state = self.conditional_update_state(layouter, &state, final_block_1, &extra_block)?;
        state = self.update_state(layouter, &state, final_block_2)?;

        Ok(state.plain())
    }
}

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> FromScratch<F> for VarLenSha256Gadget<F> {
    type Config = <Sha256Chip<F> as FromScratch<F>>::Config;

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            sha256chip: Sha256Chip::new_from_scratch(config),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        Sha256Chip::configure_from_scratch(meta, instance_columns)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.sha256chip.load_from_scratch(layouter)
    }
}

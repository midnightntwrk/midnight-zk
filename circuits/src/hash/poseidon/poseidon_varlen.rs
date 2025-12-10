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

use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use super::{
    constants::{PoseidonField, RATE},
    AssignedRegister, PoseidonChip,
};
use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    hash::poseidon::{constants::WIDTH, PoseidonState},
    instructions::{
        ArithInstructions, AssignmentInstructions, BinaryInstructions, ControlFlowInstructions,
        DivisionInstructions, EqualityInstructions, RangeCheckInstructions, SpongeCPU,
        ZeroInstructions,
    },
    types::{AssignedBit, AssignedNative, AssignedVector},
};

type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// Gadget for variable-length Poseidon operations.
#[derive(Clone, Debug)]
pub struct VarLenPoseidonGadget<F: PoseidonField> {
    poseidon_chip: PoseidonChip<F>,
    native_gadget: NG<F>,
}

impl<F: PoseidonField> VarLenPoseidonGadget<F> {
    /// Create a new variable-length Poseidon gadget from its dependencies.
    pub fn new(poseidon_chip: &PoseidonChip<F>, native_gadget: &NG<F>) -> Self {
        Self {
            poseidon_chip: poseidon_chip.clone(),
            native_gadget: native_gadget.clone(),
        }
    }
}

// Inherit SpongeCPU trait from PoseidonChip.
impl<F: PoseidonField> SpongeCPU<F, F> for VarLenPoseidonGadget<F> {
    type StateCPU = PoseidonState<F>;

    fn init(input_len: Option<usize>) -> Self::StateCPU {
        <PoseidonChip<F> as SpongeCPU<F, F>>::init(input_len)
    }

    fn absorb(state: &mut Self::StateCPU, inputs: &[F]) {
        <PoseidonChip<F> as SpongeCPU<F, F>>::absorb(state, inputs)
    }

    fn squeeze(state: &mut Self::StateCPU) -> F {
        <PoseidonChip<F> as SpongeCPU<F, F>>::squeeze(state)
    }
}

// Implement auxiliary functions for variable length hashing.
impl<F: PoseidonField> VarLenPoseidonGadget<F> {
    /// Updates the internal state `register` with the `chunk` if `update` is
    /// true. Otherwise, `register` is left unchanged.
    /// `chunk` is expected to have length `RATE`.
    fn cond_update(
        &self,
        layouter: &mut impl Layouter<F>,
        register: &AssignedRegister<F>,
        chunk: &[AssignedNative<F>],
        update: &AssignedBit<F>,
    ) -> Result<AssignedRegister<F>, Error> {
        assert_eq!(chunk.len(), RATE);
        let mut result = register.clone();

        // Perform the update and store it in result.
        for (entry, value) in result.iter_mut().zip(chunk.iter()) {
            *entry = self.native_gadget.add(layouter, entry, value)?;
        }
        result = self.poseidon_chip.permutation(layouter, &result)?;

        // Select the updated version or the original input according to `update`.
        for (register, result) in register.iter().zip(result.iter_mut()) {
            *result = self.native_gadget.select(layouter, update, result, register)?;
        }

        Ok(result)
    }

    /// Format the last chunk of data so it is zeroed after the effictive payload.
    /// Given chunk = [x1, x2, ..., xn], with n = RATE, returns [x1, ...,
    /// x_{offset-1}, 0, ..., 0]. If offset = 0, the chunk is returned
    /// intact.
    fn constrain_last_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        chunk: &[AssignedNative<F>],
        offset: &AssignedNative<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert_eq!(chunk.len(), RATE);
        let ng = &self.native_gadget;

        let mut chunk = chunk.to_vec();
        let zero = ng.assign_fixed(layouter, F::ZERO)?;
        let mut after_data: AssignedBit<F> = ng.assign_fixed(layouter, false)?;
        for (i, elem) in chunk.iter_mut().enumerate().skip(1) {
            let b = ng.is_equal_to_fixed(layouter, offset, F::from(i as u64))?;
            after_data = ng.xor(layouter, &[b, after_data])?;
            *elem = ng.select(layouter, &after_data, &zero, elem)?;
        }

        Ok(chunk)
    }

    /// Hashes the variable-length vector inputs.
    ///
    /// # Panics
    ///
    /// If `MAX_LEN` is not a multiple of `RATE`.
    pub(crate) fn poseidon_varlen<const MAX_LEN: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, AssignedNative<F>, MAX_LEN, RATE>,
    ) -> Result<AssignedNative<F>, Error> {
        assert_eq!(MAX_LEN % RATE, 0);
        let ng = &self.native_gadget;
        let len = &input.len;

        ng.assert_lower_than_fixed(layouter, len, &BigUint::from(MAX_LEN + 1))?;

        // Initialize state.
        let zero = ng.assign_fixed(layouter, F::ZERO)?;
        let mut register: AssignedRegister<F> = vec![zero; WIDTH].try_into().unwrap();
        register[RATE] = len.clone();

        // Flag that will signal when the hash input starts and chunks need to be
        // effectively processed and update the state.
        let mut updating: AssignedBit<F> = self.native_gadget.assign_fixed(layouter, false)?;

        // Last chunk length.
        let last_chunk_len =
            self.native_gadget.rem(layouter, len, RATE.into(), Some(MAX_LEN.into()))?;

        // Length of the input rounded up to the chunk size (RATE).
        let rounded_len = {
            let is_zero = ng.is_zero(layouter, &last_chunk_len)?;
            let len_round = ng.sub(layouter, len, &last_chunk_len)?;
            let len_round_extra = ng.add_constant(layouter, &len_round, F::from(RATE as u64))?;
            ng.select(layouter, &is_zero, &len_round, &len_round_extra)
        }?;

        for (i, chunk) in input.buffer.chunks(RATE).enumerate() {
            // Determines when we have arrived at the first chunk of input.
            let b = ng.is_equal_to_fixed(
                layouter,
                &rounded_len,
                F::from((MAX_LEN - (i * RATE)) as u64),
            )?;
            updating = ng.xor(layouter, &[b, updating])?;

            register = if i == MAX_LEN / RATE {
                // Constrain vector filler values in the last chunk.
                let last_chunk = self.constrain_last_chunk(layouter, chunk, &last_chunk_len)?;
                self.cond_update(layouter, &register, &last_chunk, &updating)?
            } else {
                self.cond_update(layouter, &register, chunk, &updating)?
            }
        }
        Ok(register[0].clone())
    }
}

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;

#[cfg(any(test, feature = "testing"))]
use crate::field::decomposition::chip::P2RDecompositionConfig;

#[cfg(any(test, feature = "testing"))]
impl<F: PoseidonField> FromScratch<F> for VarLenPoseidonGadget<F> {
    type Config = (
        P2RDecompositionConfig,
        <PoseidonChip<F> as FromScratch<F>>::Config,
    );

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            native_gadget: NativeGadget::new_from_scratch(&config.0),
            poseidon_chip: PoseidonChip::new_from_scratch(&config.1),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let native_config = NG::<F>::configure_from_scratch(meta, instance_columns);
        let poseidon_config = PoseidonChip::configure_from_scratch(meta, instance_columns);
        (native_config, poseidon_config)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)?;
        self.poseidon_chip.load_from_scratch(layouter)
    }
}

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

use std::marker::PhantomData;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance};

use crate::hash::sha256::{BITS_PER_SHA_BLOCK, BITS_PER_WORD, BLOCK_BYTE_SIZE};

mod compression;
mod gates;
mod message_schedule;
mod spread_table;

use compression::*;
use gates::*;
use message_schedule::*;
use spread_table::*;

use crate::hash::sha256::{
    instructions::Sha256Instructions, AssignedBits, AssignedBlockWord, BlockWord, BITS_PER_BYTE,
    BYTES_PER_WORD,
};

/// Configuration for a [`Table16Chip`].
#[derive(Clone, Debug)]
pub struct Table16Config {
    lookup: SpreadTableConfig,
    message_schedule: MessageScheduleConfig,
    compression: CompressionConfig,
}

/// A chip that implements SHA-256 with a maximum lookup table size of $2^16$.
#[derive(Clone, Debug)]
pub struct Table16Chip<F: PrimeField> {
    config: Table16Config,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Chip<F> for Table16Chip<F> {
    type Config = Table16Config;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> FromScratch<F> for Table16Chip<F> {
    type Config = Table16Config;

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        _instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        Table16Chip::configure(meta)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        Table16Chip::load(config.clone(), layouter).expect("Failed to load table")
    }
}

impl<F: PrimeField> Table16Chip<F> {
    /// Reconstructs this chip from the given config.
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Chip configuration from cap gate
    pub fn configure_with_columns(
        meta: &mut ConstraintSystem<F>,
        advice_columns: &[Column<Advice>; 7],
    ) -> <Self as Chip<F>>::Config {
        // currently we need 10 columns for sha
        // we can share for the moment up to 7
        // TODO: Look into sharing the lookup columns as well

        let advice_columns = advice_columns.iter().collect::<Vec<_>>();

        let message_schedule = advice_columns[0];

        let extras = [
            *advice_columns[1],
            *advice_columns[2],
            *advice_columns[3],
            *advice_columns[4],
            *advice_columns[5],
            *advice_columns[6],
        ];

        // - Three new advice columns to interact with the lookup table.
        let input_tag = meta.advice_column();
        let input_dense = meta.advice_column();
        let input_spread = meta.advice_column();

        let lookup = SpreadTableChip::configure(meta, input_tag, input_dense, input_spread);
        let lookup_inputs = lookup.input.clone();

        // Rename these here for ease of matching the gates to the specification.
        let _a_0 = lookup_inputs.tag;
        let a_1 = lookup_inputs.dense;
        let a_2 = lookup_inputs.spread;
        let a_3 = extras[0];
        let a_4 = extras[1];
        let a_5 = message_schedule;
        let a_6 = extras[2];
        let a_7 = extras[3];
        let a_8 = extras[4];
        let _a_9 = extras[5];

        // Add all advice columns to permutation
        for column in [a_1, a_2, a_3, a_4, *a_5, a_6, a_7, a_8].iter() {
            meta.enable_equality(*column);
        }

        // Add all advice columns to permutation
        for column in [a_1, a_2, *a_5].iter() {
            meta.enable_equality(*column);
        }

        let compression =
            CompressionConfig::configure(meta, lookup_inputs.clone(), *message_schedule, extras);

        let message_schedule =
            MessageScheduleConfig::configure(meta, lookup_inputs, *message_schedule, extras);

        Table16Config {
            lookup,
            message_schedule,
            compression,
        }
    }

    /// Configures a circuit to include this chip.
    pub fn configure(meta: &mut ConstraintSystem<F>) -> <Self as Chip<F>>::Config {
        // Columns required by this chip:
        let message_schedule = meta.advice_column();
        let extras = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        // - Three advice columns to interact with the lookup table.
        let input_tag = meta.advice_column();
        let input_dense = meta.advice_column();
        let input_spread = meta.advice_column();

        let lookup = SpreadTableChip::configure(meta, input_tag, input_dense, input_spread);
        let lookup_inputs = lookup.input.clone();

        // Rename these here for ease of matching the gates to the specification.
        let _a_0 = lookup_inputs.tag;
        let a_1 = lookup_inputs.dense;
        let a_2 = lookup_inputs.spread;
        let a_3 = extras[0];
        let a_4 = extras[1];
        let a_5 = message_schedule;
        let a_6 = extras[2];
        let a_7 = extras[3];
        let a_8 = extras[4];
        let _a_9 = extras[5];

        // fixed column to add the iv and other constants that are copyconstrained
        let iv = meta.fixed_column();

        // Add all advice columns to permutation
        for column in [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8].iter() {
            meta.enable_equality(*column);
        }
        meta.enable_constant(iv);

        let compression =
            CompressionConfig::configure(meta, lookup_inputs.clone(), message_schedule, extras);

        let message_schedule =
            MessageScheduleConfig::configure(meta, lookup_inputs, message_schedule, extras);

        Table16Config {
            lookup,
            message_schedule,
            compression,
        }
    }

    /// Loads the lookup table required by this chip into the circuit.
    pub fn load(config: Table16Config, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        SpreadTableChip::load(config.lookup, layouter)
    }
}

impl<F: PrimeField> Sha256Instructions<F> for Table16Chip<F> {
    type State = State<F>;

    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error> {
        self.config().compression.initialize_with_iv(layouter)
    }

    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error> {
        self.config()
            .compression
            .initialize_with_state(layouter, init_state.clone())
    }

    // Given an initialized state and an input message block, compress the
    // message block and return the final state.
    // The values of the blockword array are re-assigned to satisfy the satisfy the
    // message schedule constraint and then they are copy constrainted to ensure
    // the newly assigned values are equal to the ones given as input
    //
    // Panics if `input` contains Assign values that do not convert to u32 (i.e. the
    // field element representation should be exactly 4 bytes, the rest being zero).
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [AssignedBlockWord<F>; super::BLOCK_SIZE],
    ) -> Result<Self::State, Error> {
        let config = self.config();
        let lookup_inputs = &config.lookup.input;

        // extract the values that need to be input in `process`
        let input_values = input
            .clone()
            .map(|word| BlockWord::from_field_value(word.value().map(|&v| v)));
        // the output is well formed due to the constraints in `process`. The w values
        // are therefore rangechecked

        // assign the values for message schedule. Note that at these point the values
        // used are arbitrary and not-connected to the assigned input
        let (w, w_halves) = config.message_schedule.process(layouter, input_values)?;

        // here we make the connection with the input. Specifically, we assert that the
        // first 16 values returned by message schedule that represent the 16
        // 32-bit input words to be absorbed are equal with the assigned input
        // as field elements
        layouter.assign_region(
            || "Assert equality of input",
            |mut region| {
                for (w, input) in w[0..16].iter().zip(input.iter()) {
                    // Since w is already rangechecked, input is also in the appropriate range
                    region.constrain_equal(w.0.cell(), input.cell())?;
                }
                Ok(())
            },
        )?;

        config
            .compression
            .compress(layouter, initialized_state.clone(), w_halves, lookup_inputs)
    }

    /// Returns the padding for the given state.
    fn compute_padding(&self, hash_input_length: u64) -> Vec<u8> {
        // currently we only support adding 8bit words
        assert_eq!(hash_input_length as usize % BITS_PER_BYTE, 0);

        let remaining_bits = BITS_PER_SHA_BLOCK - (hash_input_length as usize % BITS_PER_SHA_BLOCK);

        // if the padded word with 1 is in the last two blockwords we need a new block
        let remaining_bytes = if remaining_bits <= 2 * BITS_PER_WORD {
            BLOCK_BYTE_SIZE + remaining_bits / BITS_PER_BYTE
        } else {
            remaining_bits / BITS_PER_BYTE
        };

        // assign the padding
        let one = 0x80; // 1 << 8
        let zeroes = (1..remaining_bytes - BYTES_PER_WORD)
            .map(|_| (0u8))
            .collect::<Vec<_>>();
        let length = (hash_input_length as u32).to_be_bytes();

        let mut padding_vector: Vec<_> = Vec::with_capacity(zeroes.len() + 5);
        padding_vector.push(one);
        padding_vector.extend(zeroes);
        padding_vector.extend(length);

        padding_vector
    }

    // Given an initialized state, the final message block and the total
    // input size, compress the message block and return the final state.
    fn apply_padding(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        block1: Option<[AssignedBlockWord<F>; super::BLOCK_SIZE]>,
        block2: [AssignedBlockWord<F>; super::BLOCK_SIZE],
        _length: u64,
    ) -> Result<Self::State, Error> {
        let config = self.config();
        let lookup_inputs = &config.lookup.input;

        // process first block if present
        let mut state = initialized_state.clone();
        let (w1, w1_halves);
        if let Some(block1) = block1.clone() {
            // message_schedule
            (w1, w1_halves) = config.message_schedule.process(
                layouter,
                block1
                    .clone()
                    .map(|word| BlockWord::from_field_value(word.value().cloned())),
            )?;

            // we assert the first 16 values returned by message schedule are equal with the
            // assigned block1 as field elements, no matter they are padded or
            // not.
            layouter.assign_region(
                || "Assert equality of input",
                |mut region| {
                    for (w, input) in w1[0..16].iter().zip(block1.iter()) {
                        region.constrain_equal(w.0.cell(), input.cell())?;
                    }
                    Ok(())
                },
            )?;

            // compress
            state =
                config
                    .compression
                    .compress(layouter, state, w1_halves.clone(), lookup_inputs)?;

            // initialize state
            state = self
                .config()
                .compression
                .initialize_with_state(layouter, state.clone())?;
        }
        // process second_block
        let (w2, w2_halves) = config.message_schedule.process(
            layouter,
            block2
                .clone()
                .map(|word| BlockWord::from_field_value(word.value().cloned())),
        )?;

        // we assert the first 16 values returned by message schedule are equal with the
        // assigned block2 as field elements, no matter they are padded or not.
        layouter.assign_region(
            || "Assert equality of input",
            |mut region| {
                for (w, input) in w2[0..16].iter().zip(block2.iter()) {
                    region.constrain_equal(w.0.cell(), input.cell())?;
                }
                Ok(())
            },
        )?;

        // compress
        state = config
            .compression
            .compress(layouter, state, w2_halves.clone(), lookup_inputs)?;

        // initialize state
        state = self
            .config()
            .compression
            .initialize_with_state(layouter, state.clone())?;

        Ok(state)
    }

    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[AssignedBlockWord<F>; super::DIGEST_SIZE], Error> {
        // Copy the dense forms of the state variable chunks down to this gate.
        // Reconstruct the 32-bit dense words.
        self.config().compression.digest(layouter, state.clone())
    }
}

/// Common assignment patterns used by Table16 regions.
trait Table16Assignment<F: PrimeField> {
    /// Assign cells for general spread computation used in sigma, ch, ch_neg,
    /// maj gates
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn assign_spread_outputs(
        &self,
        region: &mut Region<'_, F>,
        lookup: &SpreadInputs,
        a_3: Column<Advice>,
        row: usize,
        r_0_even: Value<[bool; 16]>,
        r_0_odd: Value<[bool; 16]>,
        r_1_even: Value<[bool; 16]>,
        r_1_odd: Value<[bool; 16]>,
    ) -> Result<
        (
            (AssignedBits<16, F>, AssignedBits<16, F>),
            (AssignedBits<16, F>, AssignedBits<16, F>),
        ),
        Error,
    > {
        // Lookup R_0^{even}, R_0^{odd}, R_1^{even}, R_1^{odd}
        let r_0_even = SpreadVar::with_lookup(
            region,
            lookup,
            row - 1,
            r_0_even.map(SpreadWord::<16, 32>::new),
        )?;
        let r_0_odd =
            SpreadVar::with_lookup(region, lookup, row, r_0_odd.map(SpreadWord::<16, 32>::new))?;
        let r_1_even = SpreadVar::with_lookup(
            region,
            lookup,
            row + 1,
            r_1_even.map(SpreadWord::<16, 32>::new),
        )?;
        let r_1_odd = SpreadVar::with_lookup(
            region,
            lookup,
            row + 2,
            r_1_odd.map(SpreadWord::<16, 32>::new),
        )?;

        // Assign and copy R_1^{odd}
        r_1_odd
            .spread
            .copy_advice(|| "Assign and copy R_1^{odd}", region, a_3, row)?;

        Ok((
            (r_0_even.dense, r_1_even.dense),
            (r_0_odd.dense, r_1_odd.dense),
        ))
    }

    /// Assign outputs of sigma gates
    #[allow(clippy::too_many_arguments)]
    fn assign_sigma_outputs(
        &self,
        region: &mut Region<'_, F>,
        lookup: &SpreadInputs,
        a_3: Column<Advice>,
        row: usize,
        r_0_even: Value<[bool; 16]>,
        r_0_odd: Value<[bool; 16]>,
        r_1_even: Value<[bool; 16]>,
        r_1_odd: Value<[bool; 16]>,
    ) -> Result<(AssignedBits<16, F>, AssignedBits<16, F>), Error> {
        let (even, _odd) = self.assign_spread_outputs(
            region, lookup, a_3, row, r_0_even, r_0_odd, r_1_even, r_1_odd,
        )?;

        Ok(even)
    }
}

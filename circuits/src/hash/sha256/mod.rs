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

//! The [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234

use std::{convert::TryInto, fmt::Debug, ops::Deref};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Any, Column, Error},
    utils::rational::Rational,
};
use sha2::Digest;
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    midnight_proofs::plonk::{ConstraintSystem, Instance},
};

mod instructions;
mod table11;
mod table16;
mod util;

pub use instructions::Sha256Instructions;
pub use table11::{Table11Chip, Table11Config, NB_TABLE11_ADVICE_COLS, NB_TABLE11_FIXED_COLS};
pub use table16::{Table16Chip, Table16Config};

use crate::{
    field::{decomposition::instructions::CoreDecompositionInstructions, NativeChip, NativeGadget},
    hash::sha256::util::{i2lebsp, lebs2ip, spread_bits},
    instructions::{
        hash::HashCPU, AssignmentInstructions, DecompositionInstructions, HashInstructions,
    },
    types::{AssignedByte, AssignedNative},
};

/// The size of a SHA-256 block, in 32-bit words.
pub(crate) const BLOCK_SIZE: usize = 16;

/// The number of bytes that constitutes a word.
pub(crate) const BYTES_PER_WORD: usize = 4;

/// The size of a SHA-256 block, in bytes.
pub(crate) const BLOCK_BYTE_SIZE: usize = BLOCK_SIZE * BYTES_PER_WORD;

/// The size of a SHA-256 digest, in 32-bit words.
pub(crate) const DIGEST_SIZE: usize = 8;

/// number of bits per byte
pub(crate) const BITS_PER_BYTE: usize = 8;

/// number of bits per word
pub(crate) const BITS_PER_WORD: usize = BITS_PER_BYTE * BYTES_PER_WORD;

/// the bits consumed in each sha compression
pub(crate) const BITS_PER_SHA_BLOCK: usize = BLOCK_SIZE * BYTES_PER_WORD * BITS_PER_BYTE;

const ROUNDS: usize = 64;
const STATE: usize = 8;

#[allow(clippy::unreadable_literal)]
pub(crate) const ROUND_CONSTANTS: [u32; ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const IV: [u32; STATE] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

#[derive(Clone, Copy, Debug, Default)]
/// A word in a `Sha256` message block.
pub struct BlockWord(Value<u32>);

/// An assigned block in a `Sha256` message block.
pub(super) type AssignedBlockWord<F> = AssignedNative<F>;

// TODO: Better error handling
impl BlockWord {
    // function to convert a field value to a BlockWord.
    // NOTE: We make the assumption that the field representation type [F::Rerp] is
    // in little endian
    // NOTE: the function will fail if it is given as input a field value that is
    // represented in more than 4 bytes or equivalently does not "map" to a u32
    // value.
    fn from_field_value<F: PrimeField>(value_f: Value<F>) -> Self {
        // convert the inner value from f to u32
        let value_blockword = value_f.map(|f| {
            // representation of field in bytes
            let f_repr = f.to_repr();
            // first four bytes should have the u32 representation
            // the rest should be zero
            let (bytes, zeros) = f_repr.as_ref().split_at(4);
            // check that a valid field value was given
            if zeros.iter().any(|&el| el != 0) {
                panic!()
            }
            // compute the u32 from the bytes
            let result: [u8; 4] = bytes
                .iter()
                .map(|b| b.to_owned())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            u32::from_le_bytes(result)
        });
        // wrap around Blockword
        BlockWord(value_blockword)
    }
}

#[derive(Clone, Debug)]
/// Little-endian bits (up to 64 bits)
pub struct Bits<const LEN: usize>([bool; LEN]);

impl<const LEN: usize> Bits<LEN> {
    fn spread<const SPREAD: usize>(&self) -> [bool; SPREAD] {
        spread_bits(self.0)
    }
}

impl<const LEN: usize> std::ops::Deref for Bits<LEN> {
    type Target = [bool; LEN];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const LEN: usize> From<[bool; LEN]> for Bits<LEN> {
    fn from(bits: [bool; LEN]) -> Self {
        Self(bits)
    }
}

impl<const LEN: usize> From<&Bits<LEN>> for [bool; LEN] {
    fn from(bits: &Bits<LEN>) -> Self {
        bits.0
    }
}

impl<const LEN: usize, F: PrimeField> From<&Bits<LEN>> for Rational<F> {
    fn from(bits: &Bits<LEN>) -> Rational<F> {
        assert!(LEN <= 64);
        F::from(lebs2ip(&bits.0)).into()
    }
}

impl From<&Bits<16>> for u16 {
    fn from(bits: &Bits<16>) -> u16 {
        lebs2ip(&bits.0) as u16
    }
}

impl From<u16> for Bits<16> {
    fn from(int: u16) -> Bits<16> {
        Bits(i2lebsp::<16>(int.into()))
    }
}

impl From<&Bits<32>> for u32 {
    fn from(bits: &Bits<32>) -> u32 {
        lebs2ip(&bits.0) as u32
    }
}

impl From<u32> for Bits<32> {
    fn from(int: u32) -> Bits<32> {
        Bits(i2lebsp::<32>(int.into()))
    }
}

#[derive(Clone, Debug)]
pub(crate) struct AssignedBits<const LEN: usize, F: PrimeField>(AssignedCell<Bits<LEN>, F>);

impl<const LEN: usize, F: PrimeField> Deref for AssignedBits<LEN, F> {
    type Target = AssignedCell<Bits<LEN>, F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const LEN: usize, F: PrimeField> AssignedBits<LEN, F> {
    pub(crate) fn assign_bits<A, AR, T: TryInto<[bool; LEN]> + Debug + Clone>(
        region: &mut Region<'_, F>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        value: Value<T>,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
        <T as TryInto<[bool; LEN]>>::Error: Debug,
    {
        let value: Value<[bool; LEN]> = value.map(|v| v.try_into().unwrap());
        let value: Value<Bits<LEN>> = value.map(|v| v.into());

        let column: Column<Any> = column.into();
        match column.column_type() {
            Any::Advice(_) => {
                region.assign_advice(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            Any::Fixed => {
                region.assign_fixed(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            _ => panic!("Cannot assign to instance column"),
        }
        .map(AssignedBits)
    }
}

impl<const LEN: usize, F: PrimeField> AssignedBits<LEN, F> {
    pub(crate) fn assign_bits_fixed<A, AR, T: TryInto<[bool; LEN]> + Debug + Clone>(
        region: &mut Region<'_, F>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        fixed_value: T,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
        <T as TryInto<[bool; LEN]>>::Error: Debug,
    {
        let fixed_value: [bool; LEN] = fixed_value.try_into().unwrap();
        let fixed_value: Bits<LEN> = fixed_value.into();

        let column: Column<Any> = column.into();
        match column.column_type() {
            Any::Advice(_) => region.assign_advice_from_constant(
                annotation,
                column.try_into().unwrap(),
                offset,
                fixed_value,
            ),
            _ => panic!("Cannot assign to instance or fixed column"),
        }
        .map(AssignedBits)
    }
}

impl<F: PrimeField> AssignedBits<16, F> {
    fn value_u16(&self) -> Value<u16> {
        self.value().map(|v| v.into())
    }

    fn assign<A, AR>(
        region: &mut Region<'_, F>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        value: Value<u16>,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        let column: Column<Any> = column.into();
        let value: Value<Bits<16>> = value.map(|v| v.into());
        match column.column_type() {
            Any::Advice(_) => {
                region.assign_advice(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            Any::Fixed => {
                region.assign_fixed(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            _ => panic!("Cannot assign to instance column"),
        }
        .map(AssignedBits)
    }
}

impl<F: PrimeField> AssignedBits<32, F> {
    fn value_u32(&self) -> Value<u32> {
        self.value().map(|v| v.into())
    }

    fn assign<A, AR>(
        region: &mut Region<'_, F>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        value: Value<u32>,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        let column: Column<Any> = column.into();
        let value: Value<Bits<32>> = value.map(|v| v.into());
        match column.column_type() {
            Any::Advice(_) => {
                region.assign_advice(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            Any::Fixed => {
                region.assign_fixed(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            _ => panic!("Cannot assign to instance column"),
        }
        .map(AssignedBits)
    }
}

/// The output of a SHA-256 circuit invocation.
#[derive(Debug, Clone)]
pub struct Sha256Digest<BlockWord: Clone>([BlockWord; DIGEST_SIZE]);

impl<BlockWord: Clone> Sha256Digest<BlockWord> {
    /// Gets the inner assigned cells from the Sha256Digest
    pub fn get_assigned_blockwords(&self) -> [BlockWord; DIGEST_SIZE] {
        self.0.clone()
    }
}

/// A gadget that constrains a SHA-256 invocation. This interface works with
/// in/out consisting of [BlockWord]s. To use an interface with in/out
/// consisting of bytes, refer to [ZkStdLib](crate::compact_std_lib::ZkStdLib)
/// docs.
///
/// The gadget is parametrised with a chip that implements [Sha256Instructions].
/// There are currently two implementations of the instruction set:
/// * [Table16Chip] This chip uses a lookup table of size `2**16`. This means
///   that all circuits instantiating this chip will be at least `2**17` rows,
///   as we need to padd the circuit to provide ZK. This chip achieves a SHA
///   digest in 2099 rows.
/// * [Table11Chip] This chip uses a lookup table of size `2**12` (including
///   ZK). You can find more information of this chip in its corresponding
///   documentation. This chip achieves a SHA digest in 4319 rows, meaning that
///   the table is no longer the bottle neck.
#[derive(Debug, Clone)]
pub struct Sha256<F, CS, D>
where
    F: PrimeField,
    CS: Sha256Instructions<F>,
    D: CoreDecompositionInstructions<F>,
{
    chip: CS,
    // used for assignments and decompositions
    native_gadget: NativeGadget<F, D, NativeChip<F>>,
}

impl<F, Sha256Chip, D> Sha256<F, Sha256Chip, D>
where
    F: PrimeField,
    Sha256Chip: Sha256Instructions<F> + Clone,
    D: CoreDecompositionInstructions<F>,
{
    /// Create a new hasher instance.
    pub fn new(
        chip: Sha256Chip,
        native_gadget: NativeGadget<F, D, NativeChip<F>>,
    ) -> Result<Self, Error> {
        Ok(Sha256 {
            chip,
            native_gadget,
        })
    }

    fn byte_block_to_block_word(
        &self,
        layouter: &mut impl Layouter<F>,
        block: [AssignedByte<F>; 64],
    ) -> Result<[AssignedBlockWord<F>; 16], Error> {
        Ok(block
            .chunks_exact(4)
            .map(|word_bytes| {
                self.native_gadget
                    .assigned_from_be_bytes(layouter, word_bytes)
            })
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap())
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>> FromScratch<F>
    for Sha256<F, H, D>
where
    F: PrimeField,
    H: Sha256Instructions<F> + FromScratch<F>,
    NativeGadget<F, D, NativeChip<F>>: FromScratch<F>,
{
    type Config = (
        <H as FromScratch<F>>::Config,
        <NativeGadget<F, D, NativeChip<F>> as FromScratch<F>>::Config,
    );

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            chip: <H as FromScratch<F>>::new_from_scratch(&config.0),
            native_gadget: NativeGadget::new_from_scratch(&config.1),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        (
            <H as FromScratch<F>>::configure_from_scratch(meta, instance_columns),
            NativeGadget::configure_from_scratch(meta, instance_columns),
        )
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        <H as FromScratch<F>>::load_from_scratch(layouter, &config.0);
        NativeGadget::load_from_scratch(layouter, &config.1);
    }
}

impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>>
    HashCPU<u8, [u8; 32]> for Sha256<F, H, D>
{
    fn hash(inputs: &[u8]) -> [u8; 32] {
        let output = sha2::Sha256::digest(inputs);
        output.into_iter().collect::<Vec<_>>().try_into().unwrap()
    }
}

impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>>
    HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Sha256<F, H, D>
{
    fn hash(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        let mut state = self.chip.initialization_vector(layouter)?;

        // Process any additional full blocks.
        let mut chunks_iter = inputs.chunks_exact(BLOCK_BYTE_SIZE);

        for chunk in &mut chunks_iter {
            // Convert the current byte block into blockwords
            let cur_block =
                self.byte_block_to_block_word(layouter, chunk.to_vec().try_into().unwrap())?;

            // compress the first full block in the current update
            state = self.chip.compress(layouter, &state, cur_block)?;
            state = self.chip.initialization(layouter, &state)?;
        }

        let mut final_chunk = chunks_iter.remainder().to_vec();

        // the total length of useful data hashed;
        // this valued will need to be placed in the last two words of the final block
        let input_length = inputs.len() * BITS_PER_BYTE;

        let padding_data = self.chip.compute_padding(input_length as u64);
        let assigned_padding = padding_data
            .iter()
            .map(|byte| self.native_gadget.assign_fixed(layouter, *byte))
            .collect::<Result<Vec<_>, Error>>()?;

        final_chunk.extend(assigned_padding);
        assert!(final_chunk.len() == BLOCK_BYTE_SIZE || final_chunk.len() == 2 * BLOCK_BYTE_SIZE);

        let (block1, block2) = if final_chunk.len() > BLOCK_BYTE_SIZE {
            let block1 = self.byte_block_to_block_word(
                layouter,
                final_chunk[..BLOCK_BYTE_SIZE]
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;

            let block2 = self.byte_block_to_block_word(
                layouter,
                final_chunk[BLOCK_BYTE_SIZE..]
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;
            (Some(block1), block2)
        } else {
            let block2 = self.byte_block_to_block_word(
                layouter,
                final_chunk[..]
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;
            (None, block2)
        };

        state = self
            .chip
            .apply_padding(layouter, &state, block1, block2, input_length as u64)?;

        // digest to get the final result
        let sha_output_words = self.chip.digest(layouter, &state).map(Sha256Digest)?;

        // convert the assigned output to bytes
        let assigned_digest_bytes = sha_output_words
            .get_assigned_blockwords()
            .iter()
            .map(|word| {
                self.native_gadget
                    .assigned_to_be_bytes(layouter, word, Some(4))
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        Ok(assigned_digest_bytes.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use blstrs::Fq as Scalar;

    use crate::{
        field::{decomposition::chip::P2RDecompositionChip, NativeGadget},
        hash::sha256::{Sha256, Table11Chip, Table16Chip},
        instructions::hash::tests::test_hash,
        types::AssignedByte,
    };

    #[test]
    fn test_sha_hash() {
        test_hash::<
            Scalar,
            AssignedByte<Scalar>,
            [AssignedByte<Scalar>; 32],
            Sha256<Scalar, Table11Chip<_>, P2RDecompositionChip<Scalar>>,
            NativeGadget<Scalar, _, _>,
        >(true, "ShaTable11", 16);

        test_hash::<
            Scalar,
            AssignedByte<Scalar>,
            [AssignedByte<Scalar>; 32],
            Sha256<Scalar, Table16Chip<_>, P2RDecompositionChip<Scalar>>,
            NativeGadget<Scalar, _, _>,
        >(true, "ShaTable16", 17)
    }
}

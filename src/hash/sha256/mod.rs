//! The [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234

use std::{cmp::min, convert::TryInto, fmt::Debug, ops::Deref};

use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Any, Assigned, Column, ErrorFront as Error},
};
use sha2::Digest;
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    halo2_proofs::plonk::{ConstraintSystem, Instance},
};

mod instructions;
mod table11;
mod table16;
mod util;

pub use instructions::Sha256Instructions;
pub use table11::{Table11Chip, Table11Config};
pub use table16::{Table16Chip, Table16Config};

use crate::{
    field::{decomposition::instructions::CoreDecompositionInstructions, NativeChip, NativeGadget},
    hash::sha256::util::{i2lebsp, lebs2ip, spread_bits},
    instructions::{
        hash::HashCPU, sponge::SpongeCPU, AssignmentInstructions, DecompositionInstructions,
        HashInstructions, SpongeInstructions,
    },
    types::{AssignedByte, AssignedNative, Byte, InnerValue},
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

impl<const LEN: usize, F: PrimeField> From<&Bits<LEN>> for Assigned<F> {
    fn from(bits: &Bits<LEN>) -> Assigned<F> {
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
            Any::Advice => {
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
            Any::Advice => region.assign_advice_from_constant(
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
            Any::Advice => {
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
            Any::Advice => {
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

#[derive(Clone, Debug)]
/// State used for SHA hash function
pub struct ShaState<F: PrimeField, H: Sha256Instructions<F>> {
    state: H::State,
    msg_length: usize,
    current_block: Vec<AssignedByte<F>>,
}

impl<T: InnerValue> InnerValue for [T; 32] {
    type Element = [T::Element; 32];

    fn value(&self) -> Value<Self::Element> {
        let val = Value::from_iter(self.iter().map(|val| val.value()));
        // We know sizes will match due to the type system. The problem is
        // that the type Value is not right enough.
        val.map(|v: Vec<T::Element>| v.try_into().unwrap())
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
        instance_column: &Column<Instance>,
    ) -> Self::Config {
        (
            <H as FromScratch<F>>::configure_from_scratch(meta, instance_column),
            NativeGadget::configure_from_scratch(meta, instance_column),
        )
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        <H as FromScratch<F>>::load_from_scratch(layouter, &config.0);
        NativeGadget::load_from_scratch(layouter, &config.1);
    }
}

impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>>
    SpongeCPU<Byte, [Byte; 32]> for Sha256<F, H, D>
{
    type StateCPU = sha2::Sha256;

    fn init() -> Self::StateCPU {
        sha2::Sha256::new()
    }

    fn absorb(state: &mut Self::StateCPU, input: &[Byte]) {
        state.update(input.iter().map(|byte| byte.0).collect::<Vec<_>>());
    }

    fn squeeze(state: &mut Self::StateCPU) -> [Byte; 32] {
        let output = state.clone().finalize();
        let output_byte = output.into_iter().map(Byte).collect::<Vec<_>>();

        *state = <Self as SpongeCPU<Byte, [Byte; 32]>>::init();
        <Self as SpongeCPU<Byte, [Byte; 32]>>::absorb(state, &output_byte);

        output_byte.try_into().unwrap()
    }
}

impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>>
    SpongeInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Sha256<F, H, D>
{
    type State = ShaState<F, H>;

    fn init(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error> {
        let state = self.chip.initialization_vector(layouter)?;
        let msg_length = 0;
        let current_block = Vec::with_capacity(BLOCK_BYTE_SIZE);

        Ok(ShaState {
            state,
            msg_length,
            current_block,
        })
    }

    fn absorb(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
        input: &[AssignedByte<F>],
    ) -> Result<(), Error> {
        state.msg_length += input.len() * BITS_PER_BYTE;

        // Fill the current block, if possible.
        let remaining = BLOCK_BYTE_SIZE - state.current_block.len();
        let (l, r) = input.split_at(min(remaining, input.len()));
        state.current_block.extend_from_slice(l);
        let data = r;

        // If we still don't have a full block, we are done.
        if state.current_block.len() < BLOCK_BYTE_SIZE {
            return Ok(());
        }

        // Convert the current byte block into blockwords
        let cur_block = self
            .byte_block_to_block_word(layouter, state.current_block.clone().try_into().unwrap())?;

        // compress the first full block in the current update
        state.state = self.chip.compress(layouter, &state.state, cur_block)?;
        state.state = self.chip.initialization(layouter, &state.state)?;
        state.current_block.clear();

        // Process any additional full blocks.
        let mut chunks_iter = data.chunks_exact(BLOCK_BYTE_SIZE);
        for chunk in &mut chunks_iter {
            let block_word = self.byte_block_to_block_word(
                layouter,
                chunk
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;
            state.state = self.chip.compress(layouter, &state.state, block_word)?;
            state.state = self.chip.initialization(layouter, &state.state)?;
        }

        // Cache the remaining partial block, if any.
        let rem = chunks_iter.remainder();
        state.current_block.extend_from_slice(rem);

        Ok(())
    }

    fn squeeze(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
    ) -> Result<[AssignedByte<F>; 32], Error> {
        // the total length of useful data hashed;
        // this valued will need to be placed in the last two words of the final block
        let input_length = state.msg_length;

        let padding_data = self.chip.compute_padding(input_length as u64);
        let assigned_padding = padding_data
            .iter()
            .map(|byte| self.native_gadget.assign_fixed(layouter, Byte(*byte)))
            .collect::<Result<Vec<_>, Error>>()?;

        state.current_block.extend_from_slice(&assigned_padding);
        assert!(
            state.current_block.len() == BLOCK_BYTE_SIZE
                || state.current_block.len() == 2 * BLOCK_BYTE_SIZE
        );

        let (block1, block2) = if state.current_block.len() > BLOCK_BYTE_SIZE {
            let block1 = self.byte_block_to_block_word(
                layouter,
                state.current_block[..BLOCK_BYTE_SIZE]
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;

            let block2 = self.byte_block_to_block_word(
                layouter,
                state.current_block[BLOCK_BYTE_SIZE..]
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;
            (Some(block1), block2)
        } else {
            let block2 = self.byte_block_to_block_word(
                layouter,
                state.current_block[..]
                    .to_vec()
                    .try_into()
                    .expect("chunk.len() == BLOCK_BYTE_SIZE"),
            )?;
            (None, block2)
        };

        state.state =
            self.chip
                .apply_padding(layouter, &state.state, block1, block2, input_length as u64)?;

        // digest to get the final result
        let sha_output_words = self.chip.digest(layouter, &state.state).map(Sha256Digest)?;

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

        *state = self.init(layouter)?;
        self.absorb(layouter, state, &assigned_digest_bytes)?;

        Ok(assigned_digest_bytes.try_into().unwrap())
    }
}

impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>>
    HashCPU<Byte, [Byte; 32]> for Sha256<F, H, D>
{
}

impl<F: PrimeField, H: Sha256Instructions<F>, D: CoreDecompositionInstructions<F>>
    HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Sha256<F, H, D>
{
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use blstrs::Scalar;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use sha2::Digest;

    use super::*;
    use crate::{
        field::{
            decomposition::chip::{P2RDecompositionChip, P2RDecompositionConfig},
            NativeGadget,
        },
        hash::sha256::{Sha256, Table11Chip, Table16Chip},
        instructions::{sponge::tests::test_sponge, AssignmentInstructions, SpongeInstructions},
        types::{AssignedByte, Byte, InnerValue},
        utils::circuit_modeling::circuit_to_json,
    };

    #[test]
    fn test_sha_sponge() {
        test_sponge::<
            Scalar,
            AssignedByte<Scalar>,
            [AssignedByte<Scalar>; 32],
            Sha256<Scalar, Table11Chip<_>, P2RDecompositionChip<Scalar>>,
            NativeGadget<Scalar, _, _>,
        >(false, "ShaTable11", 17);

        test_sponge::<
            Scalar,
            AssignedByte<Scalar>,
            [AssignedByte<Scalar>; 32],
            Sha256<Scalar, Table16Chip<_>, P2RDecompositionChip<Scalar>>,
            NativeGadget<Scalar, _, _>,
        >(false, "ShaTable16", 17)
    }

    fn assert_hash_result<F: PrimeField>(input: &[u8], output: [AssignedByte<F>; 32]) {
        let hash_output = sha2::Sha256::digest(input);

        // NOTE: We make the assumption that F is represented in little endian
        for (idx, word) in output.iter().enumerate() {
            word.value()
                .assert_if_known(|digest_word| digest_word.0 == hash_output[idx]);
        }
    }
    #[derive(Default)]
    struct MyCircuit<H> {
        hash: PhantomData<H>,
    }

    impl<F: PrimeField, H: Sha256Instructions<F> + FromScratch<F>> Circuit<F> for MyCircuit<H> {
        type Config = (<H as FromScratch<F>>::Config, P2RDecompositionConfig);

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self { hash: PhantomData }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_column = meta.instance_column();
            let constant_column = meta.fixed_column();
            meta.enable_constant(constant_column);

            let native_config = NativeGadget::configure_from_scratch(meta, &instance_column);
            let sha_config = H::configure_from_scratch(meta, &instance_column);

            (sha_config, native_config)
        }
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            H::load_from_scratch(&mut layouter, &config.0.clone());
            let sha_chip = H::new_from_scratch(&config.0);

            NativeGadget::load_from_scratch(&mut layouter, &config.1);
            let native_gadget = NativeGadget::new_from_scratch(&config.1);

            let test_input = b"abcd";
            let test_input_values = test_input
                .iter()
                .map(|byte| Value::known(Byte(*byte)))
                .collect::<Vec<_>>();

            let assigned_input = native_gadget.assign_many(&mut layouter, &test_input_values)?;

            let hasher = Sha256::new(sha_chip, native_gadget)?;
            let mut state = hasher.init(&mut layouter)?;
            hasher.absorb(&mut layouter, &mut state, &assigned_input)?;
            let digest = hasher.squeeze(&mut layouter, &mut state)?;

            assert_hash_result(test_input, digest);

            Ok(())
        }
    }
    #[test]
    fn test_sha256_table16() {
        const K: u32 = 17;

        let circuit = MyCircuit {
            hash: PhantomData::<Table16Chip<Scalar>>,
        };

        let pi = vec![vec![]];

        let prover = MockProver::<Scalar>::run(K, &circuit, pi).expect("Failed to run mock prover");
        prover.assert_satisfied();

        assert!(prover.verify().is_ok());

        circuit_to_json::<Scalar>(K, "sha-table16", "hash", &[&[]], circuit);
    }

    #[test]
    fn test_sha256_table11() {
        const K: u32 = 13;

        let circuit = MyCircuit {
            hash: PhantomData::<Table11Chip<Scalar>>,
        };

        let pi = vec![vec![]];

        let prover = MockProver::<Scalar>::run(K, &circuit, pi).expect("Failed to run mock prover");
        prover.assert_satisfied();

        assert!(prover.verify().is_ok());

        circuit_to_json::<Scalar>(K, "sha-table11", "hash", &[&[]], circuit);
    }
}

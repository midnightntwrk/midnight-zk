use crate::{
    field::{
        decomposition::chip::P2RDecompositionChip, AssignedBounded, AssignedNative, NativeChip,
        NativeGadget,
    },
    hash::sha256::{
        sha256_chip::ROUND_CONSTANTS,
        types::{
            AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded, CompressionState, LimbsOfA,
            LimbsOfE,
        },
    },
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, BinaryInstructions,
        ComparisonInstructions, DecompositionInstructions, DivisionInstructions,
        EqualityInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedByte, InnerValue},
    vec::AssignedVector,
};
use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::instructions::ControlFlowInstructions;

use super::{sha256_chip::IV, Sha256Chip};

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
    // Returns the length of the final chunk and if this length needs an extra block or not.
    // If len=0, then the final block length is 0 and no extra block is needed.
    // Otherwise, the final block length is in (0, 64]. Due to the allowing of value 64, the
    // returned `AssignedBounded` has bound 2^7.
    // An extra block is needed if final_block_len >= (64 - 8).
    fn final_block_len<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        len: &AssignedNative<F>, // Total input length in bytes.
    ) -> Result<(AssignedBounded<F>, AssignedBit<F>), Error> {
        let ng = &self.ng();

        // Final block length in (0, 64].
        let final_block_len = {
            // Final block length in [0, 64).
            let (_, fb_len) = ng.div_rem(layouter, len, M as u32, 64 as u32)?;

            // The final block is full if len % 64 = 0; and the input length is not 0.
            let full_final_block = {
                let len_is_zero = ng.is_zero(layouter, len)?;
                let fb_is_zero = ng.is_zero(layouter, &fb_len)?;
                ng.xor(layouter, &[len_is_zero, fb_is_zero])?
            };

            let max_block_len = ng.assign_fixed(layouter, F::from(64 as u64))?;
            ng.select(layouter, &full_final_block, &max_block_len, &fb_len)?
        };

        // Limit on the final block length: If exceeded, an extra block will be needed.
        let len_lim: usize = 56;

        // Need to use 7 since we use the range (0, 64], instead of [0, 64);
        let final_block_len = ng.bounded_of_element(layouter, 7, &final_block_len)?;
        let not_extra = ng.lower_than_fixed(layouter, &final_block_len, F::from(len_lim as u64))?;
        let extra = ng.not(layouter, &not_extra)?;

        Ok((final_block_len, extra))
    }

    // Inserts `elem` in position `idx` of `array`.
    // Idx values outside [0, L) are allowed, but they array will remain unchanged.
    fn insert_in_array<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        idx: &AssignedNative<F>, // total input length in bytes
        array: &mut [AssignedByte<F>; L],
        elem: AssignedByte<F>,
    ) -> Result<(), Error> {
        let ng = self.ng();
        for i in 0..L {
            let at_idx = ng.is_equal_to_fixed(layouter, idx, F::from(i as u64))?;
            array[i] = ng.select(layouter, &at_idx, &elem, &array[i])?;
        }
        Ok(())
    }

    // Given 2 slices of AssignedBytes, merges them into 1 by selecting the
    // first `len` bytes of the fist chunk, and the remaining bytes of second
    // chunk.
    // If `len` >= L, the output will be equal to `chunk_1`.
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
        let final_chunk_len = &ng.element_of_bounded(layouter, final_chunk_len)?;

        let not_extra_block: AssignedNative<F> = ng.not(layouter, extra_block)?.into();

        let block_1 = {
            let block_1: Vec<AssignedByte<F>> = ng.assign_many_fixed(layouter, &vec![0u8; 64])?;
            let block_1 = &block_1.try_into().unwrap();

            // We merge unconditionally in block_1 because:
            //  * if the extra block is needed, final will be placed here.
            //  * if no extra block is needed, this block will not update the state.
            self.merge_chunks(layouter, final_chunk, block_1, final_chunk_len)?
        };

        let block_2 = {
            let block_2: Vec<AssignedByte<F>> = ng.assign_many_fixed(layouter, &vec![0u8; 60])?;
            let block_2 = &block_2.try_into().unwrap();
            let final_chunk: &[_; 60] = (&final_chunk[..60]).try_into().unwrap();

            let cond_len = ng.mul(layouter, final_chunk_len, &not_extra_block, None)?;
            // We merge conditionally here. If an extra block is needed
            // `cond_len` = 0 and the merge will result in the original block_2.
            self.merge_chunks(layouter, final_chunk, block_2, &cond_len)?
        };

        let len_bytes = {
            let len_in_bits = ng.mul_by_constant(layouter, input_len, F::from(8u64))?;
            ng.assigned_to_be_bytes(layouter, &len_in_bits, Some(4usize))?
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
                ng.add_and_mul(
                    layouter,
                    (F::ONE, final_chunk_len),
                    (F::from(64u64), &not_extra_block),
                    (F::ZERO, final_chunk_len),
                    -F::from(56u64),
                    F::ZERO,
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
        state.add(&sha256, layouter, &compression_state)
    }

    // Updates the `state` with `block` if `update` is true.
    // Otherwise returns the inputed state unchanged.
    fn conditional_update_state(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &CompressionState<F>,
        block: &[AssignedByte<F>; 64],
        update: &AssignedBit<F>,
    ) -> Result<CompressionState<F>, Error> {
        let new_state = self.update_state(layouter, state, block)?;

        // State gets updated if updating is enabled.
        self.select(layouter, &update, &new_state, &state)
    }

    /// In-circuit valriable SHA256 computation, the protagonist of this chip.
    pub fn sha256_varlen<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &AssignedVector<F, AssignedByte<F>, M, 64>,
    ) -> Result<[AssignedPlain<F, 32>; 8], Error> {
        assert_eq!(inputs.buffer.len(), M);
        assert_eq!(inputs.buffer.len() % 64, 0);

        let ng = self.ng();

        // Compute the block where the effective data starts.
        let (final_block_len, extra_block) = self.final_block_len::<M>(layouter, &inputs.len)?;

        // Length of the input rounded up to the chunk size.
        let rounded_len = {
            let fc_len = ng.element_of_bounded(layouter, &final_block_len)?;
            let is_zero = ng.is_zero(layouter, &fc_len)?;
            let len_round = ng.sub(layouter, &inputs.len, &fc_len)?;
            let len_round_extra = ng.add_constant(layouter, &len_round, F::from(64 as u64))?;
            ng.select(layouter, &is_zero, &len_round, &len_round_extra)
        }?;

        // Variable that signals the start of effective data in the input buffer
        // and activates the update mechanism in the hash internal state.
        let mut updating: AssignedBit<F> = ng.assign_fixed(layouter, false)?;

        // Initial state
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

        let final_block: &[_; 64] = (block.try_into()).unwrap();

        // Padding
        let padding_data = self.compute_padding(
            layouter,
            &inputs.len,
            &final_block_len,
            &final_block,
            &extra_block,
        )?;

        let final_block_1 = (&padding_data[..64]).try_into().unwrap();
        let final_block_2 = (&padding_data[64..]).try_into().unwrap();

        state = self.conditional_update_state(layouter, &state, final_block_1, &extra_block)?;
        state = self.update_state(layouter, &state, final_block_2)?;

        Ok(state.plain())
    }
}

// ----------------------------
/// InnerValue impl for Sha internal types.

// TODO We are using:
// type Element = F
// but it would be more accurate to use some bounded type like
// uint guaranteed to be in [0, 2^L)
impl<F: PrimeField, const L: usize> InnerValue for AssignedPlain<F, L> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.0.value().cloned()
    }
}

impl<F: PrimeField, const L: usize> InnerValue for AssignedSpreaded<F, L> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.0.value().cloned()
    }
}

impl<F: PrimeField, const L: usize> InnerValue for AssignedPlainSpreaded<F, L> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.plain.value() // plain and spreaded values are consistent.
    }
}

impl<F: PrimeField> InnerValue for LimbsOfA<F> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.combined.value()
    }
}

impl<F: PrimeField> InnerValue for LimbsOfE<F> {
    type Element = F;

    fn value(&self) -> Value<Self::Element> {
        self.combined.value()
    }
}

impl<F: PrimeField> InnerValue for CompressionState<F> {
    type Element = [F; 8];

    fn value(&self) -> Value<Self::Element> {
        let vals: Value<Vec<F>> = Value::from_iter([
            self.a.value(),
            self.b.value(),
            self.c.value(),
            self.d.value(),
            self.e.value(),
            self.f.value(),
            self.g.value(),
            self.h.value(),
        ]);
        vals.map(|v| v.try_into().unwrap())
    }
}

// ----------------------------
// AssertionInstruction implementation for internal types.

impl<F: PrimeField, const L: usize> AssertionInstructions<F, AssignedPlain<F, L>>
    for VarLenSha256Gadget<F>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        y: &AssignedPlain<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_equal(layouter, &x.0, &y.0)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        y: &AssignedPlain<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_not_equal(layouter, &x.0, &y.0)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        constant: <AssignedPlain<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng().assert_equal_to_fixed(layouter, &x.0, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlain<F, L>,
        constant: <AssignedPlain<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng()
            .assert_not_equal_to_fixed(layouter, &x.0, constant)
    }
}

impl<F: PrimeField, const L: usize> AssertionInstructions<F, AssignedSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        y: &AssignedSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_equal(layouter, &x.0, &y.0)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        y: &AssignedSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.ng().assert_not_equal(layouter, &x.0, &y.0)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        constant: <AssignedSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng().assert_equal_to_fixed(layouter, &x.0, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSpreaded<F, L>,
        constant: <AssignedSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.ng()
            .assert_not_equal_to_fixed(layouter, &x.0, constant)
    }
}

impl<F: PrimeField, const L: usize> AssertionInstructions<F, AssignedPlainSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        y: &AssignedPlainSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.plain, &y.plain)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        y: &AssignedPlainSpreaded<F, L>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.plain, &y.plain)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        constant: <AssignedPlainSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.plain, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedPlainSpreaded<F, L>,
        constant: <AssignedPlainSpreaded<F, L> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.plain, constant)
    }
}

impl<F: PrimeField> AssertionInstructions<F, LimbsOfA<F>> for VarLenSha256Gadget<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        y: &LimbsOfA<F>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        y: &LimbsOfA<F>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        constant: <LimbsOfA<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.combined, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfA<F>,
        constant: <LimbsOfA<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.combined, constant)
    }
}

impl<F: PrimeField> AssertionInstructions<F, LimbsOfE<F>> for VarLenSha256Gadget<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        y: &LimbsOfE<F>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        y: &LimbsOfE<F>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.combined, &y.combined)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        constant: <LimbsOfE<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.combined, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &LimbsOfE<F>,
        constant: <LimbsOfE<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.combined, constant)
    }
}

impl<F: PrimeField> AssertionInstructions<F, CompressionState<F>> for VarLenSha256Gadget<F> {
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        y: &CompressionState<F>,
    ) -> Result<(), Error> {
        // self.assert_equal(layouter, &x.a.combined.plain.0, &y.a.combined.plain.0)?;
        self.assert_equal(layouter, &x.a, &y.a)?;
        self.assert_equal(layouter, &x.b, &y.b)?;
        self.assert_equal(layouter, &x.c, &y.c)?;
        self.assert_equal(layouter, &x.d, &y.d)?;
        self.assert_equal(layouter, &x.e, &y.e)?;
        self.assert_equal(layouter, &x.f, &y.f)?;
        self.assert_equal(layouter, &x.g, &y.g)?;
        self.assert_equal(layouter, &x.h, &y.h)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        y: &CompressionState<F>,
    ) -> Result<(), Error> {
        self.assert_not_equal(layouter, &x.a, &y.a)?;
        self.assert_not_equal(layouter, &x.b, &y.b)?;
        self.assert_not_equal(layouter, &x.c, &y.c)?;
        self.assert_not_equal(layouter, &x.d, &y.d)?;
        self.assert_not_equal(layouter, &x.e, &y.e)?;
        self.assert_not_equal(layouter, &x.f, &y.f)?;
        self.assert_not_equal(layouter, &x.g, &y.g)?;
        self.assert_not_equal(layouter, &x.h, &y.h)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        constant: <CompressionState<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, &x.a, constant[0])?;
        self.assert_equal_to_fixed(layouter, &x.b, constant[1])?;
        self.assert_equal_to_fixed(layouter, &x.c, constant[2])?;
        self.assert_equal_to_fixed(layouter, &x.d, constant[3])?;
        self.assert_equal_to_fixed(layouter, &x.e, constant[4])?;
        self.assert_equal_to_fixed(layouter, &x.f, constant[5])?;
        self.assert_equal_to_fixed(layouter, &x.g, constant[6])?;
        self.assert_equal_to_fixed(layouter, &x.h, constant[7])
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &CompressionState<F>,
        constant: <CompressionState<F> as InnerValue>::Element,
    ) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, &x.a, constant[0])?;
        self.assert_not_equal_to_fixed(layouter, &x.b, constant[1])?;
        self.assert_not_equal_to_fixed(layouter, &x.c, constant[2])?;
        self.assert_not_equal_to_fixed(layouter, &x.d, constant[3])?;
        self.assert_not_equal_to_fixed(layouter, &x.e, constant[4])?;
        self.assert_not_equal_to_fixed(layouter, &x.f, constant[5])?;
        self.assert_not_equal_to_fixed(layouter, &x.g, constant[6])?;
        self.assert_not_equal_to_fixed(layouter, &x.h, constant[7])
    }
}

// Implementation of ControlFlowInstructions

impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedPlain<F, L>>
    for VarLenSha256Gadget<F>
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedPlain<F, L>,
        y: &AssignedPlain<F, L>,
    ) -> Result<AssignedPlain<F, L>, Error> {
        Ok(AssignedPlain(self.ng().select(layouter, cond, &x.0, &y.0)?))
    }
}

impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedSpreaded<F, L>,
        y: &AssignedSpreaded<F, L>,
    ) -> Result<AssignedSpreaded<F, L>, Error> {
        Ok(AssignedSpreaded(
            self.ng().select(layouter, cond, &x.0, &y.0)?,
        ))
    }
}

impl<F: PrimeField, const L: usize> ControlFlowInstructions<F, AssignedPlainSpreaded<F, L>>
    for VarLenSha256Gadget<F>
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedPlainSpreaded<F, L>,
        y: &AssignedPlainSpreaded<F, L>,
    ) -> Result<AssignedPlainSpreaded<F, L>, Error> {
        let plain = self.select(layouter, cond, &x.plain, &y.plain)?;
        let spreaded = self.select(layouter, cond, &x.spreaded, &y.spreaded)?;
        Ok(AssignedPlainSpreaded { plain, spreaded })
    }
}

impl<F: PrimeField> ControlFlowInstructions<F, LimbsOfA<F>> for VarLenSha256Gadget<F> {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &LimbsOfA<F>,
        y: &LimbsOfA<F>,
    ) -> Result<LimbsOfA<F>, Error> {
        let combined = self.select(layouter, cond, &x.combined, &y.combined)?;
        let spreaded_limb_10 =
            self.select(layouter, cond, &x.spreaded_limb_10, &y.spreaded_limb_10)?;
        let spreaded_limb_09 =
            self.select(layouter, cond, &x.spreaded_limb_09, &y.spreaded_limb_09)?;
        let spreaded_limb_11 =
            self.select(layouter, cond, &x.spreaded_limb_11, &y.spreaded_limb_11)?;
        let spreaded_limb_02 =
            self.select(layouter, cond, &x.spreaded_limb_02, &y.spreaded_limb_02)?;

        Ok(LimbsOfA {
            combined,
            spreaded_limb_10,
            spreaded_limb_09,
            spreaded_limb_11,
            spreaded_limb_02,
        })
    }
}

impl<F: PrimeField> ControlFlowInstructions<F, LimbsOfE<F>> for VarLenSha256Gadget<F> {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &LimbsOfE<F>,
        y: &LimbsOfE<F>,
    ) -> Result<LimbsOfE<F>, Error> {
        let combined = self.select(layouter, cond, &x.combined, &y.combined)?;
        let spreaded_limb_07 =
            self.select(layouter, cond, &x.spreaded_limb_07, &y.spreaded_limb_07)?;
        let spreaded_limb_12 =
            self.select(layouter, cond, &x.spreaded_limb_12, &y.spreaded_limb_12)?;
        let spreaded_limb_02 =
            self.select(layouter, cond, &x.spreaded_limb_02, &y.spreaded_limb_02)?;
        let spreaded_limb_05 =
            self.select(layouter, cond, &x.spreaded_limb_05, &y.spreaded_limb_05)?;
        let spreaded_limb_06 =
            self.select(layouter, cond, &x.spreaded_limb_06, &y.spreaded_limb_06)?;

        Ok(LimbsOfE {
            combined,
            spreaded_limb_07,
            spreaded_limb_12,
            spreaded_limb_02,
            spreaded_limb_05,
            spreaded_limb_06,
        })
    }
}

impl<F: PrimeField> ControlFlowInstructions<F, CompressionState<F>> for VarLenSha256Gadget<F> {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &CompressionState<F>,
        y: &CompressionState<F>,
    ) -> Result<CompressionState<F>, Error> {
        let a = self.select(layouter, cond, &x.a, &y.a)?;
        let b = self.select(layouter, cond, &x.b, &y.b)?;
        let c = self.select(layouter, cond, &x.c, &y.c)?;
        let d = self.select(layouter, cond, &x.d, &y.d)?;
        let e = self.select(layouter, cond, &x.e, &y.e)?;
        let f = self.select(layouter, cond, &x.f, &y.f)?;
        let g = self.select(layouter, cond, &x.g, &y.g)?;
        let h = self.select(layouter, cond, &x.h, &y.h)?;

        Ok(CompressionState {
            a,
            b,
            c,
            d,
            e,
            f,
            g,
            h,
        })
    }
}

// ----------------------------
#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};

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

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        Sha256Chip::load_from_scratch(layouter, config);
    }
}

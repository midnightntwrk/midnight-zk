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
        hash::{HashCPU, VarHashInstructions},
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

// Inherit HashCPU trait from PoseidonChip.
impl<F: PoseidonField> HashCPU<F, F> for VarLenPoseidonGadget<F> {
    fn hash(inputs: &[F]) -> F {
        <PoseidonChip<F> as HashCPU<F, F>>::hash(inputs)
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
            *result = self
                .native_gadget
                .select(layouter, update, result, register)?;
        }

        Ok(result)
    }

    /// Format the last chunk of data so it is padded and zeroed.
    /// Given chunk = [x1, x2, ..., xn], with n = RATE, returns [x1, ...,
    /// x_{offset-1}, len, 0, ..., 0]. If offset = 0, the chunk is returned
    /// intact.
    ///
    /// If `RATE = 2`, no zeros are added after `len`.
    fn pad_last_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        chunk: &[AssignedNative<F>],
        len: &AssignedNative<F>,
        offset: &AssignedNative<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert_eq!(chunk.len(), RATE);
        let ng = &self.native_gadget;

        let mut chunk = chunk.to_vec();
        if RATE > 2 {
            // Only need to fill with zeros if the chunk length is > 2.
            let zero = ng.assign_fixed(layouter, F::ZERO)?;
            let mut after_pad: AssignedBit<F> = ng.assign_fixed(layouter, false)?;
            for (i, elem) in chunk.iter_mut().enumerate().skip(1) {
                let b = ng.is_equal_to_fixed(layouter, offset, F::from(i as u64))?;
                *elem = ng.select(layouter, &b, len, elem)?;
                *elem = ng.select(layouter, &after_pad, &zero, elem)?;
                after_pad = ng.xor(layouter, &[b, after_pad])?;
            }
        } else {
            for (i, elem) in chunk.iter_mut().enumerate().skip(1) {
                let b = ng.is_equal_to_fixed(layouter, offset, F::from(i as u64))?;
                *elem = ng.select(layouter, &b, len, elem)?;
            }
        }

        Ok(chunk)
    }
}

impl<F: PoseidonField, const MAX_LEN: usize>
    VarHashInstructions<F, MAX_LEN, AssignedNative<F>, AssignedNative<F>, RATE>
    for VarLenPoseidonGadget<F>
{
    /// Hashes the variable-length vector inputs.
    ///
    /// # Panics
    ///  * If `MAX_LEN` is not a multiple of RATE.
    fn varhash(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, AssignedNative<F>, MAX_LEN, RATE>,
    ) -> Result<AssignedNative<F>, Error> {
        assert_eq!(MAX_LEN % RATE, 0);
        let ng = &self.native_gadget;
        let len = &input.len;

        // Initialize state.
        let zero = ng.assign_fixed(layouter, F::ZERO)?;
        let mut register: AssignedRegister<F> = vec![zero; WIDTH].try_into().unwrap();
        register[RATE] = ng.assign_fixed(layouter, F::from_u128(1 << 64))?;

        ng.assert_lower_than_fixed(layouter, len, &BigUint::from(MAX_LEN + 1))?;

        let mut chunk_iter = input.buffer.chunks(RATE);
        let mut chunk = chunk_iter.next().expect("At least one chunk.");

        // Flag that will signal when the hash input starts and chunks need to be
        // effectively processed and update the state.
        let mut updating: AssignedBit<F> = self.native_gadget.assign_fixed(layouter, false)?;

        // Position in the last chunk where the padding must be placed.
        let offset = self
            .native_gadget
            .modulus(layouter, len, MAX_LEN as u32, RATE as u32)?;

        // Length of the input rounded up to the chunk size or RATE.
        let rounded_len = {
            let is_zero = ng.is_zero(layouter, &offset)?;
            let len_round = ng.sub(layouter, len, &offset)?;
            let len_round_extra = ng.add_constant(layouter, &len_round, F::from(RATE as u64))?;
            ng.select(layouter, &is_zero, &len_round, &len_round_extra)
        }?;

        // Conditional update loop. Stops 1 chunk before the end.
        for i in 0..(MAX_LEN / RATE) - 1 {
            // Determines when we have arrived at the first chunk of input.
            let b = ng.is_equal_to_fixed(
                layouter,
                &rounded_len,
                F::from((MAX_LEN - (i * RATE)) as u64),
            )?;

            updating = ng.xor(layouter, &[b, updating])?;
            register = self.cond_update(layouter, &register, chunk, &updating)?;

            chunk = chunk_iter.next().expect("One more chunk.");
        }

        // Modify last chunk with the appropriate padding if necessary.
        let chunk = self.pad_last_chunk(layouter, chunk, len, &offset)?;
        register = self.cond_update(layouter, &register, &chunk, &updating)?;

        // Add an extra chunk in case the padding requires it (if offset = 0).
        let need_extra = ng.is_zero(layouter, &offset)?;
        let zero = ng.assign_fixed(layouter, F::ZERO)?;
        let extra_pad = [&[len.clone()], vec![zero; RATE - 1].as_slice()].concat();
        register = self.cond_update(layouter, &register, &extra_pad, &need_extra)?;

        Ok(register[0].clone())
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha12Rng;

    use super::*;
    use crate::{
        field::{
            decomposition::chip::{P2RDecompositionChip, P2RDecompositionConfig},
            NativeChip, NativeGadget,
        },
        hash::poseidon::PoseidonChip,
        instructions::{hash::VarHashInstructions, AssertionInstructions, SpongeCPU},
        utils::{circuit_modeling::circuit_to_json, util::FromScratch},
        vec::vector_gadget::VectorGadget,
    };

    // Native gadget functions.
    type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    /// Variable-length hash circuit.
    #[derive(Clone, Debug, Default)]
    struct VarCircuit<F, const MAX_LEN: usize> {
        inputs: Value<Vec<F>>,
        expected: F,
    }

    impl<F: PoseidonField, const MAX_LEN: usize> Circuit<F> for VarCircuit<F, MAX_LEN> {
        type Config = (
            P2RDecompositionConfig,
            <PoseidonChip<F> as FromScratch<F>>::Config,
        );
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let native_config = NG::<F>::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            );
            let poseidon_config = PoseidonChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            );
            (native_config, poseidon_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = NG::<F>::new_from_scratch(&config.0);
            let vec_gadget = VectorGadget::new(&native_gadget);
            let poseidon_chip = PoseidonChip::new_from_scratch(&config.1);
            let varlen_poseidon_gadget = VarLenPoseidonGadget::new(&poseidon_chip, &native_gadget);

            NG::load_from_scratch(&mut layouter, &config.0);
            PoseidonChip::load_from_scratch(&mut layouter, &config.1);

            let assigned_input: AssignedVector<F, AssignedNative<F>, MAX_LEN, RATE> =
                vec_gadget.assign(&mut layouter, self.inputs.clone())?;

            let output = varlen_poseidon_gadget.varhash(&mut layouter, &assigned_input)?;
            native_gadget.assert_equal_to_fixed(&mut layouter, &output, self.expected)?;

            Ok(())
        }
    }

    fn run_varhash_test<F, const MAX_LEN: usize>(inputs: &[F], cost_model: bool)
    where
        F: PoseidonField + ff::FromUniformBytes<64> + Ord,
    {
        let mut cpu_state = <PoseidonChip<F> as SpongeCPU<_, _>>::init(None);
        <PoseidonChip<F> as SpongeCPU<_, _>>::absorb(&mut cpu_state, inputs);
        let expected = <PoseidonChip<F> as SpongeCPU<_, _>>::squeeze(&mut cpu_state);

        let circuit = VarCircuit::<F, MAX_LEN> {
            inputs: Value::known(inputs.to_vec()),
            expected,
        };

        let k = 14;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(
                k,
                "Poseidon",
                format!("VarHash with max length {MAX_LEN}").as_str(),
                0,
                circuit,
            );
        }
    }

    #[test]
    fn test_poseidon_varhash() {
        type F = blstrs::Fq;

        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xdeadcafe);
        let inputs = (0..500).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        run_varhash_test::<_, 256>(&inputs[..0], false);
        run_varhash_test::<_, 256>(&inputs[..100], false);
        run_varhash_test::<_, 256>(&inputs[..255], false);
        run_varhash_test::<_, 256>(&inputs[..256], false);
        run_varhash_test::<_, 512>(&inputs[..400], false);
    }
}

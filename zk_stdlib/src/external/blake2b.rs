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

//! Import of the blake2b hash implementation from [Eryx](https://github.com/eryxcoop).

use blake2b::{
    blake2b::{
        blake2b_chip::{Blake2bChip, Blake2bConfig},
        NB_BLAKE2B_ADVICE_COLS,
    },
    types::byte::Byte,
};
use ff::PrimeField;
#[cfg(test)]
use midnight_circuits::{
    field::decomposition::chip::P2RDecompositionConfig, testing_utils::FromScratch,
};
use midnight_circuits::{field::AssignedNative, types::AssignedByte, ComposableChip};
#[cfg(test)]
use midnight_proofs::plonk::Instance;
use midnight_proofs::{
    circuit::{AssignedCell, Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

use crate::external::{convert_to_bytes, NG};

/// The chip for the external implementation of blake2b.
#[derive(Clone, Debug)]
pub struct Blake2bWrapper<F: PrimeField> {
    blake2b_chip: Blake2bChip<F>,
    native_gadget: NG<F>,
}

impl<F: PrimeField> Chip<F> for Blake2bWrapper<F> {
    type Config = Blake2bConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        self.blake2b_chip.config()
    }
    fn loaded(&self) -> &Self::Loaded {
        self.blake2b_chip.loaded()
    }
}
impl<F: PrimeField> ComposableChip<F> for Blake2bWrapper<F> {
    type SharedResources = (Column<Fixed>, [Column<Advice>; NB_BLAKE2B_ADVICE_COLS]);
    type InstructionDeps = NG<F>;
    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self {
        Self {
            blake2b_chip: Blake2bChip::new(config),
            native_gadget: sub_chips.clone(),
        }
    }
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.blake2b_chip.load(layouter)
    }
    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config {
        Blake2bChip::configure(
            meta,
            shared_resources.0,
            shared_resources.1[0],
            shared_resources.1[1..NB_BLAKE2B_ADVICE_COLS].try_into().unwrap(),
        )
    }
}

impl<F: PrimeField> Blake2bWrapper<F> {
    /// A front-end to the external implementation of Blake2b, managing the
    /// conversion between types.
    fn hash(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
        key: &[AssignedByte<F>],
        output_size: usize,
    ) -> Result<[AssignedByte<F>; 64], Error> {
        let input = &input.iter().map(AssignedNative::from).collect::<Vec<_>>();
        let key = &key.iter().map(AssignedNative::from).collect::<Vec<_>>();
        let output = &self
            .blake2b_chip
            .hash(layouter, input, key, output_size)?
            .map(AssignedCell::<Byte, F>::from);

        // The unsafe conversion is fine because we start from `output` which is
        // ranged-checked by Blake2b.
        Ok(convert_to_bytes(layouter, &self.native_gadget, output)?.try_into().unwrap())
    }

    /// Unnkeyed blake2b with 32-byte outputs.
    pub fn blake2b_256_digest(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        let digest = self.hash(layouter, input, &[], 32)?;
        Ok(digest.iter().take(32).cloned().collect::<Vec<_>>().try_into().unwrap())
    }

    /// Unnkeyed blake2b with 64-byte outputs.
    pub fn blake2b_512_digest(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 64], Error> {
        self.hash(layouter, input, &[], 64)
    }
}

#[cfg(test)]
impl<F: PrimeField> FromScratch<F> for Blake2bWrapper<F> {
    type Config = (Blake2bConfig, P2RDecompositionConfig);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_gadget = NG::new_from_scratch(&config.1);
        let blake2b_chip = Blake2bChip::new(&config.0);
        Self {
            blake2b_chip,
            native_gadget,
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let native_config = NG::configure_from_scratch(meta, instance_columns);
        let advice_cols =
            (0..NB_BLAKE2B_ADVICE_COLS).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let constant_column = meta.fixed_column();

        let blake2b_config =
            Blake2bWrapper::configure(meta, &(constant_column, advice_cols.try_into().unwrap()));
        (blake2b_config, native_config)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.load(layouter)?;
        NG::load_from_scratch(&self.native_gadget, layouter)
    }
}

// Some preimage tests against an external library.
#[cfg(test)]
mod test {
    use blake2::Blake2b;
    use ff::PrimeField;
    use midnight_circuits::{
        field::NativeGadget,
        instructions::{hash::HashCPU, HashInstructions},
        testing_utils::{test_hash, FromScratch},
        types::AssignedByte,
    };
    use midnight_curves::Fq;
    use midnight_proofs::{
        circuit::Layouter,
        plonk::{Column, ConstraintSystem, Error, Instance},
    };
    use sha2::{
        digest::consts::{U32, U64},
        Digest,
    };

    use crate::external::blake2b::Blake2bWrapper;

    // A wrapper for testing Blake with 512 bits.
    #[derive(Debug, Clone)]
    struct Blake2b512<F: PrimeField>(Blake2bWrapper<F>);

    // A wrapper for testing Blake with 256 bits.
    #[derive(Debug, Clone)]
    struct Blake2b256<F: PrimeField>(Blake2bWrapper<F>);

    impl<F: PrimeField> HashCPU<u8, [u8; 64]> for Blake2b512<F> {
        fn hash(input: &[u8]) -> [u8; 64] {
            let mut hasher = Blake2b::<U64>::new();
            hasher.update(input);
            hasher.finalize().into()
        }
    }

    impl<F: PrimeField> HashCPU<u8, [u8; 32]> for Blake2b256<F> {
        fn hash(inputs: &[u8]) -> [u8; 32] {
            let mut hasher = Blake2b::<U32>::new();
            hasher.update(inputs);
            hasher.finalize().into()
        }
    }

    impl<F: PrimeField> HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 64]> for Blake2b512<F> {
        fn hash(
            &self,
            layouter: &mut impl Layouter<F>,
            inputs: &[AssignedByte<F>],
        ) -> Result<[AssignedByte<F>; 64], Error> {
            self.0.blake2b_512_digest(layouter, inputs)
        }
    }

    impl<F: PrimeField> HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Blake2b256<F> {
        fn hash(
            &self,
            layouter: &mut impl Layouter<F>,
            inputs: &[AssignedByte<F>],
        ) -> Result<[AssignedByte<F>; 32], Error> {
            self.0.blake2b_256_digest(layouter, inputs)
        }
    }

    impl<F: PrimeField> FromScratch<F> for Blake2b512<F> {
        type Config = <Blake2bWrapper<F> as FromScratch<F>>::Config;
        fn new_from_scratch(config: &Self::Config) -> Self {
            Blake2b512(Blake2bWrapper::new_from_scratch(config))
        }
        fn configure_from_scratch(
            meta: &mut ConstraintSystem<F>,
            instance_columns: &[Column<Instance>; 2],
        ) -> Self::Config {
            Blake2bWrapper::configure_from_scratch(meta, instance_columns)
        }
        fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
            Blake2bWrapper::load_from_scratch(&self.0, layouter)
        }
    }

    impl<F: PrimeField> FromScratch<F> for Blake2b256<F> {
        type Config = <Blake2bWrapper<F> as FromScratch<F>>::Config;
        fn new_from_scratch(config: &Self::Config) -> Self {
            Blake2b256(Blake2bWrapper::new_from_scratch(config))
        }
        fn configure_from_scratch(
            meta: &mut ConstraintSystem<F>,
            instance_columns: &[Column<Instance>; 2],
        ) -> Self::Config {
            Blake2bWrapper::configure_from_scratch(meta, instance_columns)
        }
        fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
            Blake2bWrapper::load_from_scratch(&self.0, layouter)
        }
    }

    #[test]
    fn test_blake2b_512_preimage() {
        fn test_wrapper(input_size: usize, k: u32, cost_model: bool) {
            test_hash::<
                Fq,
                AssignedByte<Fq>,
                [AssignedByte<Fq>; 64],
                Blake2b512<Fq>,
                NativeGadget<Fq, _, _>,
            >(cost_model, "Blake2b_512", input_size, k);
        }

        const BLAKE2B_BLOCK_SIZE: usize = 128;

        test_wrapper(BLAKE2B_BLOCK_SIZE - 2, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE - 1, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE + 1, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE + 2, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE - 2, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE - 1, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE + 1, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE + 2, 17, false);
    }

    #[test]
    fn test_blake2b_256_preimage() {
        fn test_wrapper(input_size: usize, k: u32, cost_model: bool) {
            test_hash::<
                Fq,
                AssignedByte<Fq>,
                [AssignedByte<Fq>; 32],
                Blake2b256<Fq>,
                NativeGadget<Fq, _, _>,
            >(cost_model, "Blake2b_256", input_size, k);
        }

        const BLAKE2B_BLOCK_SIZE: usize = 128;

        test_wrapper(BLAKE2B_BLOCK_SIZE - 2, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE - 1, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE + 1, 17, false);
        test_wrapper(BLAKE2B_BLOCK_SIZE + 2, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE - 2, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE - 1, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE + 1, 17, false);
        test_wrapper(2 * BLAKE2B_BLOCK_SIZE + 2, 17, false);
    }
}

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

//! Import of the keccak variant of SHA, implementation from [Alexandros Zacharakis](https://github.com/alexandroszacharakis8).

use ff::PrimeField;
use keccak_sha3::{
    packed_chip::{PackedChip, PackedConfig, PACKED_ADVICE_COLS, PACKED_FIXED_COLS},
    sha3_256_gadget::{Keccak256, Sha3_256},
};
#[cfg(test)]
use midnight_circuits::{
    field::decomposition::chip::P2RDecompositionConfig, testing_utils::FromScratch,
};
use midnight_circuits::{
    instructions::AssertionInstructions,
    types::{AssignedByte, InnerValue},
    ComposableChip,
};
#[cfg(test)]
use midnight_proofs::plonk::Instance;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

use crate::external::{convert_to_bytes, unsafe_convert_to_bytes, NG};

/// The chip for the external implementation of keccak and sha3.
///
/// Note: A single wrapper is used for the two circuits since, internally, both
/// are configured with the same columns and table (`PackedChip<F>`). In
/// particular, enabling either of the two chips in the standard library has the
/// same effect, namely configuring a `PackedChip<F>`.
#[derive(Clone, Debug)]
pub struct KeccakSha3Wrapper<F: PrimeField> {
    keccak_chip: Keccak256<F, PackedChip<F>>,
    sha3_chip: Sha3_256<F, PackedChip<F>>,
    native_gadget: NG<F>,
}

impl<F: PrimeField> Chip<F> for KeccakSha3Wrapper<F> {
    type Config = PackedConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        self.keccak_chip.config()
    }
    fn loaded(&self) -> &Self::Loaded {
        self.keccak_chip.loaded()
    }
}
impl<F: PrimeField> ComposableChip<F> for KeccakSha3Wrapper<F> {
    type SharedResources = (
        Column<Fixed>,
        [Column<Advice>; PACKED_ADVICE_COLS],
        [Column<Fixed>; PACKED_FIXED_COLS],
    );
    type InstructionDeps = NG<F>;
    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self {
        let packed_chip = PackedChip::new(config);
        Self {
            keccak_chip: Keccak256::<F, PackedChip<F>>::new(packed_chip.clone()),
            sha3_chip: Sha3_256::<F, PackedChip<F>>::new(packed_chip),
            native_gadget: sub_chips.clone(),
        }
    }
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.keccak_chip.load_table(layouter)
    }
    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config {
        keccak_sha3::packed_chip::PackedChip::configure(
            meta,
            shared_resources.0,
            shared_resources.1,
            shared_resources.2,
        )
    }
}

impl<F: PrimeField> KeccakSha3Wrapper<F> {
    /// Wrapper for the main method of Keccak/Sha3. The argument `keccak` is set
    /// to true to invoke the `keccak256` variant of the hash, and `sha3` is
    /// called otherwise.
    fn digest(
        &self,
        keccak: bool,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        // The Keccak implementation requires `Value<u8>` inputs, instead of assigned
        // bytes. We extract these values from `input`, and bridge the broken link with
        // `assert_equal` below.
        let raw_input = input.iter().map(|b| b.value()).collect::<Vec<Value<u8>>>();
        let (reassigned_input, digest) = if keccak {
            self.keccak_chip.digest(layouter, &raw_input)
        } else {
            self.sha3_chip.digest(layouter, &raw_input)
        }?;

        // Rebuilding the broken link between the re-assigned input and the original
        // one. The unsafe conversion is sound since we are asserting equality below
        // with `input` which is range-checked.
        let reassigned_input =
            unsafe_convert_to_bytes(layouter, &self.native_gadget, &reassigned_input)?;
        for (original_byte, reassigned_byte) in input.iter().zip(reassigned_input.iter()) {
            self.native_gadget.assert_equal(layouter, original_byte, reassigned_byte)?
        }
        // Sanity check.
        assert_eq!(input.len(), reassigned_input.len());

        // We use a safe conversion to catch potential soundness issues in the
        // range-checks of the external implementation.
        let digest = convert_to_bytes(layouter, &self.native_gadget, &digest)?;
        Ok(digest.try_into().unwrap())
    }

    /// Wrapper for the main method of Keccak.
    pub fn keccak_256_digest(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        self.digest(true, layouter, input)
    }

    /// Wrapper for the main method of sha3.
    pub fn sha3_256_digest(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        self.digest(false, layouter, input)
    }
}

#[cfg(test)]
impl<F: PrimeField> FromScratch<F> for KeccakSha3Wrapper<F> {
    type Config = (PackedConfig, P2RDecompositionConfig);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_gadget = NG::new_from_scratch(&config.1);
        KeccakSha3Wrapper::new(&config.0, &native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let advice_cols = (0..PACKED_ADVICE_COLS).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed_cols = (0..PACKED_FIXED_COLS).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let constant_column = meta.fixed_column();

        let native_config = NG::configure_from_scratch(meta, instance_columns);
        let sha_config = KeccakSha3Wrapper::configure(
            meta,
            &(
                constant_column,
                advice_cols[..PACKED_ADVICE_COLS].try_into().unwrap(),
                fixed_cols[..PACKED_FIXED_COLS].try_into().unwrap(),
            ),
        );
        (sha_config, native_config)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.load(layouter)?;
        NG::load_from_scratch(&self.native_gadget, layouter)
    }
}

// Some preimage tests against an external library.
#[cfg(test)]
mod test {
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
    use sha3::{Digest, Keccak256 as KeccakCpu, Sha3_256 as Sha3Cpu};

    use crate::external::keccak_sha3::KeccakSha3Wrapper;

    // A wrapper for testing Blake with 512 bits.
    #[derive(Debug, Clone)]
    struct Keccak256<F: PrimeField>(KeccakSha3Wrapper<F>);

    // A wrapper for testing Blake with 256 bits.
    #[derive(Debug, Clone)]
    struct Sha3_256<F: PrimeField>(KeccakSha3Wrapper<F>);

    impl<F: PrimeField> HashCPU<u8, [u8; 32]> for Keccak256<F> {
        fn hash(input: &[u8]) -> [u8; 32] {
            let mut hasher = KeccakCpu::new();
            hasher.update(input);
            hasher.finalize().into()
        }
    }

    impl<F: PrimeField> HashCPU<u8, [u8; 32]> for Sha3_256<F> {
        fn hash(inputs: &[u8]) -> [u8; 32] {
            let mut hasher = Sha3Cpu::new();
            hasher.update(inputs);
            hasher.finalize().into()
        }
    }

    impl<F: PrimeField> HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Keccak256<F> {
        fn hash(
            &self,
            layouter: &mut impl Layouter<F>,
            inputs: &[AssignedByte<F>],
        ) -> Result<[AssignedByte<F>; 32], Error> {
            self.0.keccak_256_digest(layouter, inputs)
        }
    }

    impl<F: PrimeField> HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Sha3_256<F> {
        fn hash(
            &self,
            layouter: &mut impl Layouter<F>,
            inputs: &[AssignedByte<F>],
        ) -> Result<[AssignedByte<F>; 32], Error> {
            self.0.sha3_256_digest(layouter, inputs)
        }
    }

    impl<F: PrimeField> FromScratch<F> for Keccak256<F> {
        type Config = <KeccakSha3Wrapper<F> as FromScratch<F>>::Config;
        fn new_from_scratch(config: &Self::Config) -> Self {
            Keccak256(KeccakSha3Wrapper::new_from_scratch(config))
        }
        fn configure_from_scratch(
            meta: &mut ConstraintSystem<F>,
            instance_columns: &[Column<Instance>; 2],
        ) -> Self::Config {
            KeccakSha3Wrapper::configure_from_scratch(meta, instance_columns)
        }
        fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
            KeccakSha3Wrapper::load_from_scratch(&self.0, layouter)
        }
    }

    impl<F: PrimeField> FromScratch<F> for Sha3_256<F> {
        type Config = <KeccakSha3Wrapper<F> as FromScratch<F>>::Config;
        fn new_from_scratch(config: &Self::Config) -> Self {
            Sha3_256(KeccakSha3Wrapper::new_from_scratch(config))
        }
        fn configure_from_scratch(
            meta: &mut ConstraintSystem<F>,
            instance_columns: &[Column<Instance>; 2],
        ) -> Self::Config {
            KeccakSha3Wrapper::configure_from_scratch(meta, instance_columns)
        }
        fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
            KeccakSha3Wrapper::load_from_scratch(&self.0, layouter)
        }
    }

    #[test]
    fn test_keccak_preimage() {
        fn test_wrapper(input_size: usize, k: u32, cost_model: bool) {
            test_hash::<
                Fq,
                AssignedByte<Fq>,
                [AssignedByte<Fq>; 32],
                Keccak256<Fq>,
                NativeGadget<Fq, _, _>,
            >(cost_model, "Keccak_256", input_size, k);
        }
        const SHA3_256_RATE: usize = 136;

        test_wrapper(SHA3_256_RATE - 2, 14, false);
        test_wrapper(SHA3_256_RATE - 1, 14, false);
        test_wrapper(SHA3_256_RATE, 14, false);
        test_wrapper(SHA3_256_RATE + 1, 14, false);
        test_wrapper(SHA3_256_RATE + 2, 14, false);

        test_wrapper(2 * SHA3_256_RATE - 2, 16, false);
        test_wrapper(2 * SHA3_256_RATE - 1, 16, false);
        // Test for cost model
        test_wrapper(2 * SHA3_256_RATE, 16, true);
        test_wrapper(2 * SHA3_256_RATE + 1, 16, false);
        test_wrapper(2 * SHA3_256_RATE + 2, 16, false);

        test_wrapper(4 * SHA3_256_RATE, 16, false);

        test_wrapper(0, 14, false);
        test_wrapper(1, 14, false);
        test_wrapper(2, 14, false);
    }

    #[test]
    fn test_sha3_preimage() {
        fn test_wrapper(input_size: usize, k: u32, cost_model: bool) {
            test_hash::<
                Fq,
                AssignedByte<Fq>,
                [AssignedByte<Fq>; 32],
                Sha3_256<Fq>,
                NativeGadget<Fq, _, _>,
            >(cost_model, "Sha3_256", input_size, k);
        }
        const SHA3_256_RATE: usize = 136;

        test_wrapper(SHA3_256_RATE - 2, 14, false);
        test_wrapper(SHA3_256_RATE - 1, 14, false);
        test_wrapper(SHA3_256_RATE, 14, false);
        test_wrapper(SHA3_256_RATE + 1, 14, false);
        test_wrapper(SHA3_256_RATE + 2, 14, false);

        test_wrapper(2 * SHA3_256_RATE - 2, 16, false);
        test_wrapper(2 * SHA3_256_RATE - 1, 16, false);
        // Test for cost model
        test_wrapper(2 * SHA3_256_RATE, 16, true);
        test_wrapper(2 * SHA3_256_RATE + 1, 16, false);
        test_wrapper(2 * SHA3_256_RATE + 2, 16, false);

        test_wrapper(4 * SHA3_256_RATE, 16, false);

        test_wrapper(0, 14, false);
        test_wrapper(1, 14, false);
        test_wrapper(2, 14, false);
    }
}

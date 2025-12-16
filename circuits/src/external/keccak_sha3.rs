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
use midnight_proofs::plonk::Instance;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

use crate::{
    external::{convert_to_bytes, unsafe_convert_to_bytes, NG},
    instructions::AssertionInstructions,
    types::{AssignedByte, InnerValue},
    utils::ComposableChip,
};
#[cfg(test)]
use crate::{field::decomposition::chip::P2RDecompositionConfig, testing_utils::FromScratch};

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

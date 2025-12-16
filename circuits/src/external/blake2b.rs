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
use midnight_proofs::plonk::Instance;
use midnight_proofs::{
    circuit::{AssignedCell, Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

use crate::{
    external::{convert_to_bytes, NG},
    field::AssignedNative,
    types::AssignedByte,
    utils::ComposableChip,
};
#[cfg(test)]
use crate::{field::decomposition::chip::P2RDecompositionConfig, testing_utils::FromScratch};

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

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

//! Trait for modular, composable chips.

use std::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::{ConstraintSystem, Error},
};

/// Provides a common interface for layering chips with shared resources.
pub trait ComposableChip<F>: Chip<F> + Clone + Debug
where
    F: PrimeField,
{
    /// Resources that can be used by other chips or gadgets,
    /// typically sub-chip configurations and columns.
    type SharedResources;

    /// Instruction set dependencies of the chip.
    /// This chip will need to be provided with subchips that implement these
    /// instructions.
    type InstructionDeps;

    /// Initialize the chip.
    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self;

    /// Configure the chip.
    /// Receives the underlying chips and columns it needs via
    /// Self::SharedResources. This method must not allocate any resource in
    /// the constraint system that is intended to be shared by other chips.
    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config;

    /// Load all tables (including those of underlying chips taken as configs)
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error>;
}

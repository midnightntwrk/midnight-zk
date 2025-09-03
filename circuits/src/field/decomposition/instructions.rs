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

//! Instruction trait for a chip capable of performing the core decomposition
//! operations:
//! - decompose in fixed sized limbs,
//! - less than 2^i assertions

use std::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::types::AssignedNative;

/// Trait that implement the "core" decomposition instructions
pub trait CoreDecompositionInstructions<F: PrimeField>: Clone + Debug {
    /// Decomposes a field element x in limbs of bit length limb size and
    /// returns the limbs in *low endian encoding*. If bit length is not
    /// divisible by limb_size, the last limb (corresponding to the most
    /// significant bits of x) is restricted accordingly, i.e. it is guaranteed
    /// that it has bitlength *at most* bit_length % limb_size
    ///
    /// The function guarantees that the number is smaller than 2^{bit_length}
    /// and that the returned limbs are smaller than 2^{limb_size}
    fn decompose_fixed_limb_size(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bit_length: usize,
        limb_size: usize,
    ) -> Result<Vec<AssignedNative<F>>, Error>;

    /// Assigns a value and guarantees that it is strictly lower than
    /// 2^{bit_length}
    fn assign_less_than_pow2(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        bit_length: usize,
    ) -> Result<AssignedNative<F>, Error>;

    /// Function that guarantees that x < 2^{bit_length}
    fn assert_less_than_pow2(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bit_length: usize,
    ) -> Result<(), Error> {
        let y = self.assign_less_than_pow2(layouter, x.value().copied(), bit_length)?;
        layouter.assign_region(
            || "copy",
            |mut region| region.constrain_equal(x.cell(), y.cell()),
        )
    }

    /// Assigns several values and asserts that they are all strictly lower than
    /// 2^{bit_length}.
    ///
    /// # Panics
    ///
    /// If bit_length > 8.
    fn assign_many_small(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<F>],
        bit_length: usize,
    ) -> Result<Vec<AssignedNative<F>>, Error>;
}

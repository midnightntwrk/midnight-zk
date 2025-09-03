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

//! Vector manipulation instructions interface.
//!
//! The trait is parameterized by the type `T` of elements contained in the
//! vector, as well as 2 constants: its maximum size `M` and its chunk alignment
//! value `A`.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    field::AssignedNative,
    types::AssignedBit,
    vec::{AssignedVector, Vectorizable},
};

/// Instructions for Vector manipulation..
pub trait VectorInstructions<F, T, const M: usize, const A: usize>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
{
    /// Changes the size of an AssignedVector from M to L.
    ///
    /// # Panics
    ///
    /// If `L <= M` or `A` does not divide `L`.
    fn resize<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedVector<F, T, M, A>,
    ) -> Result<AssignedVector<F, T, L, A>, Error>;

    /// Assigns vector with a chosen filler value.
    ///
    /// # Panics
    ///
    /// If |value| > M.
    fn assign_with_filler(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<T::Element>>,
        filler: Option<T::Element>,
    ) -> Result<AssignedVector<F, T, M, A>, Error>;

    /// Trims `n_elems` elements from the beginning of the vector.
    /// The trimmed elements will not be changed by filler elements,
    /// they will remain in the buffer but not as part of the effective payload.
    ///
    /// # Unsatisfiable
    ///
    ///   If the vector length < `n_elems`.
    fn trim_beginning(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
        n_elems: usize,
    ) -> Result<AssignedVector<F, T, M, A>, Error>;

    /// Returns a vector of AssignedBits signaling the cells that represent
    /// padding with a 1, and the ones that represent payload data with a 0.
    fn padding_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<[AssignedBit<F>; M], Error>;

    /// Returns the first and last positions of data in the buffer.
    fn get_limits(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error>;
}

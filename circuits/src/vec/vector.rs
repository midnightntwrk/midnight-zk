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

use std::ops::Range;

use ff::PrimeField;
use midnight_proofs::circuit::Value;

use crate::{
    field::AssignedNative,
    types::{AssignedByte, InnerValue},
    utils::util::fe_to_big,
};

/// A variable-length vector of elements of type T, with size bound M.
/// - `len` is the (potentially secret) effective length of the vector, its
///   value is guaranteed to be in the range `[0, M]`.
/// - `buffer` is the padded payload of this vector; it contains the effective
///   data of the vector as well as filler values, which are UNCONSTRAINED.
///
/// The effective payload in the data is aligned in A sized chunks. This
/// enables more efficient implementations of instructions like hashing
/// over this type. As a result of this alignment, the data may contain filler
/// values before and after the effective payload. The padding in front of
/// the payload will always be 0 mod A, so that the payload begins aligned in A
/// sized chunks. The padding at the end of the payload will be have a size in
/// [0, A) such that | front_pad | + | payload | + | back_pad | = M.
#[derive(Clone, Debug)]
pub struct AssignedVector<F: PrimeField, T: Vectorizable, const M: usize, const A: usize> {
    /// Padded payload of the vector.
    pub(crate) buffer: [T; M],

    /// Effective length of the vector.
    pub(crate) len: AssignedNative<F>,
}

/// Returns the range where the data should be placed in the buffer.
pub fn get_lims<const M: usize, const A: usize>(len: usize) -> Range<usize> {
    let final_pad_len = (A - (len % A)) % A;
    M - len - final_pad_len..M - final_pad_len
}

impl<F: PrimeField, const M: usize, T: Vectorizable, const A: usize> InnerValue
    for AssignedVector<F, T, M, A>
{
    type Element = Vec<T::Element>;

    fn value(&self) -> Value<Self::Element> {
        let data = Value::<Vec<T::Element>>::from_iter(self.buffer.iter().map(|v| v.value()));
        let idxs: Value<_> = self.len.value().map(|len| {
            let len: usize = fe_to_big(*len).try_into().unwrap();

            let end_pad = (A - (len % A)) % A;
            (M - len - end_pad, M - end_pad)
        });
        data.zip(idxs)
            .map(|(data, idxs)| data[idxs.0..idxs.1].to_vec())
    }
}

/// Trait for the individual elements of an AssignedVector.
pub trait Vectorizable: InnerValue {
    /// Value to fill the space in the buffer that is not occupied with vector
    /// data.
    const FILLER: Self::Element;
}

impl<F: PrimeField> Vectorizable for AssignedNative<F> {
    const FILLER: F = F::ZERO;
}

impl<F: PrimeField> Vectorizable for AssignedByte<F> {
    const FILLER: u8 = 0u8;
}

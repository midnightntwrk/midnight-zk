// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

use midnight_proofs::circuit::Value;

use crate::{
    field::AssignedNative,
    types::{AssignedByte, InnerValue},
    CircuitField,
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
/// sized chunks. The padding at the end of the payload will have a size in
/// [0, A) such that | front_pad | + | payload | + | back_pad | = M.
///
/// **Invariant: `A > 0`, `A <= M`, and `M` is a multiple of `A`.** Several
/// operations (`padding_flag`, `get_limits`, hashing, …) rely on this to
/// guarantee that the buffer decomposes into exactly `M / A` full chunks and
/// that a full-capacity vector (`len == M`) can always be placed without
/// overflow.
/// The invariant is checked at compile time  by [`AssignedVector::new`],
/// which is the constructor every `AssignedVector` should be built through.
#[derive(Clone, Debug)]
pub struct AssignedVector<F: CircuitField, T: Vectorizable, const M: usize, const A: usize> {
    /// Padded payload of the vector. Boxed to keep large buffers
    /// off the stack.
    pub(crate) buffer: Box<[T; M]>,

    /// Effective length of the vector.
    pub(crate) len: AssignedNative<F>,
}

impl<F: CircuitField, T: Vectorizable, const M: usize, const A: usize> AssignedVector<F, T, M, A> {
    /// Construct an `AssignedVector` from an already-assigned `buffer` and
    /// `len`.
    ///
    /// This is the single entry point for building an `AssignedVector`; it
    /// enforces the type invariant `0 < A <= M` and `A | M` at compile time.
    pub(crate) fn new(buffer: Box<[T; M]>, len: AssignedNative<F>) -> Self {
        const {
            assert!(
                A > 0 && M >= A && M.is_multiple_of(A),
                "AssignedVector requires 0 < A <= M and A | M."
            )
        };
        Self { buffer, len }
    }
}

/// Returns the range where the data should be placed in the buffer.
pub fn get_lims<const M: usize, const A: usize>(len: usize) -> Range<usize> {
    const {
        assert!(
            A > 0 && M >= A && M.is_multiple_of(A),
            "AssignedVector requires 0 < A <= M and A | M."
        )
    };
    let final_pad_len = (A - (len % A)) % A;
    M - len - final_pad_len..M - final_pad_len
}

impl<F: CircuitField, const M: usize, T: Vectorizable, const A: usize> InnerValue
    for AssignedVector<F, T, M, A>
{
    type Element = Vec<T::Element>;

    fn value(&self) -> Value<Self::Element> {
        let data = Value::<Vec<T::Element>>::from_iter(self.buffer.iter().map(|v| v.value()));
        let range = self.len.value().map(|len| {
            let len: usize = len.to_biguint().try_into().unwrap();
            get_lims::<M, A>(len)
        });
        data.zip(range).map(|(data, range)| data[range].to_vec())
    }
}

/// Trait for the individual elements of an AssignedVector.
pub trait Vectorizable: InnerValue {
    /// Value to fill the space in the buffer that is not occupied with vector
    /// data.
    const FILLER: Self::Element;
}

impl<F: CircuitField> Vectorizable for AssignedNative<F> {
    const FILLER: F = F::ZERO;
}

impl<F: CircuitField> Vectorizable for AssignedByte<F> {
    const FILLER: u8 = 0u8;
}

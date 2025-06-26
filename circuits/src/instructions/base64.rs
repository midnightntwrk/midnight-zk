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

//! Set of Base64 instructions.
use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::types::{AssignedByte, AssignedVector};

/// This trait defines methods for converting data encoded in standard Base64 or
/// Base64URL (URL-safe) format into its raw byte representation.
pub trait Base64Instructions<F: PrimeField> {
    /// Receives a base64 url-safe encoded string as [AssignedByte]s and returns
    /// the decoded ASCII string as a vector of [AssignedByte].
    /// If `padded` is selected, the input length must be a multiple of 4.
    ///
    /// The length of the output is always 3/4 of the padded input's length.
    /// In order to reach this length, the output will be completed with one or
    /// two ASCII_ZERO chars if necessary.
    ///
    /// # Panics
    /// If `padded` = true and the input length is not a multiple of 4.
    fn decode_base64url(
        &self,
        layouter: &mut impl Layouter<F>,
        b64url_input: &[AssignedByte<F>],
        padded: bool,
    ) -> Result<Vec<AssignedByte<F>>, Error>;

    /// Receives a base64 encoded string as [AssignedByte]s and returns
    /// the decoded ASCII string as a vector of [AssignedByte].
    /// If `padded` is selected, the input length must be a multiple of 4.
    ///
    /// The length of the output is always 3/4 of the padded input's length.
    /// In order to reach this length, the output will be completed with one or
    /// two ASCII_ZERO chars if necessary.
    ///
    /// # Panics
    /// If `padded` = true and the input length is not a multiple of 4.
    fn decode_base64(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &[AssignedByte<F>],
        padded: bool,
    ) -> Result<Vec<AssignedByte<F>>, Error>;
}

/// An AssignedVector with additional assumptions:
///  1. The filler elements in the vector are present in the Base64 table, and
///     therefore, we can decode the whole buffer.
///  2. The length of the vector is a multiple of 4. This is guaranteed for
///     every padded base64 string.
///
/// Note:
///  These extra assumptions guarantee completeness.
///  Soundness is always guaranteed.
#[derive(Debug, Clone)]
pub struct Base64Vec<F: PrimeField, const M: usize, const A: usize>(
    pub AssignedVector<F, AssignedByte<F>, M, A>,
);

impl<F: PrimeField, const M: usize, const A: usize> From<Base64Vec<F, M, A>>
    for AssignedVector<F, AssignedByte<F>, M, A>
{
    fn from(value: Base64Vec<F, M, A>) -> Self {
        value.0
    }
}

/// Equivalent to Base64Instructions for variable-length inputs.
pub trait Base64VarInstructions<F: PrimeField, const M: usize, const A: usize>:
    Base64Instructions<F>
{
    /// Assigns a vector of bytes into Base64Vec.
    ///
    /// # Panics
    ///
    /// If |value| > M or A does not divide |value|.
    fn assign_var_base64(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<u8>>,
    ) -> Result<Base64Vec<F, M, A>, Error>;

    /// Variable length equivalent of `decode_base64_url` in
    /// `Base64Instructions`. Inputs must always be padded apropriately
    /// according to the base64 format.
    fn var_decode_base64url<const M_OUT: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        b64url_input: &Base64Vec<F, M, A>,
    ) -> Result<AssignedVector<F, AssignedByte<F>, M_OUT, 3>, Error>;

    /// Equivalent of `decode_base64` in `Base64Instructions`.
    /// Inputs must always be padded apropriately according to the base64
    /// format.
    fn var_decode_base64<const M_OUT: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &Base64Vec<F, M, A>,
    ) -> Result<AssignedVector<F, AssignedByte<F>, M_OUT, 3>, Error>;
}

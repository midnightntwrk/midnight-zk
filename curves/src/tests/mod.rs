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

pub mod curve;
pub mod engine;
pub mod field;
pub mod field_halo2curves;
pub mod pairing;

pub(crate) fn hex_to_bytes(hex: &str) -> Vec<u8> {
    hex::decode(hex).expect("Invalid hex string")
}

/// Helper function to convert a hex string to a field element.
/// This is used in the tests for BN256 curve, which uses little-endian internal
/// representation for its field elements. The input of this function should
/// have the opposite endianness, so it expects big-endian hex strings.
#[cfg(any(test, feature = "dev-curves"))]
pub(crate) fn hex_to_field<F: ff::PrimeField>(hex: &str) -> F {
    let mut bytes = hex_to_bytes(hex);
    bytes.reverse();
    let mut repr = F::Repr::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes);
    F::from_repr(repr).unwrap()
}

/// Helper function to create a point from hex coordinates.
/// Assuming the field elements use little-endian internal representation, this
/// function expects coordinates as big-endian hex strings in canonical form.
#[cfg(any(test, feature = "dev-curves"))]
pub(crate) fn point_from_hex<C>(x_hex: &str, y_hex: &str) -> C
where
    C: crate::CurveAffine,
    C::Base: ff::PrimeField,
{
    let x = hex_to_field(x_hex);
    let y = hex_to_field(y_hex);
    C::from_xy(x, y).expect("Invalid point coordinates")
}

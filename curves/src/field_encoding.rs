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

//! Field encoding utilities for explicit byte representation conversions.
//!
//! The `ff::PrimeField` trait treats `to_repr()`/`from_repr()` as opaque with
//! implementation-specific endianness. This module provides the [`FieldEncoding`]
//! trait with explicit conversions that guarantee byte order.
//!
//! # Example
//!
//! ```ignore
//! use midnight_curves::{FieldEncoding, Fq};
//!
//! let scalar = Fq::from(42u64);
//!
//! // Explicit endianness.
//! let le_bytes = scalar.to_le_bytes();
//! let be_bytes = scalar.to_be_bytes();
//!
//! // Roundtrip.
//! let recovered = Fq::from_le_bytes(le_bytes.as_ref()).unwrap();
//! assert_eq!(scalar, recovered);
//!
//! // BigUint conversion.
//! let n = scalar.to_biguint();
//! let recovered = Fq::from_biguint(&n).unwrap();
//! assert_eq!(scalar, recovered);
//! ```

use ff::PrimeField;
use num_bigint::BigUint;

/// Endianness of a field native byte representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian {
    /// Little-endian: least significant byte first.
    LE,
    /// Big-endian: most significant byte first.
    BE,
}

/// Extension trait for [`PrimeField`] providing explicit byte encoding methods.
pub trait FieldEncoding: PrimeField {
    /// Fixed-size byte array type for this field.
    ///
    /// This should be `[u8; BYTE_SIZE]`. We use an associated type because Rust
    /// doesn't allow using associated constants as const generic parameters.
    type Bytes: Copy + Default + AsRef<[u8]> + AsMut<[u8]>;

    /// Size of the field element in bytes.
    ///
    /// This should match `size_of::<Self::Repr>()` and `size_of::<Self::Bytes>()`.
    const BYTE_SIZE: usize;

    /// Endianness of the native `to_repr()` representation.
    ///
    /// This allows generic code to know how to interpret the bytes from
    /// `PrimeField::to_repr()` without runtime detection.
    const REPR_ENDIAN: Endian;

    /// Converts the field element to a little-endian byte array.
    fn to_le_bytes(&self) -> Self::Bytes;

    /// Converts the field element to a big-endian byte array.
    fn to_be_bytes(&self) -> Self::Bytes;

    /// Creates a field element from little-endian bytes.
    ///
    /// Returns `None` if:
    /// - The byte slice has incorrect length.
    /// - The value is not in the canonical range `[0, modulus)`.
    fn from_le_bytes(bytes: &[u8]) -> Option<Self>;

    /// Creates a field element from big-endian bytes.
    ///
    /// Returns `None` if:
    /// - The byte slice has incorrect length.
    /// - The value is not in the canonical range `[0, modulus)`.
    fn from_be_bytes(bytes: &[u8]) -> Option<Self>;

    /// Converts the field element to a [`BigUint`].
    ///
    /// This is endianness-agnostic: the returned `BigUint` represents the
    /// same integer value regardless of the field's native representation.
    fn to_biguint(&self) -> BigUint;

    /// Creates a field element from a [`BigUint`].
    ///
    /// Returns `None` if the value is not in the canonical range `[0, modulus)`.
    ///
    /// Note: This does **not** perform modular reduction. If you need reduction,
    /// compute `n % modulus` before calling this method.
    fn from_biguint(n: &BigUint) -> Option<Self>;

    /// Converts the field element to little-endian bits.
    ///
    /// The returned vector has length `BYTE_SIZE * 8`. The least significant
    /// bit is at index 0.
    fn to_le_bits(&self) -> Vec<bool> {
        let bytes = self.to_le_bytes();
        bytes
            .as_ref()
            .iter()
            .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1 == 1))
            .collect()
    }

    /// Creates a field element from little-endian bits.
    ///
    /// Returns `None` if the resulting value is not in the canonical range.
    fn from_le_bits(bits: &[bool]) -> Option<Self> {
        let mut bytes = Self::Bytes::default();
        for (i, chunk) in bits.chunks(8).enumerate() {
            if i >= bytes.as_ref().len() {
                break;
            }
            bytes.as_mut()[i] =
                chunk.iter().enumerate().fold(0u8, |acc, (j, &bit)| acc | ((bit as u8) << j));
        }
        Self::from_le_bytes(bytes.as_ref())
    }

    /// Returns the field modulus as a [`BigUint`].
    fn modulus() -> BigUint {
        // Parse the MODULUS string, handling both "0x"-prefixed and non-prefixed formats.
        let modulus_str = Self::MODULUS;
        let hex_str = if modulus_str.starts_with("0x") || modulus_str.starts_with("0X") {
            &modulus_str[2..]
        } else {
            modulus_str
        };
        BigUint::parse_bytes(hex_str.as_bytes(), 16)
            .expect("PrimeField::MODULUS should be a valid hex string")
    }
}

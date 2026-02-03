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
//! ```
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
    /// Little-endian.
    LE,
    /// Big-endian.
    BE,
}

/// Extension trait for [`PrimeField`] providing explicit byte encoding methods.
pub trait FieldEncoding: PrimeField {
    /// Fixed-size byte array type for this field.
    //
    // This should be `[u8; BYTE_SIZE]`. We use an associated type because Rust
    // doesn't allow using associated constants as const generic parameters.
    type Bytes: Copy + Default + AsRef<[u8]> + AsMut<[u8]>;

    /// Endianness of the native `to_repr()` representation.
    //
    // This allows generic code to know how to interpret the bytes from
    // `PrimeField::to_repr()`.
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

/// Generic tests for FieldEncoding implementations.
#[cfg(test)]
pub mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    /// Tests that BE and LE byte conversions roundtrip correctly.
    pub fn test_bytes_roundtrip<F: FieldEncoding>() {
        let val = F::from(0x1234567890ABCDEFu64);

        // BE roundtrip.
        let be_bytes = val.to_be_bytes();
        let recovered = F::from_be_bytes(be_bytes.as_ref()).unwrap();
        assert_eq!(val, recovered, "BE roundtrip failed");

        // LE roundtrip.
        let le_bytes = val.to_le_bytes();
        let recovered = F::from_le_bytes(le_bytes.as_ref()).unwrap();
        assert_eq!(val, recovered, "LE roundtrip failed");
    }

    /// Tests that BigUint conversion roundtrips correctly.
    pub fn test_biguint_roundtrip<F: FieldEncoding>() {
        let val = F::from(0x1234567890ABCDEFu64);

        let big = val.to_biguint();
        let recovered = F::from_biguint(&big).unwrap();
        assert_eq!(val, recovered, "BigUint roundtrip failed");
    }

    /// Tests that LE and BE byte representations are consistent.
    pub fn test_endianness_consistency<F: FieldEncoding>() {
        let val = F::from(0x0102030405060708u64);
        let be_bytes = val.to_be_bytes();
        let le_bytes = val.to_le_bytes();

        // BE and LE should be reverses of each other.
        let mut reversed_le = le_bytes.as_ref().to_vec();
        reversed_le.reverse();
        assert_eq!(
            be_bytes.as_ref(),
            &reversed_le[..],
            "BE and LE should be byte-reversed"
        );
    }

    /// Tests roundtrip with random values.
    pub fn test_random_roundtrip<F: FieldEncoding>(seed: u64, iterations: usize) {
        let mut rng = XorShiftRng::seed_from_u64(seed);

        for _ in 0..iterations {
            let original = F::random(&mut rng);

            // Bytes roundtrip.
            let be_bytes = original.to_be_bytes();
            let recovered = F::from_be_bytes(be_bytes.as_ref()).unwrap();
            assert_eq!(original, recovered, "Random BE roundtrip failed");

            let le_bytes = original.to_le_bytes();
            let recovered = F::from_le_bytes(le_bytes.as_ref()).unwrap();
            assert_eq!(original, recovered, "Random LE roundtrip failed");

            // BigUint roundtrip.
            let big = original.to_biguint();
            let recovered = F::from_biguint(&big).unwrap();
            assert_eq!(original, recovered, "Random BigUint roundtrip failed");
        }
    }

    /// Tests that values outside the field are rejected.
    pub fn test_out_of_range<F: FieldEncoding>() {
        let modulus = F::modulus();

        // Modulus itself should be rejected.
        assert!(
            F::from_biguint(&modulus).is_none(),
            "Modulus should be out of range"
        );

        // Modulus + 1 should be rejected.
        let too_large = &modulus + 1u64;
        assert!(
            F::from_biguint(&too_large).is_none(),
            "Modulus + 1 should be out of range"
        );
    }

    /// Tests bit conversion roundtrip.
    pub fn test_bits_roundtrip<F: FieldEncoding>() {
        let val = F::from(0xDEADBEEFu64);

        let bits = val.to_le_bits();
        let recovered = F::from_le_bits(&bits).unwrap();
        assert_eq!(val, recovered, "Bits roundtrip failed");
    }

    /// Runs all standard FieldEncoding tests for a type.
    pub fn test_field_encoding<F: FieldEncoding>() {
        test_bytes_roundtrip::<F>();
        test_biguint_roundtrip::<F>();
        test_endianness_consistency::<F>();
        test_special_values::<F>();
        test_out_of_range::<F>();
        test_bits_roundtrip::<F>();
        test_random_roundtrip::<F>(0xCAFE, 10);
    }
}

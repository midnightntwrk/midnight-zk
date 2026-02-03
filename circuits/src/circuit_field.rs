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

//! Circuit-compatible prime field trait.
//!
//! This module defines [`CircuitField`], a trait that extends [`ff::PrimeField`]
//! with integer conversion methods required for limb decomposition and foreign
//! field arithmetic.
//!
//! # Example
//!
//! ```ignore
//! use crate::CircuitField;
//!
//! fn decompose_into_limbs<F: CircuitField>(value: F, limb_bits: usize) -> Vec<F> {
//!     let mut n = value.to_biguint();
//!     let base = BigUint::from(1u64) << limb_bits;
//!     let mut limbs = vec![];
//!     while !n.is_zero() {
//!         let limb = &n % &base;
//!         limbs.push(F::from_biguint(&limb).unwrap());
//!         n >>= limb_bits;
//!     }
//!     limbs
//! }
//! ```

use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::Num;

/// A prime field suitable for use as a circuit's native field.
///
/// Extends [`PrimeField`] with integer conversion methods required for limb
/// decomposition and foreign field arithmetic.
///
/// Implementations must handle endianness internally - callers should not need
/// to know whether the underlying field uses little-endian or big-endian
/// representation.
pub trait CircuitField: PrimeField {
    /// Converts the field element to a [`BigUint`].
    ///
    /// The returned value is in the canonical range `[0, modulus)`.
    fn to_biguint(&self) -> BigUint;

    /// Creates a field element from a [`BigUint`].
    ///
    /// Returns `None` if the value is not in the canonical range `[0, modulus)`.
    /// This method does **not** perform modular reduction.
    fn from_biguint(n: &BigUint) -> Option<Self>;

    /// Returns the field modulus as a [`BigUint`].
    fn modulus() -> BigUint;

    /// Converts the field element to little-endian bytes.
    ///
    /// The output length is the minimum number of bytes needed to represent
    /// any element of the field (i.e., `ceil(modulus_bits / 8)`).
    fn to_bytes_le(&self) -> Vec<u8> {
        let num_bytes = (Self::NUM_BITS as usize + 7) / 8;
        let mut bytes = self.to_biguint().to_bytes_le();
        bytes.resize(num_bytes, 0);
        bytes
    }

    /// Converts the field element to big-endian bytes.
    ///
    /// The output length is the minimum number of bytes needed to represent
    /// any element of the field (i.e., `ceil(modulus_bits / 8)`).
    fn to_bytes_be(&self) -> Vec<u8> {
        let num_bytes = (Self::NUM_BITS as usize + 7) / 8;
        let mut bytes = self.to_biguint().to_bytes_be();
        // Pad at the front for big-endian.
        while bytes.len() < num_bytes {
            bytes.insert(0, 0);
        }
        bytes
    }

    /// Creates a field element from little-endian bytes.
    ///
    /// Returns `None` if the value is not in the canonical range `[0, modulus)`.
    fn from_bytes_le(bytes: &[u8]) -> Option<Self> {
        let n = BigUint::from_bytes_le(bytes);
        Self::from_biguint(&n)
    }

    /// Creates a field element from big-endian bytes.
    ///
    /// Returns `None` if the value is not in the canonical range `[0, modulus)`.
    fn from_bytes_be(bytes: &[u8]) -> Option<Self> {
        let n = BigUint::from_bytes_be(bytes);
        Self::from_biguint(&n)
    }
}

// ============================================================================
// Macro for implementing CircuitField for little-endian fields
// ============================================================================

macro_rules! impl_circuit_field_le {
    ($field:ty, $repr_size:expr) => {
        impl CircuitField for $field {
            fn to_biguint(&self) -> BigUint {
                BigUint::from_bytes_le(self.to_repr().as_ref())
            }

            fn from_biguint(n: &BigUint) -> Option<Self> {
                let bytes = n.to_bytes_le();
                if bytes.len() > $repr_size {
                    return None;
                }
                let mut padded = [0u8; $repr_size];
                padded[..bytes.len()].copy_from_slice(&bytes);
                Self::from_repr(padded.into()).into()
            }

            fn modulus() -> BigUint {
                let hex_str = &Self::MODULUS[2..]; // Skip "0x" prefix.
                BigUint::from_str_radix(hex_str, 16).expect("Invalid modulus hex string")
            }
        }
    };
}

// ============================================================================
// Implementations for BLS12-381 fields (little-endian representation)
// ============================================================================

// Jubjub scalar field (Fr) - 255 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::Fr, 32);

// BLS12-381 scalar field (Fq) - 255 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::Fq, 32);

// BLS12-381 base field (Fp) - 381 bits, 48 bytes.
impl_circuit_field_le!(midnight_curves::Fp, 48);

// ============================================================================
// Implementations for secp256k1 fields (little-endian representation)
// ============================================================================

// secp256k1 base field (Fp) - 256 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::secp256k1::Fp, 32);

// secp256k1 scalar field (Fq) - 256 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::secp256k1::Fq, 32);

#[cfg(test)]
mod tests {
    use ff::Field;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;

    type F = midnight_curves::Fq;

    #[test]
    fn test_roundtrip_small_values() {
        for i in 0u64..1000 {
            let fe = F::from(i);
            let big = fe.to_biguint();
            assert_eq!(big, BigUint::from(i));

            let recovered = F::from_biguint(&big).unwrap();
            assert_eq!(fe, recovered);
        }
    }

    #[test]
    fn test_roundtrip_random_values() {
        let mut rng = ChaCha8Rng::seed_from_u64(0xCAFE);

        for _ in 0..100 {
            let fe = F::random(&mut rng);
            let big = fe.to_biguint();
            let recovered = F::from_biguint(&big).unwrap();
            assert_eq!(fe, recovered);
        }
    }

    #[test]
    fn test_modulus_rejected() {
        let modulus = F::modulus();
        assert!(F::from_biguint(&modulus).is_none());

        let too_large = &modulus + 1u64;
        assert!(F::from_biguint(&too_large).is_none());
    }

    #[test]
    fn test_zero() {
        let zero = F::ZERO;
        let big = zero.to_biguint();
        assert_eq!(big, BigUint::from(0u64));

        let recovered = F::from_biguint(&big).unwrap();
        assert_eq!(zero, recovered);
    }

    #[test]
    fn test_one() {
        let one = F::ONE;
        let big = one.to_biguint();
        assert_eq!(big, BigUint::from(1u64));

        let recovered = F::from_biguint(&big).unwrap();
        assert_eq!(one, recovered);
    }

    #[test]
    fn test_modulus_value() {
        // The modulus should be greater than 2^254 for BLS12-381.
        let modulus = F::modulus();
        let two_pow_254 = BigUint::from(1u64) << 254;
        assert!(modulus > two_pow_254);
    }

    #[test]
    fn test_bytes_le_roundtrip() {
        let mut rng = ChaCha8Rng::seed_from_u64(0xBEEF);

        for _ in 0..100 {
            let fe = F::random(&mut rng);
            let bytes = fe.to_bytes_le();
            assert_eq!(bytes.len(), 32); // BLS12-381 scalar is 255 bits = 32 bytes.
            let recovered = F::from_bytes_le(&bytes).unwrap();
            assert_eq!(fe, recovered);
        }
    }

    #[test]
    fn test_bytes_be_roundtrip() {
        let mut rng = ChaCha8Rng::seed_from_u64(0xDEAD);

        for _ in 0..100 {
            let fe = F::random(&mut rng);
            let bytes = fe.to_bytes_be();
            assert_eq!(bytes.len(), 32);
            let recovered = F::from_bytes_be(&bytes).unwrap();
            assert_eq!(fe, recovered);
        }
    }

    #[test]
    fn test_bytes_le_be_consistency() {
        let mut rng = ChaCha8Rng::seed_from_u64(0xFACE);

        for _ in 0..100 {
            let fe = F::random(&mut rng);
            let le = fe.to_bytes_le();
            let be = fe.to_bytes_be();

            // LE and BE should be reverses of each other.
            let mut le_reversed = le.clone();
            le_reversed.reverse();
            assert_eq!(le_reversed, be);
        }
    }

    #[test]
    fn test_bytes_small_values() {
        // Test that small values have correct byte representation.
        let one = F::ONE;
        let le = one.to_bytes_le();
        let be = one.to_bytes_be();

        assert_eq!(le[0], 1);
        assert!(le[1..].iter().all(|&b| b == 0));

        assert_eq!(be[31], 1);
        assert!(be[..31].iter().all(|&b| b == 0));
    }
}

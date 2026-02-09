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
//! field arithmetic. It also provides generic access to modulus fields.

use std::ops::Index;

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
    /// Byte length of the field representation.
    const NUM_BYTES: usize;

    /// Fixed-size byte array for the field representation, typically `[u8; NUM_BYTES]`.
    type Bytes: Copy + Send + Sync + 'static + AsRef<[u8]> + AsMut<[u8]> + Index<usize, Output = u8>;

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
    /// The output length is Self::NUM_BYTES.
    fn to_bytes_le(&self) -> Self::Bytes;

    /// Converts the field element to big-endian bytes.
    ///
    /// The output length is Self::NUM_BYTES.
    fn to_bytes_be(&self) -> Self::Bytes;

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

    /// Decomposes the field element into little-endian bits.
    ///
    /// - If `nb_bits = None`, the output has as many bits as necessary to
    ///   represent the element, but no more.
    /// - If `nb_bits` is provided, the output has the specified length,
    ///   possibly with trailing zeros.
    ///
    /// # Panics
    ///
    /// If the element does not fit in `nb_bits` bits when such argument is
    /// provided.
    fn to_le_bits(&self, nb_bits: Option<usize>) -> Vec<bool> {
        let big = self.to_biguint();
        let mut bits: Vec<bool> = (0..big.bits()).map(|i| big.bit(i)).collect();
        if let Some(n) = nb_bits {
            assert!(n >= bits.len());
            bits.resize(n, false);
        }
        bits
    }

    /// Creates a field element from a little-endian bitstring.
    ///
    /// # Panics
    ///
    /// If `bits.len() > Self::NUM_BITS`.
    fn from_le_bits(bits: &[bool]) -> Self {
        assert!(bits.len() as u32 <= Self::NUM_BITS);
        let bytes: Vec<u8> = bits
            .chunks(8)
            .map(|chunk| {
                chunk
                    .iter()
                    .enumerate()
                    .fold(0u8, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
            })
            .collect();
        Self::from_bytes_le(&bytes).unwrap()
    }
}

// Macro for implementing CircuitField for LE and BE fields
// =========================================================

macro_rules! impl_circuit_field_le {
    ($field:ty, $repr_size:expr) => {
        impl CircuitField for $field {
            const NUM_BYTES: usize = $repr_size;
            type Bytes = [u8; $repr_size];

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

            fn to_bytes_le(&self) -> Self::Bytes {
                let mut bytes = [0u8; $repr_size];
                bytes.copy_from_slice(self.to_repr().as_ref());
                bytes
            }

            fn to_bytes_be(&self) -> Self::Bytes {
                let mut bytes = [0u8; $repr_size];
                bytes.copy_from_slice(self.to_repr().as_ref());
                bytes.reverse();
                bytes
            }
        }
    };
}

// Note: Will be used for k256.
// macro_rules! impl_circuit_field_be {
//     ($field:ty, $repr_size:expr) => {
//         impl CircuitField for $field {
//             const NUM_BYTES: usize = $repr_size;
//             type Bytes = [u8; $repr_size];
//
//             fn to_biguint(&self) -> BigUint {
//                 BigUint::from_bytes_be(self.to_repr().as_ref())
//             }
//
//             fn from_biguint(n: &BigUint) -> Option<Self> {
//                 let bytes = n.to_bytes_be();
//                 if bytes.len() > $repr_size {
//                     return None;
//                 }
//                 let mut padded = [0u8; $repr_size];
//                 padded[..bytes.len()].copy_from_slice(&bytes);
//                 Self::from_repr(padded.into()).into()
//             }
//
//             fn modulus() -> BigUint {
//                 let hex_str = &Self::MODULUS[2..]; // Skip "0x" prefix.
//                 BigUint::from_str_radix(hex_str, 16).expect("Invalid modulus hex string")
//             }
//
//             fn to_bytes_le(&self) -> Self::Bytes {
//                 let mut bytes = [0u8; $repr_size];
//                 bytes.copy_from_slice(self.to_repr().as_ref());
//                 bytes.reverse();
//                 bytes
//             }
//
//             fn to_bytes_be(&self) -> Self::Bytes {
//                 let mut bytes = [0u8; $repr_size];
//                 bytes.copy_from_slice(self.to_repr().as_ref());
//                 bytes
//             }
//         }
//     };
// }

// Implementations for BLS12-381 fields
// =====================================

// Jubjub scalar field (Fr) - 255 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::Fr, 32);

// BLS12-381 scalar field, Jubjub base field (Fq) - 255 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::Fq, 32);

// BLS12-381 base field (Fp) - 381 bits, 48 bytes.
impl_circuit_field_le!(midnight_curves::Fp, 48);

// Implementations for secp256k1 fields
// =====================================

// secp256k1 base field (Fp) - 256 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::secp256k1::Fp, 32);

// secp256k1 scalar field (Fq) - 256 bits, 32 bytes.
impl_circuit_field_le!(midnight_curves::secp256k1::Fq, 32);

// Implementations for BN256 fields
// ====================================

// BN256 base field (Fq) - 254 bits, 32 bytes.
#[cfg(feature = "dev-curves")]
impl_circuit_field_le!(midnight_curves::bn256::Fq, 32);

// BN256 scalar field (Fr) - 254 bits, 32 bytes.
#[cfg(feature = "dev-curves")]
impl_circuit_field_le!(midnight_curves::bn256::Fr, 32);

#[cfg(test)]
mod tests {
    use ff::Field;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;

    type F = midnight_curves::Fq;

    #[test]
    fn test_biguint_roundtrip() {
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
}

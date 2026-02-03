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

//! Safe wrapper around k256::FieldElement.
//!
//! k256's FieldElement uses lazy reduction, meaning field elements may not be
//! in canonical form after arithmetic operations. This wrapper ensures that
//! comparison and predicate methods normalize before operating, eliminating
//! the risk of incorrect results.
//!
//! See: <https://github.com/RustCrypto/elliptic-curves/issues/531>

use core::{
    convert::TryInto,
    iter::{Product, Sum},
    mem::size_of,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use ff::{Field, PrimeField};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// secp256k1 base field element with safe comparison semantics.
///
/// This wrapper normalizes field elements before comparison and predicate
/// operations to ensure correct results regardless of internal representation.
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct Fp(pub(crate) k256::FieldElement);

impl Fp {
    /// The zero element.
    pub const ZERO: Self = Self(k256::FieldElement::ZERO);

    /// The multiplicative identity.
    pub const ONE: Self = Self(k256::FieldElement::ONE);

    /// Returns the inner k256::FieldElement.
    #[inline]
    pub fn inner(&self) -> &k256::FieldElement {
        &self.0
    }

    /// Consumes the wrapper and returns the inner k256::FieldElement.
    #[inline]
    pub fn into_inner(self) -> k256::FieldElement {
        self.0
    }

    /// Normalizes the field element to canonical form.
    #[inline]
    pub fn normalize(&self) -> Self {
        Self(self.0.normalize())
    }

    /// Normalizes in place.
    #[inline]
    pub fn normalize_mut(&mut self) {
        self.0 = self.0.normalize();
    }
}

// ============================================================================
// Safe predicate methods (normalize before checking)
// ============================================================================

impl Fp {
    /// Returns true if this element is zero.
    /// Normalizes before checking to ensure correct result.
    #[inline]
    pub fn is_zero(&self) -> Choice {
        self.0.normalize().is_zero()
    }

    /// Returns true if this element is odd.
    /// Normalizes before checking to ensure correct result.
    #[inline]
    pub fn is_odd(&self) -> Choice {
        self.0.normalize().is_odd()
    }

    /// Returns true if this element is even.
    /// Normalizes before checking to ensure correct result.
    #[inline]
    pub fn is_even(&self) -> Choice {
        self.0.normalize().is_even()
    }
}

// ============================================================================
// Safe comparison (normalize before comparing)
// ============================================================================

impl PartialEq for Fp {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.normalize().ct_eq(&other.0.normalize()).into()
    }
}

impl Eq for Fp {}

impl ConstantTimeEq for Fp {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.normalize().ct_eq(&other.0.normalize())
    }
}

impl ConditionallySelectable for Fp {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(k256::FieldElement::conditional_select(&a.0, &b.0, choice))
    }
}

// ============================================================================
// Arithmetic (delegate to inner type)
// ============================================================================

impl Add for Fp {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<&Fp> for Fp {
    type Output = Self;
    #[inline]
    fn add(self, rhs: &Fp) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl AddAssign for Fp {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl AddAssign<&Fp> for Fp {
    #[inline]
    fn add_assign(&mut self, rhs: &Fp) {
        self.0 += rhs.0;
    }
}

impl Sub for Fp {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<&Fp> for Fp {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: &Fp) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for Fp {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<&Fp> for Fp {
    #[inline]
    fn sub_assign(&mut self, rhs: &Fp) {
        self.0 -= rhs.0;
    }
}

impl Mul for Fp {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(self.0 * rhs.0)
    }
}

impl Mul<&Fp> for Fp {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: &Fp) -> Self {
        Self(self.0 * rhs.0)
    }
}

impl MulAssign for Fp {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

impl MulAssign<&Fp> for Fp {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fp) {
        self.0 *= rhs.0;
    }
}

impl Neg for Fp {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Neg for &Fp {
    type Output = Fp;
    #[inline]
    fn neg(self) -> Fp {
        Fp(-self.0)
    }
}

// ============================================================================
// Sum and Product traits (required by Field)
// ============================================================================

impl Sum for Fp {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a Fp> for Fp {
    fn sum<I: Iterator<Item = &'a Fp>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl Product for Fp {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

impl<'a> Product<&'a Fp> for Fp {
    fn product<I: Iterator<Item = &'a Fp>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x)
    }
}

// ============================================================================
// Field trait implementation
// ============================================================================

impl Field for Fp {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;

    fn random(rng: impl rand_core::RngCore) -> Self {
        Self(k256::FieldElement::random(rng))
    }

    fn square(&self) -> Self {
        Self(self.0.square())
    }

    fn double(&self) -> Self {
        Self(self.0.double())
    }

    fn invert(&self) -> CtOption<Self> {
        self.0.invert().map(Self)
    }

    fn sqrt(&self) -> CtOption<Self> {
        self.0.sqrt().map(Self)
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        let (choice, result) = k256::FieldElement::sqrt_ratio(&num.0, &div.0);
        (choice, Self(result))
    }
}

// ============================================================================
// PrimeField trait implementation
// ============================================================================

impl PrimeField for Fp {
    type Repr = k256::FieldBytes;

    const MODULUS: &'static str = <k256::FieldElement as PrimeField>::MODULUS;
    const NUM_BITS: u32 = <k256::FieldElement as PrimeField>::NUM_BITS;
    const CAPACITY: u32 = <k256::FieldElement as PrimeField>::CAPACITY;
    const TWO_INV: Self = Self(<k256::FieldElement as PrimeField>::TWO_INV);
    const MULTIPLICATIVE_GENERATOR: Self =
        Self(<k256::FieldElement as PrimeField>::MULTIPLICATIVE_GENERATOR);
    const S: u32 = <k256::FieldElement as PrimeField>::S;
    const ROOT_OF_UNITY: Self = Self(<k256::FieldElement as PrimeField>::ROOT_OF_UNITY);
    const ROOT_OF_UNITY_INV: Self = Self(<k256::FieldElement as PrimeField>::ROOT_OF_UNITY_INV);
    const DELTA: Self = Self(<k256::FieldElement as PrimeField>::DELTA);

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        k256::FieldElement::from_repr(repr).map(Self)
    }

    fn to_repr(&self) -> Self::Repr {
        // to_repr normalizes internally, so this is safe.
        self.0.to_repr()
    }

    fn is_odd(&self) -> Choice {
        // Use our safe normalized version.
        Fp::is_odd(self)
    }
}

// ============================================================================
// Conversions
// ============================================================================

impl From<k256::FieldElement> for Fp {
    #[inline]
    fn from(fe: k256::FieldElement) -> Self {
        Self(fe)
    }
}

impl From<Fp> for k256::FieldElement {
    #[inline]
    fn from(fp: Fp) -> Self {
        fp.0
    }
}

impl From<u64> for Fp {
    #[inline]
    fn from(val: u64) -> Self {
        Self(k256::FieldElement::from(val))
    }
}

impl Fp {
    /// Create a field element from a u64 value.
    #[inline]
    pub const fn from_u64(val: u64) -> Self {
        Self(k256::FieldElement::from_u64(val))
    }
}

impl Fp {
    /// Create a field element from bytes (big-endian).
    #[inline]
    pub fn from_bytes(bytes: &k256::FieldBytes) -> CtOption<Self> {
        k256::FieldElement::from_bytes(bytes).map(Self)
    }

    /// Serialize to bytes (big-endian). Normalizes internally.
    #[inline]
    pub fn to_bytes(&self) -> k256::FieldBytes {
        self.0.to_bytes()
    }
}

// ============================================================================
// FieldEncoding trait implementation
// ============================================================================

impl crate::FieldEncoding for Fp {
    type Bytes = [u8; 32];

    const REPR_ENDIAN: crate::Endian = crate::Endian::BE;

    fn to_le_bytes(&self) -> Self::Bytes {
        let mut bytes: [u8; 32] = self.to_bytes().into();
        bytes.reverse();
        bytes
    }

    fn to_be_bytes(&self) -> Self::Bytes {
        self.to_bytes().into()
    }

    fn from_le_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != size_of::<Self::Repr>() {
            return None;
        }
        let mut be_bytes = [0u8; 32];
        be_bytes.copy_from_slice(bytes);
        be_bytes.reverse();
        Self::from_bytes(&k256::FieldBytes::from(be_bytes)).into()
    }

    fn from_be_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != size_of::<Self::Repr>() {
            return None;
        }
        let be_bytes: [u8; 32] = bytes.try_into().ok()?;
        Self::from_bytes(&k256::FieldBytes::from(be_bytes)).into()
    }

    fn to_biguint(&self) -> num_bigint::BigUint {
        num_bigint::BigUint::from_bytes_be(&self.to_be_bytes())
    }

    fn from_biguint(n: &num_bigint::BigUint) -> Option<Self> {
        let bytes = n.to_bytes_be();
        if bytes.len() > size_of::<Self::Repr>() {
            return None;
        }
        // Pad with leading zeros for big-endian.
        let mut padded = [0u8; 32];
        padded[32 - bytes.len()..].copy_from_slice(&bytes);
        Self::from_be_bytes(&padded)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field_encoding::tests as encoding_tests;

    // ========================================================================
    // k256-specific tests for normalization safety
    // ========================================================================

    /// k256::FieldElement.is_zero() panics on unnormalized input.
    /// In release builds, it would return incorrect results instead of panicking.
    #[test]
    #[should_panic(expected = "assertion failed: self.normalized")]
    fn test_raw_k256_is_zero_panics_without_normalize() {
        let raw_a = k256::FieldElement::from(12345u64);
        let raw_zero = raw_a - raw_a;
        // This panics in debug builds because raw_zero is not normalized.
        let _ = raw_zero.is_zero();
    }

    #[test]
    fn test_zero_after_subtraction() {
        let a = Fp::from(12345u64);
        let zero = a - a;

        assert!(bool::from(zero.is_zero()));
        assert_eq!(zero, Fp::ZERO);
    }

    /// k256::FieldElement.is_odd() panics on unnormalized input.
    #[test]
    #[should_panic(expected = "assertion failed: self.normalized")]
    fn test_raw_k256_is_odd_panics_without_normalize() {
        let raw_a = k256::FieldElement::from(100u64);
        let raw_b = k256::FieldElement::from(97u64);
        // Subtraction produces unnormalized results. 100 - 97 = 3 (odd).
        let diff = raw_a - raw_b;
        // This panics in debug builds because diff is not normalized.
        let _ = diff.is_odd();
    }

    #[test]
    fn test_is_odd_after_subtraction() {
        let raw_a = Fp::from(100u64);
        let raw_b = Fp::from(97u64);
        let diff = raw_a - raw_b;
        assert!(bool::from(diff.is_odd()));
    }

    #[test]
    fn test_equality_after_multiplication() {
        const ZETA_BYTES: [u8; 32] = [
            0x7a, 0xe9, 0x6a, 0x2b, 0x65, 0x7c, 0x07, 0x10, 0x6e, 0x64, 0x47, 0x9e, 0xac, 0x34,
            0x34, 0xe9, 0x9c, 0xf0, 0x49, 0x75, 0x12, 0xf5, 0x89, 0x95, 0xc1, 0x39, 0x6c, 0x28,
            0x71, 0x95, 0x01, 0xee,
        ];
        let zeta = Fp::from_bytes(&k256::FieldBytes::from(ZETA_BYTES)).expect("Valid ZETA bytes");
        let zeta_cube = zeta * zeta * zeta;
        assert_eq!(zeta_cube, Fp::ONE);
    }

    // ========================================================================
    // Generic FieldEncoding tests
    // ========================================================================

    #[test]
    fn test_field_encoding() {
        encoding_tests::test_field_encoding::<Fp>();
    }
}

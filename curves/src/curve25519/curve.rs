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

//! Curve25519 circuit integration.
//!
//! This module provides a wrapper around curve25519_dalek's EdwardsPoint
//! to implement the traits required for circuit usage.
//! Currently, this is necessary because group::Curve is a requirement for
//! CircuitCurve and this trait cannot be implemented for the foreign
//! EdwardsPoint.

use core::{
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use curve25519_dalek::{edwards::CompressedEdwardsY, EdwardsPoint};
use group::{Group, GroupEncoding};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use super::{affine::Curve25519Affine, Fp, Scalar};

/// Macro to implement common traits for Edwards curve point wrappers.
macro_rules! impl_edwards_curve_ops {
    ($type:ident) => {
        impl PartialEq for $type {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq for $type {}

        impl ConstantTimeEq for $type {
            fn ct_eq(&self, other: &Self) -> Choice {
                self.0.ct_eq(&other.0)
            }
        }

        impl ConditionallySelectable for $type {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $type(EdwardsPoint::conditional_select(&a.0, &b.0, choice))
            }
        }

        impl Add for $type {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                $type(self.0 + rhs.0)
            }
        }

        impl<'a> Add<&'a $type> for $type {
            type Output = Self;
            fn add(self, rhs: &'a $type) -> Self {
                $type(self.0 + rhs.0)
            }
        }

        impl Add<$type> for &$type {
            type Output = $type;
            fn add(self, rhs: $type) -> $type {
                $type(self.0 + rhs.0)
            }
        }

        impl<'a> Add<&'a $type> for &$type {
            type Output = $type;
            fn add(self, rhs: &'a $type) -> $type {
                $type(self.0 + rhs.0)
            }
        }

        impl Sub for $type {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self {
                $type(self.0 - rhs.0)
            }
        }

        impl<'a> Sub<&'a $type> for $type {
            type Output = Self;
            fn sub(self, rhs: &'a $type) -> Self {
                $type(self.0 - rhs.0)
            }
        }

        impl Neg for $type {
            type Output = Self;
            fn neg(self) -> Self {
                $type(-self.0)
            }
        }

        impl Neg for &$type {
            type Output = $type;
            fn neg(self) -> $type {
                $type(-self.0)
            }
        }

        impl Mul<Scalar> for $type {
            type Output = Self;
            fn mul(self, rhs: Scalar) -> Self {
                $type(self.0 * rhs)
            }
        }

        impl<'a> Mul<&'a Scalar> for $type {
            type Output = Self;
            fn mul(self, rhs: &'a Scalar) -> Self {
                $type(self.0 * rhs)
            }
        }

        impl Mul<$type> for Scalar {
            type Output = $type;
            fn mul(self, rhs: $type) -> $type {
                $type(self * rhs.0)
            }
        }

        impl<'a> Mul<&'a $type> for Scalar {
            type Output = $type;
            fn mul(self, rhs: &'a $type) -> $type {
                $type(self * rhs.0)
            }
        }

        impl AddAssign for $type {
            fn add_assign(&mut self, rhs: Self) {
                self.0 += rhs.0;
            }
        }

        impl<'a> AddAssign<&'a $type> for $type {
            fn add_assign(&mut self, rhs: &'a $type) {
                self.0 += rhs.0;
            }
        }

        impl SubAssign for $type {
            fn sub_assign(&mut self, rhs: Self) {
                self.0 -= rhs.0;
            }
        }

        impl<'a> SubAssign<&'a $type> for $type {
            fn sub_assign(&mut self, rhs: &'a $type) {
                self.0 -= rhs.0;
            }
        }

        impl MulAssign<Scalar> for $type {
            fn mul_assign(&mut self, rhs: Scalar) {
                self.0 *= rhs;
            }
        }

        impl<'a> MulAssign<&'a Scalar> for $type {
            fn mul_assign(&mut self, rhs: &'a Scalar) {
                self.0 *= rhs;
            }
        }

        impl Sum for $type {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold($type::identity(), |acc, x| acc + x)
            }
        }

        impl<'a> Sum<&'a $type> for $type {
            fn sum<I: Iterator<Item = &'a $type>>(iter: I) -> Self {
                iter.fold($type::identity(), |acc, x| acc + x)
            }
        }
    };
}

/// A = -1 for Curve25519 (twisted Edwards form: a*x² + y² = 1 + d*x²*y²).
pub const CURVE_A: Fp = Fp::from_raw([
    0xffffffffffffffec,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x7fffffffffffffff,
]);

/// D = -(121665/121666) for Curve25519.
pub const CURVE_D: Fp = Fp::from_raw([
    0x75eb4dca135978a3,
    0x00700a4d4141d8ab,
    0x8cc740797779e898,
    0x52036cee2b6ffe73,
]);

/// EdwardsPoint wrapper for circuit integration.
#[derive(Copy, Clone, Debug, Default)]
pub struct Curve25519(pub EdwardsPoint);

/// Curve25519 point guaranteed to be in the prime-order subgroup.
/// This type can only be constructed via `Curve25519::into_subgroup()` which
/// verifies that the point is torsion-free.
#[derive(Copy, Clone, Debug, Default)]
pub struct Curve25519Subgroup(pub(crate) EdwardsPoint);

impl Curve25519Subgroup {
    /// Returns the underlying EdwardsPoint.
    pub fn inner(&self) -> &EdwardsPoint {
        &self.0
    }

    /// Returns Some(point) if the point is in the prime-order subgroup, None
    /// otherwise.
    pub fn from_edwards(point: EdwardsPoint) -> Option<Self> {
        // Use the is_torsion_free method from curve25519_dalek.
        if point.is_torsion_free() {
            Some(Curve25519Subgroup(point))
        } else {
            None
        }
    }
}

impl_edwards_curve_ops!(Curve25519Subgroup);

impl Group for Curve25519Subgroup {
    type Scalar = Scalar;

    fn random(mut rng: impl rand_core::RngCore) -> Self {
        // Generate a random point and clear cofactor to ensure it's in subgroup.
        let point = EdwardsPoint::random(&mut rng);
        Curve25519Subgroup(point.mul_by_cofactor())
    }

    fn identity() -> Self {
        Curve25519Subgroup(EdwardsPoint::identity())
    }

    fn generator() -> Self {
        Curve25519Subgroup(curve25519_dalek::constants::ED25519_BASEPOINT_POINT)
    }

    fn is_identity(&self) -> Choice {
        self.0.is_identity()
    }

    fn double(&self) -> Self {
        Curve25519Subgroup(self.0.double())
    }
}

/// Conversion from Curve25519Subgroup to Curve25519 (always valid).
impl From<Curve25519Subgroup> for Curve25519 {
    fn from(p: Curve25519Subgroup) -> Self {
        Curve25519(p.0)
    }
}

/// Reference conversion from Curve25519Subgroup to Curve25519.
impl From<&Curve25519Subgroup> for Curve25519 {
    fn from(p: &Curve25519Subgroup) -> Self {
        Curve25519(p.0)
    }
}

impl_edwards_curve_ops!(Curve25519);

// Operations with affine representation
impl Add<Curve25519Affine> for Curve25519 {
    type Output = Curve25519;
    fn add(self, rhs: Curve25519Affine) -> Curve25519 {
        self + Curve25519::from(rhs)
    }
}

impl<'a> Add<&'a Curve25519Affine> for Curve25519 {
    type Output = Curve25519;
    fn add(self, rhs: &'a Curve25519Affine) -> Curve25519 {
        self + Curve25519::from(*rhs)
    }
}

impl Sub<Curve25519Affine> for Curve25519 {
    type Output = Curve25519;
    fn sub(self, rhs: Curve25519Affine) -> Curve25519 {
        self - Curve25519::from(rhs)
    }
}

impl<'a> Sub<&'a Curve25519Affine> for Curve25519 {
    type Output = Curve25519;
    fn sub(self, rhs: &'a Curve25519Affine) -> Curve25519 {
        self - Curve25519::from(*rhs)
    }
}

impl AddAssign<Curve25519Affine> for Curve25519 {
    fn add_assign(&mut self, rhs: Curve25519Affine) {
        *self += Curve25519::from(rhs);
    }
}

impl<'a> AddAssign<&'a Curve25519Affine> for Curve25519 {
    fn add_assign(&mut self, rhs: &'a Curve25519Affine) {
        *self += Curve25519::from(*rhs);
    }
}

impl SubAssign<Curve25519Affine> for Curve25519 {
    fn sub_assign(&mut self, rhs: Curve25519Affine) {
        *self -= Curve25519::from(rhs);
    }
}

impl<'a> SubAssign<&'a Curve25519Affine> for Curve25519 {
    fn sub_assign(&mut self, rhs: &'a Curve25519Affine) {
        *self -= Curve25519::from(*rhs);
    }
}

// Implement group
impl Group for Curve25519 {
    type Scalar = Scalar;

    fn random(mut rng: impl rand_core::RngCore) -> Self {
        Curve25519(EdwardsPoint::random(&mut rng))
    }

    fn identity() -> Self {
        Curve25519(EdwardsPoint::identity())
    }

    fn generator() -> Self {
        Curve25519(curve25519_dalek::constants::ED25519_BASEPOINT_POINT)
    }

    fn is_identity(&self) -> Choice {
        self.0.is_identity()
    }

    fn double(&self) -> Self {
        Curve25519(self.0.double())
    }
}

impl group::Curve for Curve25519 {
    type AffineRepr = Curve25519Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        Curve25519Affine::from_edwards(self.0)
    }

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        assert_eq!(p.len(), q.len());
        for (proj, affine) in p.iter().zip(q.iter_mut()) {
            *affine = proj.to_affine();
        }
    }
}

// Implement GroupEncoding
impl GroupEncoding for Curve25519 {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let compressed = CompressedEdwardsY(*bytes);
        match compressed.decompress() {
            Some(point) => CtOption::new(Curve25519(point), Choice::from(1u8)),
            None => CtOption::new(Curve25519(EdwardsPoint::identity()), Choice::from(0u8)),
        }
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.compress().to_bytes()
    }
}

#[cfg(test)]
mod tests {
    use group::Group;

    use super::*;

    #[test]
    fn test_identity() {
        let id = Curve25519::identity();
        let gen = Curve25519::generator();

        assert_eq!(id + gen, gen);
        assert_eq!(gen - gen, id);
    }

    #[test]
    fn test_scalar_mul() {
        let gen = Curve25519::generator();
        let scalar = Scalar::from(42u64);
        let result = gen * scalar;

        // Check it's not identity
        assert_ne!(result, Curve25519::identity());
    }

    #[test]
    fn test_doubling() {
        let gen = Curve25519::generator();
        let doubled = gen.double();
        let added = gen + gen;

        assert_eq!(doubled, added);
    }

    #[test]
    fn test_encoding() {
        let gen = Curve25519::generator();
        let bytes = gen.to_bytes();
        let decoded = Curve25519::from_bytes(&bytes).unwrap();

        assert_eq!(gen, decoded);
    }

    #[test]
    fn test_default() {
        // The wrapper Curve25519Affine requires that EdwardsPoint::default()
        // returns the identity for consistency.

        let default = EdwardsPoint::default();
        let id = EdwardsPoint::identity();

        assert_eq!(id, default);
    }
}

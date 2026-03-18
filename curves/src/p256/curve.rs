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

//! NIST P-256 / secp256r1 curve types using p256.

use ff::Field as FfField;
use group::{Curve, Group, GroupEncoding};
use p256::{
    elliptic_curve::{
        ff::PrimeField as P256PrimeField,
        group::GroupEncoding as P256GroupEncoding,
        point::AffineCoordinates,
        sec1::{FromEncodedPoint, ToEncodedPoint},
        Group as P256Group,
    },
    AffinePoint, ProjectivePoint,
};
use subtle::{Choice, CtOption};

use super::{Fp, Fq};

/// NIST P-256 curve point in projective coordinates.
#[derive(Clone, Copy, Debug, Default)]
pub struct P256(pub ProjectivePoint);

/// NIST P-256 curve point in affine coordinates.
#[derive(Clone, Copy, Debug)]
pub struct P256Affine(pub AffinePoint);

impl P256 {
    /// Returns the identity point.
    pub fn identity() -> Self {
        Self(ProjectivePoint::IDENTITY)
    }

    /// Returns the designated generator.
    pub fn generator() -> Self {
        Self(ProjectivePoint::GENERATOR)
    }
}

impl P256Affine {
    /// Returns the identity point.
    pub fn identity() -> Self {
        Self(AffinePoint::IDENTITY)
    }

    /// Returns the generator point.
    pub fn generator() -> Self {
        Self(AffinePoint::GENERATOR)
    }

    /// Returns the x coordinate for non-identity points, or `None` for the
    /// identity.
    pub fn try_x(&self) -> Option<Fp> {
        if bool::from(self.0.is_identity()) {
            return None;
        }
        Option::from(<Fp as P256PrimeField>::from_repr(self.0.x()))
    }

    /// Returns the y coordinate for non-identity points, or `None` for the
    /// identity.
    pub fn try_y(&self) -> Option<Fp> {
        if bool::from(self.0.is_identity()) {
            return None;
        }

        // Use uncompressed encoding to get y coordinate.
        let encoded = self.0.to_encoded_point(false);
        let y_bytes = encoded.y()?;
        Option::from(<Fp as P256PrimeField>::from_repr(*y_bytes))
    }

    /// Creates an affine point from x and y coordinates.
    pub fn from_xy(x: Fp, y: Fp) -> Option<Self> {
        // Use uncompressed SEC1 encoding to avoid sqrt during decompression.
        let encoded = p256::EncodedPoint::from_affine_coordinates(
            &x.to_repr(),
            &y.to_repr(),
            false, // Don't compress - we have both coordinates.
        );

        // from_encoded_point validates the point is on the curve.
        AffinePoint::from_encoded_point(&encoded).into_option().map(Self)
    }
}

impl Default for P256Affine {
    fn default() -> Self {
        Self::identity()
    }
}

// ============================================================================
// Group and Curve trait implementations
// ============================================================================

impl Group for P256 {
    type Scalar = Fq;

    fn random(mut rng: impl rand_core::RngCore) -> Self {
        // Generate a random scalar and multiply the generator.
        let scalar = <Fq as FfField>::random(&mut rng);
        Self::generator() * scalar
    }

    fn identity() -> Self {
        Self(ProjectivePoint::IDENTITY)
    }

    fn generator() -> Self {
        Self(ProjectivePoint::GENERATOR)
    }

    fn is_identity(&self) -> Choice {
        <ProjectivePoint as P256Group>::is_identity(&self.0)
    }

    fn double(&self) -> Self {
        Self(self.0.double())
    }
}

impl Curve for P256 {
    type AffineRepr = P256Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        P256Affine(self.0.to_affine())
    }
}

// ============================================================================
// CompressedPoint wrapper and GroupEncoding
// ============================================================================

// GroupEncoding requires Repr: Default which [u8; 33] doesn't implement.
// We use a wrapper type instead.
#[derive(Clone, Copy, Debug)]
pub struct CompressedPoint([u8; 33]);

impl Default for CompressedPoint {
    fn default() -> Self {
        Self([0u8; 33])
    }
}

impl AsRef<[u8]> for CompressedPoint {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for CompressedPoint {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl From<[u8; 33]> for CompressedPoint {
    fn from(bytes: [u8; 33]) -> Self {
        Self(bytes)
    }
}

impl From<CompressedPoint> for [u8; 33] {
    fn from(cp: CompressedPoint) -> Self {
        cp.0
    }
}

impl GroupEncoding for P256 {
    type Repr = CompressedPoint;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let compressed = p256::CompressedPoint::from(bytes.0);
        <ProjectivePoint as P256GroupEncoding>::from_bytes(&compressed).map(Self)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        let bytes: [u8; 33] = <ProjectivePoint as P256GroupEncoding>::to_bytes(&self.0).into();
        CompressedPoint(bytes)
    }
}

impl GroupEncoding for P256Affine {
    type Repr = CompressedPoint;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let compressed = p256::CompressedPoint::from(bytes.0);
        <AffinePoint as P256GroupEncoding>::from_bytes(&compressed).map(Self)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        let bytes: [u8; 33] = <AffinePoint as P256GroupEncoding>::to_bytes(&self.0).into();
        CompressedPoint(bytes)
    }
}

// ============================================================================
// Pure wrapper trait implementations (delegate to inner type)
// ============================================================================

use core::{
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use subtle::{ConditionallySelectable, ConstantTimeEq};

impl PartialEq for P256 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for P256 {}

impl PartialEq for P256Affine {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for P256Affine {}

impl ConstantTimeEq for P256 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConstantTimeEq for P256Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for P256 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(ProjectivePoint::conditional_select(&a.0, &b.0, choice))
    }
}

impl ConditionallySelectable for P256Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(AffinePoint::conditional_select(&a.0, &b.0, choice))
    }
}

// Arithmetic operations for P256.
impl Add for P256 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<&P256> for P256 {
    type Output = Self;
    fn add(self, rhs: &P256) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<P256Affine> for P256 {
    type Output = Self;
    fn add(self, rhs: P256Affine) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<&P256Affine> for P256 {
    type Output = Self;
    fn add(self, rhs: &P256Affine) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl AddAssign for P256 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl AddAssign<&P256> for P256 {
    fn add_assign(&mut self, rhs: &P256) {
        self.0 += rhs.0;
    }
}

impl AddAssign<P256Affine> for P256 {
    fn add_assign(&mut self, rhs: P256Affine) {
        self.0 += rhs.0;
    }
}

impl AddAssign<&P256Affine> for P256 {
    fn add_assign(&mut self, rhs: &P256Affine) {
        self.0 += rhs.0;
    }
}

impl Sub for P256 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<&P256> for P256 {
    type Output = Self;
    fn sub(self, rhs: &P256) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<P256Affine> for P256 {
    type Output = Self;
    fn sub(self, rhs: P256Affine) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<&P256Affine> for P256 {
    type Output = Self;
    fn sub(self, rhs: &P256Affine) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for P256 {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<&P256> for P256 {
    fn sub_assign(&mut self, rhs: &P256) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<P256Affine> for P256 {
    fn sub_assign(&mut self, rhs: P256Affine) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<&P256Affine> for P256 {
    fn sub_assign(&mut self, rhs: &P256Affine) {
        self.0 -= rhs.0;
    }
}

impl Neg for P256 {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Neg for &P256 {
    type Output = P256;
    fn neg(self) -> P256 {
        P256(-self.0)
    }
}

// Scalar multiplication.
impl Mul<Fq> for P256 {
    type Output = Self;
    fn mul(self, rhs: Fq) -> Self {
        Self(self.0 * rhs)
    }
}

impl Mul<&Fq> for P256 {
    type Output = Self;
    fn mul(self, rhs: &Fq) -> Self {
        Self(self.0 * rhs)
    }
}

impl Mul<P256> for Fq {
    type Output = P256;
    fn mul(self, rhs: P256) -> P256 {
        P256(rhs.0 * self)
    }
}

impl Mul<&P256> for Fq {
    type Output = P256;
    fn mul(self, rhs: &P256) -> P256 {
        P256(rhs.0 * self)
    }
}

impl MulAssign<Fq> for P256 {
    fn mul_assign(&mut self, rhs: Fq) {
        self.0 *= rhs;
    }
}

impl MulAssign<&Fq> for P256 {
    fn mul_assign(&mut self, rhs: &Fq) {
        self.0 *= rhs;
    }
}

// Sum trait.
impl Sum for P256 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(P256::identity(), |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a P256> for P256 {
    fn sum<I: Iterator<Item = &'a P256>>(iter: I) -> Self {
        iter.fold(P256::identity(), |acc, x| acc + x)
    }
}

// Conversions between P256 and P256Affine.
impl From<P256Affine> for P256 {
    fn from(affine: P256Affine) -> Self {
        Self(affine.0.into())
    }
}

impl From<&P256Affine> for P256 {
    fn from(affine: &P256Affine) -> Self {
        Self(affine.0.into())
    }
}

impl From<P256> for P256Affine {
    fn from(proj: P256) -> Self {
        proj.to_affine()
    }
}

impl From<&P256> for P256Affine {
    fn from(proj: &P256) -> Self {
        proj.to_affine()
    }
}

#[cfg(test)]
mod tests {
    use group::{Curve, Group};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    const TEST_ITERATIONS: usize = 100;

    fn seeded_rng() -> XorShiftRng {
        XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ])
    }

    #[test]
    fn test_affine_coordinates() {
        let mut rng = seeded_rng();

        for _ in 0..TEST_ITERATIONS {
            let point = P256::random(&mut rng);
            let affine = point.to_affine();

            // Skip identity point since it will panic when we try to get coordinates.
            if bool::from(affine.0.is_identity()) {
                continue;
            }

            let x = affine.try_x().unwrap();
            let y = affine.try_y().unwrap();

            // Reconstruct point from coordinates.
            let reconstructed = P256Affine::from_xy(x, y);
            assert_eq!(reconstructed.expect("Valid affine point"), affine);
        }
    }

    #[test]
    fn test_batch_normalize() {
        let mut rng = seeded_rng();

        for _ in 0..50 {
            let points: Vec<P256> = (0..10).map(|_| P256::random(&mut rng)).collect();
            let mut affine_points = vec![P256Affine::identity(); points.len()];

            // Convert each point to affine individually
            for (i, point) in points.iter().enumerate() {
                affine_points[i] = point.to_affine();
            }

            for (proj, affine) in points.iter().zip(affine_points.iter()) {
                assert_eq!(proj.to_affine(), *affine);
            }
        }
    }

    #[test]
    fn test_identity_coordinates_are_none() {
        let identity = P256Affine::identity();
        assert!(identity.try_x().is_none());
        assert!(identity.try_y().is_none());
    }

    #[test]
    fn test_malformed_compressed_encoding_rejected() {
        // 0x01 is not a valid SEC1 tag.
        let bytes = CompressedPoint::from([
            0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ]);

        assert!(!bool::from(P256::from_bytes(&bytes).is_some()));
        assert!(!bool::from(P256Affine::from_bytes(&bytes).is_some()));
    }
}

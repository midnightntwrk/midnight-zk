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

//! Secp256k1 curve types using k256.

use ff::Field as FfField;
use group::{Curve, Group, GroupEncoding};
use k256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use k256::{AffinePoint, ProjectivePoint};
use subtle::{Choice, CtOption};

use k256::elliptic_curve::group::GroupEncoding as K256GroupEncoding;
use k256::elliptic_curve::point::AffineCoordinates;
use k256::elliptic_curve::BatchNormalize;
use k256::elliptic_curve::Group as K256Group;

use super::{Fp, Fq};
use k256::elliptic_curve::ff::PrimeField as K256PrimeField;

/// secp256k1 curve point in projective coordinates.
// NOTE: Necessary to implement group::Curve, which is necessary to implement
// CircuitCurve. This wrapper may be removed when CircuitCurve no longer needs
// group::Curve.
#[derive(Clone, Copy, Debug, Default)]
pub struct K256(pub ProjectivePoint);

/// secp256k1 curve point in affine coordinates.
#[derive(Clone, Copy, Debug)]
pub struct K256Affine(pub AffinePoint);

impl K256 {
    /// Returns the identity point.
    pub fn identity() -> Self {
        Self(ProjectivePoint::IDENTITY)
    }

    /// Returns the generator point.
    pub fn generator() -> Self {
        Self(ProjectivePoint::GENERATOR)
    }

    /// Returns the cubic root of unity in the base field for GLV endomorphism.
    /// ZETA^3 = 1 mod p, ZETA != 1.
    pub fn base_zeta() -> Fp {
        // 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
        const ZETA_BYTES: [u8; 32] = [
            0x7a, 0xe9, 0x6a, 0x2b, 0x65, 0x7c, 0x07, 0x10, 0x6e, 0x64, 0x47, 0x9e, 0xac, 0x34,
            0x34, 0xe9, 0x9c, 0xf0, 0x49, 0x75, 0x12, 0xf5, 0x89, 0x95, 0xc1, 0x39, 0x6c, 0x28,
            0x71, 0x95, 0x01, 0xee,
        ];
        Fp::from_bytes(&k256::FieldBytes::from(ZETA_BYTES)).expect("Valid ZETA bytes")
    }

    /// Returns the cubic root of unity in the scalar field for GLV endomorphism.
    /// ZETA^3 = 1 mod n, ZETA != 1.
    pub fn scalar_zeta() -> Fq {
        // 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
        const ZETA_BYTES: [u8; 32] = [
            0x53, 0x63, 0xad, 0x4c, 0xc0, 0x5c, 0x30, 0xe0, 0xa5, 0x26, 0x1c, 0x02, 0x88, 0x12,
            0x64, 0x5a, 0x12, 0x2e, 0x22, 0xea, 0x20, 0x81, 0x66, 0x78, 0xdf, 0x02, 0x96, 0x7c,
            0x1b, 0x23, 0xbd, 0x72,
        ];
        <Fq as K256PrimeField>::from_repr(k256::FieldBytes::from(ZETA_BYTES))
            .expect("Valid ZETA bytes")
    }
}

impl K256Affine {
    /// Returns the identity point.
    pub fn identity() -> Self {
        Self(AffinePoint::IDENTITY)
    }

    /// Returns the generator point.
    pub fn generator() -> Self {
        Self(AffinePoint::GENERATOR)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp {
        Fp::from_bytes(&self.0.x()).expect("Valid coordinate")
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp {
        // Use uncompressed encoding to get y coordinate.
        let encoded = self.0.to_encoded_point(false);
        let y_bytes = encoded.y().expect("Uncompressed point has y coordinate");
        Fp::from_bytes(y_bytes).expect("Valid coordinate")
    }

    /// Creates an affine point from x and y coordinates.
    pub fn from_xy(x: Fp, y: Fp) -> Option<Self> {
        // Use uncompressed SEC1 encoding to avoid sqrt during decompression.
        // EncodedPoint::from_affine_coordinates takes big-endian x and y bytes.
        let encoded = k256::EncodedPoint::from_affine_coordinates(
            &x.to_bytes(),
            &y.to_bytes(),
            false, // Don't compress - we have both coordinates.
        );

        // from_encoded_point validates the point is on the curve.
        AffinePoint::from_encoded_point(&encoded).into_option().map(Self)
    }
}

impl Default for K256Affine {
    fn default() -> Self {
        Self::identity()
    }
}

// ============================================================================
// Group and Curve trait implementations
// ============================================================================

impl Group for K256 {
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
        <ProjectivePoint as K256Group>::is_identity(&self.0)
    }

    fn double(&self) -> Self {
        Self(self.0.double())
    }
}

impl Curve for K256 {
    type AffineRepr = K256Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        K256Affine(self.0.to_affine())
    }

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        assert_eq!(p.len(), q.len());
        let inner: Vec<ProjectivePoint> = p.iter().map(|pt| pt.0).collect();

        let affine_points: Vec<AffinePoint> =
            <ProjectivePoint as BatchNormalize<[ProjectivePoint]>>::batch_normalize(&inner);

        for (dst, src) in q.iter_mut().zip(affine_points.into_iter()) {
            *dst = K256Affine(src);
        }
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

impl GroupEncoding for K256 {
    type Repr = CompressedPoint;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let compressed = k256::CompressedPoint::from(bytes.0);
        <ProjectivePoint as K256GroupEncoding>::from_bytes(&compressed).map(Self)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        let bytes: [u8; 33] = <ProjectivePoint as K256GroupEncoding>::to_bytes(&self.0).into();
        CompressedPoint(bytes)
    }
}

impl GroupEncoding for K256Affine {
    type Repr = CompressedPoint;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let compressed = k256::CompressedPoint::from(bytes.0);
        <AffinePoint as K256GroupEncoding>::from_bytes(&compressed).map(Self)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        let bytes: [u8; 33] = <AffinePoint as K256GroupEncoding>::to_bytes(&self.0).into();
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

impl PartialEq for K256 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for K256 {}

impl PartialEq for K256Affine {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for K256Affine {}

impl ConstantTimeEq for K256 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConstantTimeEq for K256Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for K256 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(ProjectivePoint::conditional_select(&a.0, &b.0, choice))
    }
}

impl ConditionallySelectable for K256Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(AffinePoint::conditional_select(&a.0, &b.0, choice))
    }
}

// Arithmetic operations for K256.
impl Add for K256 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<&K256> for K256 {
    type Output = Self;
    fn add(self, rhs: &K256) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<K256Affine> for K256 {
    type Output = Self;
    fn add(self, rhs: K256Affine) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Add<&K256Affine> for K256 {
    type Output = Self;
    fn add(self, rhs: &K256Affine) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl AddAssign for K256 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl AddAssign<&K256> for K256 {
    fn add_assign(&mut self, rhs: &K256) {
        self.0 += rhs.0;
    }
}

impl AddAssign<K256Affine> for K256 {
    fn add_assign(&mut self, rhs: K256Affine) {
        self.0 += rhs.0;
    }
}

impl AddAssign<&K256Affine> for K256 {
    fn add_assign(&mut self, rhs: &K256Affine) {
        self.0 += rhs.0;
    }
}

impl Sub for K256 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<&K256> for K256 {
    type Output = Self;
    fn sub(self, rhs: &K256) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<K256Affine> for K256 {
    type Output = Self;
    fn sub(self, rhs: K256Affine) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Sub<&K256Affine> for K256 {
    type Output = Self;
    fn sub(self, rhs: &K256Affine) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for K256 {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<&K256> for K256 {
    fn sub_assign(&mut self, rhs: &K256) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<K256Affine> for K256 {
    fn sub_assign(&mut self, rhs: K256Affine) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<&K256Affine> for K256 {
    fn sub_assign(&mut self, rhs: &K256Affine) {
        self.0 -= rhs.0;
    }
}

impl Neg for K256 {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Neg for &K256 {
    type Output = K256;
    fn neg(self) -> K256 {
        K256(-self.0)
    }
}

// Scalar multiplication.
impl Mul<Fq> for K256 {
    type Output = Self;
    fn mul(self, rhs: Fq) -> Self {
        Self(self.0 * rhs)
    }
}

impl Mul<&Fq> for K256 {
    type Output = Self;
    fn mul(self, rhs: &Fq) -> Self {
        Self(self.0 * rhs)
    }
}

impl Mul<K256> for Fq {
    type Output = K256;
    fn mul(self, rhs: K256) -> K256 {
        K256(rhs.0 * self)
    }
}

impl Mul<&K256> for Fq {
    type Output = K256;
    fn mul(self, rhs: &K256) -> K256 {
        K256(rhs.0 * self)
    }
}

impl MulAssign<Fq> for K256 {
    fn mul_assign(&mut self, rhs: Fq) {
        self.0 *= rhs;
    }
}

impl MulAssign<&Fq> for K256 {
    fn mul_assign(&mut self, rhs: &Fq) {
        self.0 *= rhs;
    }
}

// Sum trait.
impl Sum for K256 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(K256::identity(), |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a K256> for K256 {
    fn sum<I: Iterator<Item = &'a K256>>(iter: I) -> Self {
        iter.fold(K256::identity(), |acc, x| acc + x)
    }
}

// Conversions between K256 and K256Affine.
impl From<K256Affine> for K256 {
    fn from(affine: K256Affine) -> Self {
        Self(affine.0.into())
    }
}

impl From<&K256Affine> for K256 {
    fn from(affine: &K256Affine) -> Self {
        Self(affine.0.into())
    }
}

impl From<K256> for K256Affine {
    fn from(proj: K256) -> Self {
        proj.to_affine()
    }
}

impl From<&K256> for K256Affine {
    fn from(proj: &K256) -> Self {
        proj.to_affine()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use group::{Curve, Group};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

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
            let point = K256::random(&mut rng);
            let affine = point.to_affine();
            let x = affine.x();
            let y = affine.y();

            // Reconstruct point from coordinates.
            let reconstructed = K256Affine::from_xy(x, y);
            assert_eq!(reconstructed.expect("Valid affine point"), affine);
        }
    }

    #[test]
    fn test_batch_normalize() {
        let mut rng = seeded_rng();

        for _ in 0..50 {
            let points: Vec<K256> = (0..10).map(|_| K256::random(&mut rng)).collect();
            let mut affine_points = vec![K256Affine::identity(); points.len()];

            K256::batch_normalize(&points, &mut affine_points);

            for (proj, affine) in points.iter().zip(affine_points.iter()) {
                assert_eq!(proj.to_affine(), *affine);
            }
        }
    }

    #[test]
    fn test_base_zeta_cubed_is_one() {
        let zeta = K256::base_zeta();
        let zeta_squared = zeta * zeta;
        let zeta_cubed = zeta_squared * zeta;

        // k256's FieldElement requires normalization after arithmetic
        // for canonical comparison.
        assert_eq!(zeta_cubed.normalize(), Fp::ONE);
        assert_ne!(zeta_squared.normalize(), Fp::ONE);
    }

    #[test]
    fn test_scalar_zeta_cubed_is_one() {
        let zeta = K256::scalar_zeta();
        let zeta_squared = zeta * zeta;
        let zeta_cubed = zeta_squared * zeta;

        assert_eq!(zeta_cubed, Fq::ONE);
        assert_ne!(zeta_squared, Fq::ONE);
    }
}

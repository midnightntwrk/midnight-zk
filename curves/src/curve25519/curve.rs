//! Curve25519 circuit integration.
//!
//! This module provides a wrapper around curve25519_dalek's EdwardsPoint
//! to implement the traits required for circuit usage.
//! Currently, this is necessary because group::Curve is a requirement for CircuitCurve
//! and this trait cannot be implemented for the foreign EdwardsPoint.

use super::Scalar;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use curve25519_dalek::{edwards::CompressedEdwardsY, EdwardsPoint};
use group::{Curve as GroupCurve, Group, GroupEncoding};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

/// EdwardsPoint wrapper for circuit integration.
#[derive(Copy, Clone, Debug)]
pub struct Curve25519(pub EdwardsPoint);

impl PartialEq for Curve25519 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Curve25519 {}

impl ConstantTimeEq for Curve25519 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for Curve25519 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Curve25519(EdwardsPoint::conditional_select(&a.0, &b.0, choice))
    }
}

impl Default for Curve25519 {
    fn default() -> Self {
        Curve25519(EdwardsPoint::default())
    }
}

// Arithmetic operations
impl Add for Curve25519 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Curve25519(self.0 + rhs.0)
    }
}

impl<'a> Add<&'a Curve25519> for Curve25519 {
    type Output = Self;
    fn add(self, rhs: &'a Curve25519) -> Self {
        Curve25519(self.0 + rhs.0)
    }
}

impl<'a> Add<Curve25519> for &'a Curve25519 {
    type Output = Curve25519;
    fn add(self, rhs: Curve25519) -> Curve25519 {
        Curve25519(self.0 + rhs.0)
    }
}

impl<'a, 'b> Add<&'a Curve25519> for &'b Curve25519 {
    type Output = Curve25519;
    fn add(self, rhs: &'a Curve25519) -> Curve25519 {
        Curve25519(self.0 + rhs.0)
    }
}

impl Sub for Curve25519 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Curve25519(self.0 - rhs.0)
    }
}

impl<'a> Sub<&'a Curve25519> for Curve25519 {
    type Output = Self;
    fn sub(self, rhs: &'a Curve25519) -> Self {
        Curve25519(self.0 - rhs.0)
    }
}

impl Neg for Curve25519 {
    type Output = Self;
    fn neg(self) -> Self {
        Curve25519(-self.0)
    }
}

impl<'a> Neg for &'a Curve25519 {
    type Output = Curve25519;
    fn neg(self) -> Curve25519 {
        Curve25519(-self.0)
    }
}

impl Mul<Scalar> for Curve25519 {
    type Output = Self;
    fn mul(self, rhs: Scalar) -> Self {
        Curve25519(self.0 * rhs)
    }
}

impl<'a> Mul<&'a Scalar> for Curve25519 {
    type Output = Self;
    fn mul(self, rhs: &'a Scalar) -> Self {
        Curve25519(self.0 * rhs)
    }
}

impl Mul<Curve25519> for Scalar {
    type Output = Curve25519;
    fn mul(self, rhs: Curve25519) -> Curve25519 {
        Curve25519(self * rhs.0)
    }
}

impl<'a> Mul<&'a Curve25519> for Scalar {
    type Output = Curve25519;
    fn mul(self, rhs: &'a Curve25519) -> Curve25519 {
        Curve25519(self * rhs.0)
    }
}

// Assignment operations
impl AddAssign for Curve25519 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl<'a> AddAssign<&'a Curve25519> for Curve25519 {
    fn add_assign(&mut self, rhs: &'a Curve25519) {
        self.0 += rhs.0;
    }
}

impl SubAssign for Curve25519 {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl<'a> SubAssign<&'a Curve25519> for Curve25519 {
    fn sub_assign(&mut self, rhs: &'a Curve25519) {
        self.0 -= rhs.0;
    }
}

impl MulAssign<Scalar> for Curve25519 {
    fn mul_assign(&mut self, rhs: Scalar) {
        self.0 *= rhs;
    }
}

impl<'a> MulAssign<&'a Scalar> for Curve25519 {
    fn mul_assign(&mut self, rhs: &'a Scalar) {
        self.0 *= rhs;
    }
}

// Sum trait for iterator operations
impl Sum for Curve25519 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Curve25519::identity(), |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a Curve25519> for Curve25519 {
    fn sum<I: Iterator<Item = &'a Curve25519>>(iter: I) -> Self {
        iter.fold(Curve25519::identity(), |acc, x| acc + x)
    }
}

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
        // Convert to affine by compressing and decompressing
        // This is not the most efficient but works for circuit use
        let compressed = self.0.compress();
        Curve25519Affine(compressed)
    }

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        assert_eq!(p.len(), q.len());
        // Simple implementation - just convert each point
        for (proj, affine) in p.iter().zip(q.iter_mut()) {
            *affine = proj.to_affine();
        }
    }
}

// Implement GroupEncoding
impl GroupEncoding for Curve25519 {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> subtle::CtOption<Self> {
        let compressed = CompressedEdwardsY(*bytes);
        match compressed.decompress() {
            Some(point) => subtle::CtOption::new(Curve25519(point), Choice::from(1u8)),
            None => subtle::CtOption::new(Curve25519(EdwardsPoint::identity()), Choice::from(0u8)),
        }
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> subtle::CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.compress().to_bytes()
    }
}

/// Affine representation (compressed form)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Curve25519Affine(pub CompressedEdwardsY);

impl From<Curve25519> for Curve25519Affine {
    fn from(point: Curve25519) -> Self {
        point.to_affine()
    }
}

impl From<Curve25519Affine> for Curve25519 {
    fn from(affine: Curve25519Affine) -> Self {
        Curve25519(affine.0.decompress().expect("valid affine point"))
    }
}

impl GroupEncoding for Curve25519Affine {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> subtle::CtOption<Self> {
        let compressed = CompressedEdwardsY(*bytes);
        // Check if it's valid by trying to decompress
        match compressed.decompress() {
            Some(_) => subtle::CtOption::new(Curve25519Affine(compressed), Choice::from(1u8)),
            None => subtle::CtOption::new(
                Curve25519Affine(CompressedEdwardsY([0u8; 32])),
                Choice::from(0u8),
            ),
        }
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> subtle::CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.to_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use group::Group;

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
}

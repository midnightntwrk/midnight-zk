//! An implementation of the $\mathbb{G}_1$ group of BLS12-381.
#![allow(unused_variables)]

use core::{
    borrow::Borrow,
    fmt,
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::{convert::TryInto, io::Read};

use blst::*;
use ff::Field;
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding, WnafGroup,
};
use halo2curves::{serde::SerdeObject, Coordinates, CurveAffine, CurveExt};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{
    fp::{Fp, ZETA_BASE},
    Bls12, Engine, Fq, G2Affine, Gt, PairingCurveAffine,
};

/// This is an element of $\mathbb{G}_1$ represented in the affine coordinate
/// space. It is ideal to keep elements in this representation to reduce memory
/// usage and improve performance through the use of mixed curve model
/// arithmetic.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G1Affine(pub(crate) blst_p1_affine);

const COMPRESSED_SIZE: usize = 48;
const UNCOMPRESSED_SIZE: usize = 96;

pub const A: Fp = Fp::ZERO;
pub const B: Fp = Fp(blst_fp {
    // 0x04 in Montgomery form.
    l: [
        0xaa270000000cfff3,
        0x53cc0032fc34000a,
        0x478fe97a6b0a807f,
        0xb1d37ebee6ba24d7,
        0x8ec9733bbf78ab2f,
        0x09d645513d83de7e,
    ],
});

impl fmt::Debug for G1Affine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let is_ident: bool = self.is_identity().into();
        f.debug_struct("G1Affine")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("infinity", &is_ident)
            .finish()
    }
}

impl fmt::Display for G1Affine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_identity().into() {
            write!(f, "G1Affine(Infinity)")
        } else {
            write!(f, "G1Affine(x={}, y={})", self.x(), self.y())
        }
    }
}

impl core::hash::Hash for G1Affine {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.x.l.hash::<H>(state);
        self.0.y.l.hash::<H>(state)
    }
}

impl Default for G1Affine {
    fn default() -> G1Affine {
        G1Affine::identity()
    }
}

impl From<&G1Projective> for G1Affine {
    fn from(p: &G1Projective) -> G1Affine {
        let mut out = blst_p1_affine::default();

        unsafe { blst_p1_to_affine(&mut out, &p.0) };

        G1Affine(out)
    }
}

impl From<G1Projective> for G1Affine {
    fn from(p: G1Projective) -> G1Affine {
        G1Affine::from(&p)
    }
}

impl AsRef<blst_p1_affine> for G1Affine {
    fn as_ref(&self) -> &blst_p1_affine {
        &self.0
    }
}

impl AsMut<blst_p1_affine> for G1Affine {
    fn as_mut(&mut self) -> &mut blst_p1_affine {
        &mut self.0
    }
}

impl Eq for G1Affine {}
impl PartialEq for G1Affine {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        unsafe { blst_p1_affine_is_equal(&self.0, &other.0) }
    }
}

impl Neg for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn neg(self) -> G1Projective {
        -*self
    }
}

impl Neg for G1Projective {
    type Output = G1Projective;

    #[inline]
    fn neg(mut self) -> G1Projective {
        unsafe { blst_p1_cneg(&mut self.0, true) };
        self
    }
}

impl Neg for &G1Affine {
    type Output = G1Affine;

    #[inline]
    fn neg(self) -> G1Affine {
        -*self
    }
}

impl Neg for G1Affine {
    type Output = G1Affine;

    #[inline]
    fn neg(mut self) -> G1Affine {
        // Missing for affine in blst
        if (!self.is_identity()).into() {
            unsafe {
                blst_fp_cneg(&mut self.0.y, &self.0.y, true);
            }
        }
        self
    }
}

impl Add<&G1Projective> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn add(self, rhs: &G1Projective) -> G1Projective {
        let mut out = blst_p1::default();
        unsafe { blst_p1_add_or_double(&mut out, &self.0, &rhs.0) };
        G1Projective(out)
    }
}

impl Add<&G1Projective> for &G1Affine {
    type Output = G1Projective;

    #[inline]
    fn add(self, rhs: &G1Projective) -> G1Projective {
        rhs.add_mixed(self)
    }
}

impl Add<&G1Affine> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn add(self, rhs: &G1Affine) -> G1Projective {
        self.add_mixed(rhs)
    }
}

impl Sub<&G1Projective> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn sub(self, rhs: &G1Projective) -> G1Projective {
        self + (-rhs)
    }
}

impl Sub<&G1Projective> for &G1Affine {
    type Output = G1Projective;

    #[inline]
    fn sub(self, rhs: &G1Projective) -> G1Projective {
        self + (-rhs)
    }
}

impl Sub<&G1Affine> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn sub(self, rhs: &G1Affine) -> G1Projective {
        self + (-rhs)
    }
}

impl AddAssign<&G1Projective> for G1Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G1Projective) {
        unsafe { blst_p1_add_or_double(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&G1Projective> for G1Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G1Projective) {
        *self += &-rhs;
    }
}

impl AddAssign<&G1Affine> for G1Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G1Affine) {
        unsafe { blst_p1_add_or_double_affine(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&G1Affine> for G1Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G1Affine) {
        *self += &-rhs;
    }
}

impl Mul<&Fq> for &G1Projective {
    type Output = G1Projective;

    fn mul(self, scalar: &Fq) -> Self::Output {
        self.multiply(scalar)
    }
}

impl Mul<&Fq> for &G1Affine {
    type Output = G1Projective;

    fn mul(self, scalar: &Fq) -> Self::Output {
        G1Projective::from(self).multiply(scalar)
    }
}

impl MulAssign<&Fq> for G1Projective {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fq) {
        *self = *self * rhs;
    }
}

impl MulAssign<&Fq> for G1Affine {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fq) {
        *self = (*self * rhs).into();
    }
}

impl_add_sub!(G1Projective);
impl_add_sub!(G1Projective, G1Affine);
impl_add_sub!(G1Affine, G1Projective, G1Projective);

impl_add_sub_assign!(G1Projective);
impl_add_sub_assign!(G1Projective, G1Affine);

impl_mul!(G1Projective, Fq);
impl_mul!(G1Affine, Fq, G1Projective);

impl_mul_assign!(G1Projective, Fq);
impl_mul_assign!(G1Affine, Fq);

impl<T> Sum<T> for G1Projective
where
    T: Borrow<G1Projective>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl ConditionallySelectable for G1Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Affine(blst_p1_affine {
            x: Fp::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp::conditional_select(&a.y(), &b.y(), choice).0,
        })
    }
}

impl ConditionallySelectable for G1Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Projective(blst_p1 {
            x: Fp::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp::conditional_select(&a.y(), &b.y(), choice).0,
            z: Fp::conditional_select(&a.z(), &b.z(), choice).0,
        })
    }
}

// Internal serializations methods.
impl G1Affine {
    /// Serializes this element into compressed form.
    fn to_compressed(&self) -> [u8; COMPRESSED_SIZE] {
        let mut out = [0u8; COMPRESSED_SIZE];

        unsafe {
            blst_p1_affine_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Serializes this element into uncompressed form.
    fn to_uncompressed(&self) -> [u8; UNCOMPRESSED_SIZE] {
        let mut out = [0u8; UNCOMPRESSED_SIZE];
        unsafe {
            blst_p1_affine_serialize(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize an uncompressed element.
    fn from_uncompressed(bytes: &[u8; UNCOMPRESSED_SIZE]) -> CtOption<Self> {
        G1Affine::from_uncompressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_on_curve() & p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is on the curve and not checking if it is in the correct
    /// subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading;
    /// otherwise, API invariants may be broken.** Please consider using
    /// `from_uncompressed()` instead.
    fn from_uncompressed_unchecked(bytes: &[u8; UNCOMPRESSED_SIZE]) -> CtOption<Self> {
        let mut raw = blst_p1_affine::default();
        let success =
            unsafe { blst_p1_deserialize(&mut raw, bytes.as_ptr()) == BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G1Affine(raw), Choice::from(success as u8))
    }

    /// Attempts to deserialize a compressed element.
    fn from_compressed(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        G1Affine::from_compressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_on_curve() & p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading;
    /// otherwise, API invariants may be broken.** Please consider using
    /// `from_compressed()` instead.
    fn from_compressed_unchecked(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        let mut raw = blst_p1_affine::default();
        let success =
            unsafe { blst_p1_uncompress(&mut raw, bytes.as_ptr()) == BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G1Affine(raw), Choice::from(success as u8))
    }

    pub const fn uncompressed_size() -> usize {
        UNCOMPRESSED_SIZE
    }

    pub const fn compressed_size() -> usize {
        COMPRESSED_SIZE
    }
}

impl G1Affine {
    /// Returns true if this point is free of an $h$-torsion component, and so
    /// it exists within the $q$-order subgroup $\mathbb{G}_1$. This should
    /// always return true unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        unsafe { Choice::from(blst_p1_affine_in_g1(&self.0) as u8) }
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp {
        Fp(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp {
        Fp(self.0.y)
    }

    // Internal wrapper for `blst_p1_affine`.
    fn from_raw_unchecked(x: Fp, y: Fp, _infinity: bool) -> Self {
        // FIXME: what about infinity?
        let raw = blst_p1_affine { x: x.0, y: y.0 };
        G1Affine(raw)
    }
}

impl SerdeObject for G1Affine {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), UNCOMPRESSED_SIZE);
        let input: [u8; UNCOMPRESSED_SIZE] = bytes.try_into().unwrap();
        Self::from_uncompressed_unchecked(&input).unwrap()
    }

    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        debug_assert_eq!(bytes.len(), UNCOMPRESSED_SIZE);
        let input: [u8; UNCOMPRESSED_SIZE] = bytes.try_into().unwrap();
        Self::from_uncompressed(&input).into()
    }

    fn to_raw_bytes(&self) -> Vec<u8> {
        self.to_uncompressed().into()
    }

    fn read_raw_unchecked<R: Read>(reader: &mut R) -> Self {
        let mut buf = [0u8; UNCOMPRESSED_SIZE];
        reader
            .read_exact(&mut buf)
            .expect("Could not read from buffer.");
        Self::from_uncompressed_unchecked(&buf)
            .expect("from_uncompressed_unchecked should return a point.")
    }

    fn read_raw<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut buf = [0u8; UNCOMPRESSED_SIZE];
        reader.read_exact(&mut buf)?;
        let res = Self::from_uncompressed(&buf);
        if res.is_some().into() {
            Ok(res.unwrap())
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid point. (Either not on curve, or not in subgroup.",
            ))
        }
    }

    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.to_uncompressed())
    }
}

/// This is an element of $\mathbb{G}_1$ represented in the projective
/// coordinate space.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G1Projective(pub(crate) blst_p1);

impl fmt::Debug for G1Projective {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("G1Projective")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("z", &self.z())
            .finish()
    }
}

impl fmt::Display for G1Projective {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", G1Affine::from(self))
    }
}

impl AsRef<blst_p1> for G1Projective {
    fn as_ref(&self) -> &blst_p1 {
        &self.0
    }
}

impl AsMut<blst_p1> for G1Projective {
    fn as_mut(&mut self) -> &mut blst_p1 {
        &mut self.0
    }
}

impl From<&G1Affine> for G1Projective {
    fn from(p: &G1Affine) -> G1Projective {
        let mut out = blst_p1::default();

        unsafe { blst_p1_from_affine(&mut out, &p.0) };

        G1Projective(out)
    }
}

impl From<G1Affine> for G1Projective {
    fn from(p: G1Affine) -> G1Projective {
        G1Projective::from(&p)
    }
}

impl Eq for G1Projective {}
impl PartialEq for G1Projective {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let self_is_zero: bool = self.is_identity().into();
        let other_is_zero: bool = other.is_identity().into();
        (self_is_zero && other_is_zero)
            || (!self_is_zero && !other_is_zero && unsafe { blst_p1_is_equal(&self.0, &other.0) })
    }
}

// Internal serializations methods.
impl G1Projective {
    /// Serializes this element into compressed form.
    fn to_compressed(&self) -> [u8; COMPRESSED_SIZE] {
        let mut out = [0u8; COMPRESSED_SIZE];

        unsafe {
            blst_p1_compress(out.as_mut_ptr(), &self.0);
        }
        out
    }

    /// Attempts to deserialize a compressed element.
    fn from_compressed(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        G1Affine::from_compressed(bytes).map(Into::into)
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading;
    /// otherwise, API invariants may be broken.** Please consider using
    /// `from_compressed()` instead.
    fn from_compressed_unchecked(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        G1Affine::from_compressed_unchecked(bytes).map(Into::into)
    }
}

impl G1Projective {
    /// Adds this point to another point in the affine model.
    fn add_mixed(&self, rhs: &G1Affine) -> G1Projective {
        let mut out = blst_p1::default();

        unsafe { blst_p1_add_or_double_affine(&mut out, &self.0, &rhs.0) };

        G1Projective(out)
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> Choice {
        let is_on_curve = unsafe { Choice::from(blst_p1_on_curve(&self.0) as u8) };
        is_on_curve | self.is_identity()
    }

    fn multiply(&self, scalar: &Fq) -> G1Projective {
        let mut out = blst_p1::default();

        // Scalar is 255 bits wide.
        const NBITS: usize = 255;

        unsafe { blst_p1_mult(&mut out, &self.0, scalar.to_bytes_le().as_ptr(), NBITS) };

        G1Projective(out)
    }

    fn from_raw_unchecked(x: Fp, y: Fp, z: Fp) -> Self {
        let raw = blst_p1 {
            x: x.0,
            y: y.0,
            z: z.0,
        };

        G1Projective(raw)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp {
        Fp(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp {
        Fp(self.0.y)
    }

    /// Returns the z coordinate.
    pub fn z(&self) -> Fp {
        Fp(self.0.z)
    }

    /// Hash to curve algorithm.
    pub fn hash_to_curve(msg: &[u8], dst: &[u8], aug: &[u8]) -> Self {
        let mut res = Self::identity();
        unsafe {
            blst_hash_to_g1(
                &mut res.0,
                msg.as_ptr(),
                msg.len(),
                dst.as_ptr(),
                dst.len(),
                aug.as_ptr(),
                aug.len(),
            );
        }
        res
    }

    /// Perform a multi-exponentiation, aka "multi-scalar-multiplication" (MSM)
    /// using `blst`'s implementation of Pippenger's algorithm.
    /// Note: `scalars` is cloned in this method.
    pub fn multi_exp(points: &[Self], scalars: &[Fq]) -> Self {
        let n = if points.len() < scalars.len() {
            points.len()
        } else {
            scalars.len()
        };
        let points =
            unsafe { std::slice::from_raw_parts(points.as_ptr() as *const blst_p1, points.len()) };

        let points = p1_affines::from(points);

        let mut scalar_bytes: Vec<u8> = Vec::with_capacity(n * 32);
        for a in scalars.iter().map(|s| s.to_bytes_le()) {
            scalar_bytes.extend_from_slice(&a);
        }

        let res = points.mult(scalar_bytes.as_slice(), 255);

        G1Projective(res)
    }
}

impl Group for G1Projective {
    type Scalar = Fq;

    fn random(mut rng: impl RngCore) -> Self {
        let mut out = blst_p1::default();
        let mut msg = [0u8; 64];
        rng.fill_bytes(&mut msg);
        const DST: [u8; 16] = [0; 16];
        const AUG: [u8; 16] = [0; 16];

        unsafe {
            blst_encode_to_g1(
                &mut out,
                msg.as_ptr(),
                msg.len(),
                DST.as_ptr(),
                DST.len(),
                AUG.as_ptr(),
                AUG.len(),
            )
        };

        G1Projective(out)
    }

    fn identity() -> Self {
        G1Projective(blst_p1::default())
    }

    fn generator() -> Self {
        G1Projective(unsafe { *blst_p1_generator() })
    }

    fn is_identity(&self) -> Choice {
        unsafe { Choice::from(blst_p1_is_inf(&self.0) as u8) }
    }

    fn double(&self) -> Self {
        let mut double = blst_p1::default();
        unsafe { blst_p1_double(&mut double, &self.0) };
        G1Projective(double)
    }
}

impl WnafGroup for G1Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl PrimeGroup for G1Projective {}

impl Curve for G1Projective {
    type AffineRepr = G1Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G1Projective {
    type Affine = G1Affine;
}

impl PrimeCurveAffine for G1Affine {
    type Scalar = Fq;
    type Curve = G1Projective;

    fn identity() -> Self {
        G1Affine(blst_p1_affine::default())
    }

    fn generator() -> Self {
        G1Affine(unsafe { *blst_p1_affine_generator() })
    }

    fn is_identity(&self) -> Choice {
        unsafe { Choice::from(blst_p1_affine_is_inf(&self.0) as u8) }
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl GroupEncoding for G1Projective {
    type Repr = G1Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G1Compressed(self.to_compressed())
    }
}

impl GroupEncoding for G1Affine {
    type Repr = G1Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G1Compressed(self.to_compressed())
    }
}

impl UncompressedEncoding for G1Affine {
    type Uncompressed = G1Uncompressed;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed(&bytes.0)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed_unchecked(&bytes.0)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G1Uncompressed(self.to_uncompressed())
    }
}

// UncompressedEncoding is not implemented for projective coordinates
// impl UncompressedEncoding for G1Projective{}

#[derive(Copy, Clone)]
#[repr(transparent)]
// Wrapper for [u8; UNCOMPRESSED_SIZE].
// This is needed to satisfy the [`Default`] bound on the Uncompressed type
// for [`UncompressedEncoding`].
pub struct G1Uncompressed([u8; UNCOMPRESSED_SIZE]);

encoded_point_delegations!(G1Uncompressed);

impl Default for G1Uncompressed {
    fn default() -> Self {
        G1Uncompressed([0u8; UNCOMPRESSED_SIZE])
    }
}

impl fmt::Debug for G1Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G1Compressed([u8; COMPRESSED_SIZE]);

encoded_point_delegations!(G1Compressed);

impl Default for G1Compressed {
    fn default() -> Self {
        G1Compressed([0u8; COMPRESSED_SIZE])
    }
}

impl fmt::Debug for G1Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl PairingCurveAffine for G1Affine {
    type Pair = G2Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        <Bls12 as Engine>::pairing(self, other)
    }
}

impl Add for G1Affine {
    type Output = <Self as PrimeCurveAffine>::Curve;

    fn add(self, rhs: Self) -> Self::Output {
        G1Projective::from(self) + rhs
    }
}

impl Sub for G1Affine {
    type Output = <Self as PrimeCurveAffine>::Curve;

    fn sub(self, rhs: Self) -> Self::Output {
        G1Projective::from(self) - rhs
    }
}

impl ConstantTimeEq for G1Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        let z1 = self.is_identity();
        let z2 = other.is_identity();

        (z1 & z2) | ((!z1) & (!z2) & (self.x().ct_eq(&other.x())) & (self.y().ct_eq(&other.y())))
    }
}

impl Default for G1Projective {
    fn default() -> Self {
        G1Projective::identity()
    }
}

impl ConstantTimeEq for G1Projective {
    fn ct_eq(&self, other: &Self) -> Choice {
        // Is (x, y, z) equal to (x', y, z') when converted to affine?
        // => (x/z , y/z) equal to (x'/z' , y'/z')
        // => (xz' == x'z) & (yz' == y'z)

        let x1 = self.x() * other.z();
        let y1 = self.y() * other.z();

        let x2 = other.x() * self.z();
        let y2 = other.y() * self.z();

        let self_is_zero = self.is_identity();
        let other_is_zero = other.is_identity();

        (self_is_zero & other_is_zero) // Both point at infinity
            | ((!self_is_zero) & (!other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
        // Neither point at infinity, coordinates are the same
    }
}

impl CurveExt for G1Projective {
    type ScalarExt = Fq;
    type Base = Fp;
    type AffineExt = G1Affine;
    const CURVE_ID: &'static str = "";

    fn endo(&self) -> Self {
        G1Projective::from_raw_unchecked(self.x() * ZETA_BASE, self.y(), self.z())
    }

    fn jacobian_coordinates(&self) -> (Self::Base, Self::Base, Self::Base) {
        // Homogeneous to Jacobian
        let x = self.x() * self.z();
        let y = self.y() * self.z().square();
        (x, y, self.z())
    }

    fn hash_to_curve<'a>(domain_prefix: &'a str) -> Box<dyn Fn(&[u8]) -> Self + 'a> {
        Box::new(move |message| {
            Self::hash_to_curve(
                message,
                domain_prefix.as_ref(),
                b"BLS12381G1_XMD:SHA-256_SSWU_RO_",
            )
        })
    }

    fn is_on_curve(&self) -> Choice {
        self.is_on_curve()
    }

    fn a() -> Self::Base {
        A
    }

    fn b() -> Self::Base {
        B
    }

    fn new_jacobian(x: Self::Base, y: Self::Base, z: Self::Base) -> CtOption<Self> {
        // Jacobian to homogeneous
        let z_inv = z.invert().unwrap_or(Fp::ZERO);
        let p_x = x * z_inv;
        let p_y = y * z_inv.square();
        let p = G1Projective::from_raw_unchecked(
            p_x,
            Fp::conditional_select(&p_y, &Fp::ONE, z.is_zero()),
            z,
        );
        CtOption::new(p, p.is_on_curve())
    }
}

impl CurveAffine for G1Affine {
    type ScalarExt = Fq;
    type Base = Fp;
    type CurveExt = G1Projective;

    fn coordinates(&self) -> CtOption<Coordinates<Self>> {
        Coordinates::from_xy(self.x(), self.y())
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> CtOption<Self> {
        let p = Self::from_raw_unchecked(x, y, false);
        CtOption::new(p, p.is_on_curve())
    }

    fn is_on_curve(&self) -> Choice {
        unsafe { Choice::from(blst_p1_affine_on_curve(&self.0) as u8) }
    }

    fn a() -> Self::Base {
        A
    }

    fn b() -> Self::Base {
        B
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::eq_op)]

    use ff::Field;
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    #[test]
    fn curve_tests() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        {
            let z = G1Projective::identity();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
        }

        // Negation edge case with zero.
        {
            let mut z = G1Projective::identity();
            z = z.neg();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
        }

        // Doubling edge case with zero.
        {
            let mut z = G1Projective::identity();
            z = z.double();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
        }

        // Addition edge cases with zero
        {
            let mut r = G1Projective::random(&mut rng);
            let rcopy = r;
            r += &G1Projective::identity();
            assert_eq!(r, rcopy);
            r += &G1Affine::identity();
            assert_eq!(r, rcopy);

            let mut z = G1Projective::identity();
            z += &G1Projective::identity();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
            z += &G1Affine::identity();
            assert_eq!(z.is_identity().unwrap_u8(), 1);

            let mut z2 = z;
            z2 += &r;

            z += &G1Affine::from(r);

            assert_eq!(z, z2);
            assert_eq!(z, r);
        }

        // Transformations
        {
            let a = G1Projective::random(&mut rng);
            let b: G1Projective = G1Affine::from(a).into();
            let c = G1Projective::from(G1Affine::from(G1Projective::from(G1Affine::from(a))));

            assert_eq!(a, b);
            assert_eq!(b, c);
        }
    }

    #[test]
    fn test_is_on_curve() {
        assert_eq!(G1Projective::identity().is_on_curve().unwrap_u8(), 1);
        assert_eq!(G1Projective::generator().is_on_curve().unwrap_u8(), 1);

        assert_eq!(G1Affine::identity().is_on_curve().unwrap_u8(), 1);
        assert_eq!(G1Affine::generator().is_on_curve().unwrap_u8(), 1);

        let z = Fp::from_mont_unchecked([
            0xba7afa1f9a6fe250,
            0xfa0f5b595eafe731,
            0x3bdc477694c306e7,
            0x2149be4b3949fa24,
            0x64aa6e0649b2078c,
            0x12b108ac33643c3e,
        ]);

        let gen = G1Affine::generator();
        let z2 = z.square();
        let mut test = G1Projective::from_raw_unchecked(gen.x() * z2, gen.y() * (z2 * z), z);

        assert_eq!(test.is_on_curve().unwrap_u8(), 1);

        test.0.x = z.0;
        assert_eq!(test.is_on_curve().unwrap_u8(), 0);
    }

    #[test]
    fn test_affine_point_equality() {
        let a = G1Affine::generator();
        let b = G1Affine::identity();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);
    }

    #[test]
    fn test_projective_point_equality() {
        let a = G1Projective::generator();
        let b = G1Projective::identity();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);

        let z = Fp::from_mont_unchecked([
            0xba7afa1f9a6fe250,
            0xfa0f5b595eafe731,
            0x3bdc477694c306e7,
            0x2149be4b3949fa24,
            0x64aa6e0649b2078c,
            0x12b108ac33643c3e,
        ]);

        let z2 = z.square();
        let mut c = G1Projective::from_raw_unchecked(a.x() * z2, a.y() * (z2 * z), z);
        assert_eq!(c.is_on_curve().unwrap_u8(), 1);

        assert_eq!(a, c);
        assert_eq!(c, a);
        assert_ne!(b, c);
        assert_ne!(c, b);

        c.0.y = (-c.y()).0;
        assert_eq!(c.is_on_curve().unwrap_u8(), 1);

        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_ne!(c, a);
        assert_ne!(c, b);

        c.0.y = (-c.y()).0;
        c.0.x = z.0;
        assert_eq!(c.is_on_curve().unwrap_u8(), 0);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
    }

    #[test]
    fn test_projective_to_affine() {
        let a = G1Projective::generator();
        let b = G1Projective::identity();

        assert_eq!(G1Affine::from(a).is_on_curve().unwrap_u8(), 1);
        assert_eq!(G1Affine::from(a).is_identity().unwrap_u8(), 0);
        assert_eq!(G1Affine::from(b).is_on_curve().unwrap_u8(), 1);
        assert_eq!(G1Affine::from(b).is_identity().unwrap_u8(), 1);

        let z = Fp::from_mont_unchecked([
            0xba7afa1f9a6fe250,
            0xfa0f5b595eafe731,
            0x3bdc477694c306e7,
            0x2149be4b3949fa24,
            0x64aa6e0649b2078c,
            0x12b108ac33643c3e,
        ]);

        let z2 = z.square();
        let c = G1Projective::from_raw_unchecked(a.x() * z2, a.y() * (z2 * z), z);

        assert_eq!(G1Affine::from(c), G1Affine::generator());
    }

    #[test]
    fn test_affine_to_projective() {
        let a = G1Affine::generator();
        let b = G1Affine::identity();

        assert_eq!(G1Projective::from(a).is_on_curve().unwrap_u8(), 1);
        assert_eq!(G1Projective::from(a).is_identity().unwrap_u8(), 0);
        assert_eq!(G1Projective::from(b).is_on_curve().unwrap_u8(), 1);
        assert_eq!(G1Projective::from(b).is_identity().unwrap_u8(), 1);
    }

    #[test]
    fn test_doubling() {
        {
            let tmp = G1Projective::identity().double();
            assert_eq!(tmp.is_identity().unwrap_u8(), 1);
            assert_eq!(tmp.is_on_curve().unwrap_u8(), 1);
        }
        {
            let tmp = G1Projective::generator().double();
            assert_eq!(tmp.is_identity().unwrap_u8(), 0);
            assert_eq!(tmp.is_on_curve().unwrap_u8(), 1);

            assert_eq!(
                G1Affine::from(tmp),
                G1Affine::from_raw_unchecked(
                    Fp::from_mont_unchecked([
                        0x53e978ce58a9ba3c,
                        0x3ea0583c4f3d65f9,
                        0x4d20bb47f0012960,
                        0xa54c664ae5b2b5d9,
                        0x26b552a39d7eb21f,
                        0x8895d26e68785
                    ]),
                    Fp::from_mont_unchecked([
                        0x70110b3298293940,
                        0xda33c5393f1f6afc,
                        0xb86edfd16a5aa785,
                        0xaec6d1c9e7b1c895,
                        0x25cfc2b522d11720,
                        0x6361c83f8d09b15
                    ]),
                    false
                )
            );
        }
    }

    #[test]
    fn test_projective_addition() {
        {
            let a = G1Projective::identity();
            let b = G1Projective::identity();
            let c = a + b;
            assert_eq!(c.is_identity().unwrap_u8(), 1);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
        }
        {
            let a = G1Projective::identity();
            let mut b = G1Projective::generator();
            {
                let z = Fp::from_mont_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = a + b;
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
            assert_eq!(c, G1Projective::generator());
        }
        {
            let a = G1Projective::identity();
            let mut b = G1Projective::generator();
            {
                let z = Fp::from_mont_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = b + a;
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
            assert_eq!(c, G1Projective::generator());
        }
        {
            let a = G1Projective::generator().double().double(); // 4P
            let b = G1Projective::generator().double(); // 2P
            let c = a + b;

            let mut d = G1Projective::generator();
            for _ in 0..5 {
                d += G1Projective::generator();
            }
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
            assert_eq!(d.is_identity().unwrap_u8(), 0);
            assert_eq!(d.is_on_curve().unwrap_u8(), 1);
            assert_eq!(c, d);
        }

        // Degenerate case
        {
            let mut beta = Fp::from_mont_unchecked([
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ]);
            beta = beta.square();
            let a = G1Projective::generator().double().double();
            let b = G1Projective::from_raw_unchecked(a.x() * beta, -a.y(), a.z());
            assert_eq!(a.is_on_curve().unwrap_u8(), 1);
            assert_eq!(b.is_on_curve().unwrap_u8(), 1);

            let c = a + b;
            assert_eq!(
                G1Affine::from(c),
                G1Affine::from(G1Projective::from_raw_unchecked(
                    Fp::from_mont_unchecked([
                        0x29e1e987ef68f2d0,
                        0xc5f3ec531db03233,
                        0xacd6c4b6ca19730f,
                        0x18ad9e827bc2bab7,
                        0x46e3b2c5785cc7a9,
                        0x7e571d42d22ddd6
                    ]),
                    Fp::from_mont_unchecked([
                        0x94d117a7e5a539e7,
                        0x8e17ef673d4b5d22,
                        0x9d746aaf508a33ea,
                        0x8c6d883d2516c9a2,
                        0xbc3b8d5fb0447f7,
                        0x7bfa4c7210f4f44
                    ]),
                    Fp::ONE,
                ))
            );
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
        }
    }

    #[test]
    fn test_mixed_addition() {
        {
            let a = G1Affine::identity();
            let b = G1Projective::identity();
            let c = a + b;
            assert_eq!(c.is_identity().unwrap_u8(), 1);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
        }
        {
            let a = G1Affine::identity();
            let mut b = G1Projective::generator();
            {
                let z = Fp::from_mont_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = a + b;
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
            assert_eq!(c, G1Projective::generator());
        }
        {
            let a = G1Affine::identity();
            let mut b = G1Projective::generator();
            {
                let z = Fp::from_mont_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = b + a;
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
            assert_eq!(c, G1Projective::generator());
        }
        {
            let a = G1Projective::generator().double().double(); // 4P
            let b = G1Projective::generator().double(); // 2P
            let c = a + b;

            let mut d = G1Projective::generator();
            for _ in 0..5 {
                d += G1Affine::generator();
            }
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
            assert_eq!(d.is_identity().unwrap_u8(), 0);
            assert_eq!(d.is_on_curve().unwrap_u8(), 1);
            assert_eq!(c, d);
        }

        // Degenerate case
        {
            let mut beta = Fp::from_mont_unchecked([
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ]);
            beta = beta.square();
            let a = G1Projective::generator().double().double();
            let b = G1Projective::from_raw_unchecked(a.x() * beta, -a.y(), a.z());
            let a = G1Affine::from(a);
            assert_eq!(a.is_on_curve().unwrap_u8(), 1);
            assert_eq!(b.is_on_curve().unwrap_u8(), 1);

            let c = a + b;
            assert_eq!(
                G1Affine::from(c),
                G1Affine::from(G1Projective::from_raw_unchecked(
                    Fp::from_mont_unchecked([
                        0x29e1e987ef68f2d0,
                        0xc5f3ec531db03233,
                        0xacd6c4b6ca19730f,
                        0x18ad9e827bc2bab7,
                        0x46e3b2c5785cc7a9,
                        0x7e571d42d22ddd6
                    ]),
                    Fp::from_mont_unchecked([
                        0x94d117a7e5a539e7,
                        0x8e17ef673d4b5d22,
                        0x9d746aaf508a33ea,
                        0x8c6d883d2516c9a2,
                        0xbc3b8d5fb0447f7,
                        0x7bfa4c7210f4f44
                    ]),
                    Fp::ONE
                ))
            );
            assert_eq!(c.is_identity().unwrap_u8(), 0);
            assert_eq!(c.is_on_curve().unwrap_u8(), 1);
        }
    }

    #[test]
    fn test_projective_negation_and_subtraction() {
        let a = G1Projective::generator().double();
        assert_eq!(a + (-a), G1Projective::identity());
        assert_eq!(a + (-a), a - a);
    }

    #[test]
    fn test_affine_projective_negation_and_subtraction() {
        let a = G1Affine::generator();
        assert_eq!(G1Projective::from(a) + (-a), G1Projective::identity());
        assert_eq!(G1Projective::from(a) + (-a), G1Projective::from(a) - a);
    }

    #[test]
    fn test_projective_scalar_multiplication() {
        let g = G1Projective::generator();
        let a = Fq(blst::blst_fr {
            l: [
                0x2b568297a56da71c,
                0xd8c39ecb0ef375d1,
                0x435c38da67bfbf96,
                0x8088a05026b659b2,
            ],
        });
        let b = Fq(blst::blst_fr {
            l: [
                0x785fdd9b26ef8b85,
                0xc997f25837695c18,
                0x4c8dbc39e7b756c1,
                0x70d9b6cc6d87df20,
            ],
        });
        let c = a * b;

        assert_eq!((g * a) * b, g * c);
    }

    #[test]
    fn test_affine_scalar_multiplication() {
        let g = G1Affine::generator();
        let a = Fq(blst::blst_fr {
            l: [
                0x2b568297a56da71c,
                0xd8c39ecb0ef375d1,
                0x435c38da67bfbf96,
                0x8088a05026b659b2,
            ],
        });
        let b = Fq(blst::blst_fr {
            l: [
                0x785fdd9b26ef8b85,
                0xc997f25837695c18,
                0x4c8dbc39e7b756c1,
                0x70d9b6cc6d87df20,
            ],
        });
        let c = a * b;

        assert_eq!(G1Affine::from(g * a) * b, g * c);
    }

    #[test]
    fn g1_curve_tests() {
        use group::tests::curve_tests;
        curve_tests::<G1Projective>();
    }

    #[test]
    fn test_g1_is_identity() {
        assert_eq!(G1Projective::identity().is_identity().unwrap_u8(), 1);
        assert_eq!(G1Projective::generator().is_identity().unwrap_u8(), 0);
        assert_eq!(G1Affine::identity().is_identity().unwrap_u8(), 1);
        assert_eq!(G1Affine::generator().is_identity().unwrap_u8(), 0);
    }

    #[test]
    fn test_g1_serialization_roundtrip() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            // Affine
            let el: G1Affine = G1Projective::random(&mut rng).into();
            let c = el.to_compressed();
            assert_eq!(G1Affine::from_compressed(&c).unwrap(), el);
            assert_eq!(G1Affine::from_compressed_unchecked(&c).unwrap(), el);

            let u = el.to_uncompressed();
            assert_eq!(G1Affine::from_uncompressed(&u).unwrap(), el);
            assert_eq!(G1Affine::from_uncompressed_unchecked(&u).unwrap(), el);

            let c = el.to_bytes();
            assert_eq!(G1Affine::from_bytes(&c).unwrap(), el);
            assert_eq!(G1Affine::from_bytes_unchecked(&c).unwrap(), el);

            let c = el.to_raw_bytes();
            assert_eq!(G1Affine::from_raw_bytes(&c).unwrap(), el);
            assert_eq!(G1Affine::from_raw_bytes_unchecked(&c), el);

            // Projective
            let el = G1Projective::random(&mut rng);
            let c = el.to_compressed();
            assert_eq!(G1Projective::from_compressed(&c).unwrap(), el);
            assert_eq!(G1Projective::from_compressed_unchecked(&c).unwrap(), el);

            let c = el.to_bytes();
            assert_eq!(G1Projective::from_bytes(&c).unwrap(), el);
            assert_eq!(G1Projective::from_bytes_unchecked(&c).unwrap(), el);
        }
    }

    #[test]
    fn test_multi_exp() {
        const SIZE: usize = 10;
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let points: Vec<G1Projective> = (0..SIZE).map(|_| G1Projective::random(&mut rng)).collect();
        let scalars: Vec<Fq> = (0..SIZE).map(|_| Fq::random(&mut rng)).collect();

        let mut naive = points[0] * scalars[0];
        for i in 1..SIZE {
            naive += points[i] * scalars[i];
        }

        let pippenger = G1Projective::multi_exp(points.as_slice(), scalars.as_slice());

        assert_eq!(naive, pippenger);
    }
}

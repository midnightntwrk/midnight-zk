//! An implementation of the $\mathbb{G}_2$ group of BLS12-381.
#![allow(unused_variables)]

use core::{
    borrow::Borrow,
    fmt,
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::{
    convert::TryInto,
    io::Read,
    ops::{Deref, DerefMut},
};

use blst::*;
use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding, WnafGroup,
};
use halo2curves::{serde::SerdeObject, Coordinates, CurveAffine, CurveExt};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{fp::Fp, fp2::Fp2, Bls12, Engine, Fq, G1Affine, Gt, PairingCurveAffine};

/// This is an element of $\mathbb{G}_2$ represented in the affine coordinate
/// space. It is ideal to keep elements in this representation to reduce memory
/// usage and improve performance through the use of mixed curve model
/// arithmetic.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G2Affine(pub(crate) blst_p2_affine);

const COMPRESSED_SIZE: usize = 96;
const UNCOMPRESSED_SIZE: usize = 192;

impl fmt::Debug for G2Affine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let is_ident: bool = self.is_identity().into();
        f.debug_struct("G2Affine")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("infinity", &is_ident)
            .finish()
    }
}

impl fmt::Display for G2Affine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_identity().into() {
            write!(f, "G2Affine(Infinity)")
        } else {
            write!(f, "G2Affine(x={}, y={})", self.x(), self.y())
        }
    }
}

impl core::hash::Hash for G2Affine {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.x.fp[0].l.hash::<H>(state);
        self.0.x.fp[1].l.hash::<H>(state);
        self.0.y.fp[0].l.hash::<H>(state);
        self.0.y.fp[1].l.hash::<H>(state)
    }
}

impl AsRef<blst_p2_affine> for G2Affine {
    fn as_ref(&self) -> &blst_p2_affine {
        &self.0
    }
}

impl AsMut<blst_p2_affine> for G2Affine {
    fn as_mut(&mut self) -> &mut blst_p2_affine {
        &mut self.0
    }
}

impl Default for G2Affine {
    fn default() -> G2Affine {
        G2Affine::identity()
    }
}

impl From<&G2Projective> for G2Affine {
    fn from(p: &G2Projective) -> G2Affine {
        let mut out = blst_p2_affine::default();

        unsafe { blst_p2_to_affine(&mut out, &p.0) };

        G2Affine(out)
    }
}

impl From<G2Projective> for G2Affine {
    fn from(p: G2Projective) -> G2Affine {
        G2Affine::from(&p)
    }
}

impl Eq for G2Affine {}
impl PartialEq for G2Affine {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        unsafe { blst_p2_affine_is_equal(&self.0, &other.0) }
    }
}

impl Neg for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn neg(self) -> G2Projective {
        -*self
    }
}

impl Neg for G2Projective {
    type Output = G2Projective;

    #[inline]
    fn neg(mut self) -> G2Projective {
        unsafe { blst_p2_cneg(&mut self.0, true) }
        self
    }
}

impl Neg for &G2Affine {
    type Output = G2Affine;

    #[inline]
    fn neg(self) -> G2Affine {
        -*self
    }
}

impl Neg for G2Affine {
    type Output = G2Affine;

    #[inline]
    fn neg(mut self) -> G2Affine {
        // Missing for affine in blst
        if (!self.is_identity()).into() {
            unsafe {
                blst_fp2_cneg(&mut self.0.y, &self.0.y, true);
            }
        }
        self
    }
}

impl Add<&G2Projective> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn add(self, rhs: &G2Projective) -> G2Projective {
        let mut out = blst_p2::default();
        unsafe { blst_p2_add_or_double(&mut out, &self.0, &rhs.0) };
        G2Projective(out)
    }
}

impl Add<&G2Affine> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn add(self, rhs: &G2Affine) -> G2Projective {
        self.add_mixed(rhs)
    }
}

impl Add<&G2Projective> for &G2Affine {
    type Output = G2Projective;

    #[inline]
    fn add(self, rhs: &G2Projective) -> G2Projective {
        rhs.add_mixed(self)
    }
}

impl Sub<&G2Projective> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn sub(self, rhs: &G2Projective) -> G2Projective {
        self + -rhs
    }
}

impl Sub<&G2Projective> for &G2Affine {
    type Output = G2Projective;

    #[inline]
    fn sub(self, rhs: &G2Projective) -> G2Projective {
        self + -rhs
    }
}

impl Sub<&G2Affine> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn sub(self, rhs: &G2Affine) -> G2Projective {
        self + -rhs
    }
}

impl AddAssign<&G2Projective> for G2Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G2Projective) {
        unsafe { blst_p2_add_or_double(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&G2Projective> for G2Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G2Projective) {
        *self += &-rhs
    }
}

impl AddAssign<&G2Affine> for G2Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G2Affine) {
        unsafe { blst_p2_add_or_double_affine(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&G2Affine> for G2Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G2Affine) {
        *self += &-rhs;
    }
}

impl Mul<&Fq> for &G2Projective {
    type Output = G2Projective;

    fn mul(self, scalar: &Fq) -> Self::Output {
        self.multiply(scalar)
    }
}

impl Mul<&Fq> for &G2Affine {
    type Output = G2Projective;

    fn mul(self, scalar: &Fq) -> Self::Output {
        G2Projective::from(self).multiply(scalar)
    }
}

impl MulAssign<&Fq> for G2Projective {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fq) {
        *self = *self * rhs;
    }
}

impl MulAssign<&Fq> for G2Affine {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fq) {
        *self = (*self * rhs).into();
    }
}

impl_add_sub!(G2Projective);
impl_add_sub!(G2Projective, G2Affine);
impl_add_sub!(G2Affine, G2Projective, G2Projective);

impl_add_sub_assign!(G2Projective);
impl_add_sub_assign!(G2Projective, G2Affine);

impl_mul!(G2Projective, Fq);
impl_mul!(G2Affine, Fq, G2Projective);

impl_mul_assign!(G2Projective, Fq);
impl_mul_assign!(G2Affine, Fq);

impl<T> Sum<T> for G2Projective
where
    T: Borrow<G2Projective>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl PrimeCurveAffine for G2Affine {
    type Scalar = Fq;
    type Curve = G2Projective;

    fn identity() -> Self {
        G2Affine(blst_p2_affine::default())
    }

    fn generator() -> Self {
        G2Affine(unsafe { *blst_p2_affine_generator() })
    }

    fn is_identity(&self) -> Choice {
        unsafe { Choice::from(blst_p2_affine_is_inf(&self.0) as u8) }
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl ConditionallySelectable for G2Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G2Affine(blst_p2_affine {
            x: Fp2::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp2::conditional_select(&a.y(), &b.y(), choice).0,
        })
    }
}

impl ConditionallySelectable for G2Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G2Projective(blst_p2 {
            x: Fp2::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp2::conditional_select(&a.y(), &b.y(), choice).0,
            z: Fp2::conditional_select(&a.z(), &b.z(), choice).0,
        })
    }
}

impl G2Affine {
    /// Serializes this element into compressed form.
    fn to_compressed(&self) -> [u8; COMPRESSED_SIZE] {
        let mut out = [0u8; COMPRESSED_SIZE];

        unsafe {
            blst_p2_affine_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Serializes this element into uncompressed form.
    fn to_uncompressed(&self) -> [u8; UNCOMPRESSED_SIZE] {
        let mut out = [0u8; UNCOMPRESSED_SIZE];

        unsafe {
            blst_p2_affine_serialize(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize an uncompressed element.
    fn from_uncompressed(bytes: &[u8; UNCOMPRESSED_SIZE]) -> CtOption<Self> {
        G2Affine::from_uncompressed_unchecked(bytes)
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
        let mut raw = blst_p2_affine::default();
        let success =
            unsafe { blst_p2_deserialize(&mut raw, bytes.as_ptr()) == BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G2Affine(raw), Choice::from(success as u8))
    }

    /// Attempts to deserialize a compressed element.
    fn from_compressed(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        G2Affine::from_compressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_on_curve() & p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading;
    /// otherwise, API invariants may be broken.** Please consider using
    /// `from_compressed()` instead.
    fn from_compressed_unchecked(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        let mut raw = blst_p2_affine::default();
        let success =
            unsafe { blst_p2_uncompress(&mut raw, bytes.as_ptr()) == BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G2Affine(raw), Choice::from(success as u8))
    }

    pub const fn uncompressed_size() -> usize {
        UNCOMPRESSED_SIZE
    }

    pub const fn compressed_size() -> usize {
        COMPRESSED_SIZE
    }
}

impl G2Affine {
    /// Returns true if this point is free of an $h$-torsion component, and so
    /// it exists within the $q$-order subgroup $\mathbb{G}_2$. This should
    /// always return true unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        unsafe { Choice::from(blst_p2_affine_in_g2(&self.0) as u8) }
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp2 {
        Fp2(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp2 {
        Fp2(self.0.y)
    }

    #[cfg(test)]
    fn from_raw_unchecked(x: Fp2, y: Fp2, _infinity: bool) -> Self {
        let raw = blst_p2_affine { x: x.0, y: y.0 };
        G2Affine(raw)
    }
}

impl SerdeObject for G2Affine {
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

/// This is an element of $\mathbb{G}_2$ represented in the projective
/// coordinate space.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G2Projective(pub(crate) blst_p2);

impl fmt::Debug for G2Projective {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("G2Projective")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("z", &self.z())
            .finish()
    }
}

impl fmt::Display for G2Projective {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", G2Affine::from(self))
    }
}

impl AsRef<blst_p2> for G2Projective {
    fn as_ref(&self) -> &blst_p2 {
        &self.0
    }
}

impl AsMut<blst_p2> for G2Projective {
    fn as_mut(&mut self) -> &mut blst_p2 {
        &mut self.0
    }
}

impl From<&G2Affine> for G2Projective {
    fn from(p: &G2Affine) -> G2Projective {
        let mut out = blst_p2::default();

        unsafe { blst_p2_from_affine(&mut out, &p.0) };

        G2Projective(out)
    }
}

impl From<G2Affine> for G2Projective {
    fn from(p: G2Affine) -> G2Projective {
        G2Projective::from(&p)
    }
}

impl Eq for G2Projective {}
impl PartialEq for G2Projective {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let self_is_zero: bool = self.is_identity().into();
        let other_is_zero: bool = other.is_identity().into();
        (self_is_zero && other_is_zero)
            || (!self_is_zero && !other_is_zero && unsafe { blst_p2_is_equal(&self.0, &other.0) })
    }
}

impl G2Projective {
    /// Serializes this element into compressed form.
    fn to_compressed(&self) -> [u8; COMPRESSED_SIZE] {
        let mut out = [0u8; COMPRESSED_SIZE];

        unsafe {
            blst_p2_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize a compressed element.
    fn from_compressed(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        G2Affine::from_compressed(bytes).map(Into::into)
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading;
    /// otherwise, API invariants may be broken.** Please consider using
    /// `from_compressed()` instead.
    fn from_compressed_unchecked(bytes: &[u8; COMPRESSED_SIZE]) -> CtOption<Self> {
        G2Affine::from_compressed_unchecked(bytes).map(Into::into)
    }
}

impl G2Projective {
    /// Adds this point to another point in the affine model.
    pub fn add_mixed(&self, rhs: &G2Affine) -> G2Projective {
        let mut out = blst_p2::default();

        unsafe { blst_p2_add_or_double_affine(&mut out, &self.0, &rhs.0) };

        G2Projective(out)
    }

    fn multiply(&self, scalar: &Fq) -> G2Projective {
        let mut out = blst_p2::default();

        // Sclar is 255 bits wide.
        const NBITS: usize = 255;

        unsafe { blst_p2_mult(&mut out, &self.0, scalar.to_bytes_le().as_ptr(), NBITS) };

        G2Projective(out)
    }

    fn from_raw_unchecked(x: Fp2, y: Fp2, z: Fp2) -> Self {
        let raw = blst_p2 {
            x: x.0,
            y: y.0,
            z: z.0,
        };
        G2Projective(raw)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp2 {
        Fp2(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp2 {
        Fp2(self.0.y)
    }

    /// Returns the z coordinate.
    pub fn z(&self) -> Fp2 {
        Fp2(self.0.z)
    }

    /// Hash to curve algorithm.
    pub fn hash_to_curve(msg: &[u8], dst: &[u8], aug: &[u8]) -> Self {
        let mut res = Self::identity();
        unsafe {
            blst_hash_to_g2(
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
            unsafe { std::slice::from_raw_parts(points.as_ptr() as *const blst_p2, points.len()) };
        let points = p2_affines::from(points);

        let mut scalar_bytes: Vec<u8> = Vec::with_capacity(n * 32);
        for a in scalars.iter().map(|s| s.to_bytes_le()) {
            scalar_bytes.extend_from_slice(&a);
        }

        let res = points.mult(scalar_bytes.as_slice(), 255);

        G2Projective(res)
    }
}

impl Group for G2Projective {
    type Scalar = Fq;

    fn random(mut rng: impl RngCore) -> Self {
        let mut out = blst_p2::default();
        let mut msg = [0u8; 64];
        rng.fill_bytes(&mut msg);
        const DST: [u8; 16] = [0; 16];
        const AUG: [u8; 16] = [0; 16];

        unsafe {
            blst_encode_to_g2(
                &mut out,
                msg.as_ptr(),
                msg.len(),
                DST.as_ptr(),
                DST.len(),
                AUG.as_ptr(),
                AUG.len(),
            )
        };

        G2Projective(out)
    }

    fn identity() -> Self {
        G2Projective(blst_p2::default())
    }

    fn generator() -> Self {
        G2Projective(unsafe { *blst_p2_generator() })
    }

    fn is_identity(&self) -> Choice {
        unsafe { Choice::from(blst_p2_is_inf(&self.0) as u8) }
    }

    fn double(&self) -> Self {
        let mut double = blst_p2::default();
        unsafe { blst_p2_double(&mut double, &self.0) };
        G2Projective(double)
    }
}

impl WnafGroup for G2Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 11] = [1, 3, 8, 20, 47, 126, 260, 826, 1501, 4555, 84071];

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

impl PrimeGroup for G2Projective {}

impl Curve for G2Projective {
    type AffineRepr = G2Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G2Projective {
    type Affine = G2Affine;
}

impl GroupEncoding for G2Projective {
    type Repr = G2Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G2Compressed(self.to_compressed())
    }
}

impl GroupEncoding for G2Affine {
    type Repr = G2Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G2Compressed(self.to_compressed())
    }
}

impl UncompressedEncoding for G2Affine {
    type Uncompressed = G2Uncompressed;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed(&bytes.0)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed_unchecked(&bytes.0)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G2Uncompressed(self.to_uncompressed())
    }
}

#[derive(Clone, Debug)]
pub struct G2Prepared {
    pub(crate) lines: Vec<blst_fp6>,
    infinity: bool,
}

impl From<G2Affine> for G2Prepared {
    fn from(affine: G2Affine) -> Self {
        if affine.is_identity().into() {
            G2Prepared {
                lines: Vec::new(),
                infinity: true,
            }
        } else {
            let mut lines = vec![blst_fp6::default(); 68];
            unsafe { blst_precompute_lines(lines.as_mut_ptr(), &affine.0) }
            G2Prepared {
                lines,
                infinity: false,
            }
        }
    }
}

impl G2Prepared {
    pub fn is_identity(&self) -> Choice {
        Choice::from(self.infinity as u8)
    }
}

impl PairingCurveAffine for G2Affine {
    type Pair = G1Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        <Bls12 as Engine>::pairing(other, self)
    }
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G2Uncompressed([u8; UNCOMPRESSED_SIZE]);

encoded_point_delegations!(G2Uncompressed);

impl Default for G2Uncompressed {
    fn default() -> Self {
        G2Uncompressed([0u8; UNCOMPRESSED_SIZE])
    }
}

impl fmt::Debug for G2Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct G2Compressed([u8; COMPRESSED_SIZE]);

encoded_point_delegations!(G2Compressed);

impl Default for G2Compressed {
    fn default() -> Self {
        G2Compressed([0u8; COMPRESSED_SIZE])
    }
}

impl fmt::Debug for G2Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl Add for G2Affine {
    type Output = <Self as PrimeCurveAffine>::Curve;

    fn add(self, rhs: Self) -> Self::Output {
        G2Projective::from(self) + rhs
    }
}

impl Sub for G2Affine {
    type Output = <Self as PrimeCurveAffine>::Curve;

    fn sub(self, rhs: G2Affine) -> Self::Output {
        G2Projective::from(self) - rhs
    }
}

impl ConstantTimeEq for G2Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        let z1 = self.is_identity();
        let z2 = other.is_identity();

        (z1 & z2) | ((!z1) & (!z2) & (self.x().ct_eq(&other.x())) & (self.y().ct_eq(&other.y())))
    }
}

impl ConstantTimeEq for G2Projective {
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

// Wrapper needed, because we don't have Default implemented for [0u8; 48]
#[derive(Copy, Clone)]
pub struct Fp2Repr([u8; 96]);

impl Default for Fp2Repr {
    fn default() -> Self {
        Self([0u8; 96])
    }
}

impl Deref for Fp2Repr {
    type Target = [u8; 96];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<[u8]> for Fp2Repr {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for Fp2Repr {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

impl DerefMut for Fp2Repr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl PrimeField for Fp2 {
    type Repr = Fp2Repr;
    const MODULUS: &'static str = <Fp as PrimeField>::MODULUS;
    const MULTIPLICATIVE_GENERATOR: Self = Fp2::new(Fp::MULTIPLICATIVE_GENERATOR, Fp::ZERO);
    const NUM_BITS: u32 = Fp::NUM_BITS;
    const CAPACITY: u32 = Fp::NUM_BITS;
    const S: u32 = Fp::S;

    // TODO: Check that we can just 0 this and forget.
    const ROOT_OF_UNITY: Self = Fp2::ZERO;
    const ROOT_OF_UNITY_INV: Self = Fp2::ZERO;
    const DELTA: Self = Fp2::ZERO;

    const TWO_INV: Self = Fp2::new(Fp::TWO_INV, Fp::ZERO);

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let c0: [u8; 48] = repr[..48].try_into().unwrap();
        let c0: <Fp as PrimeField>::Repr = c0.into();
        let c0 = Fp::from_repr(c0);

        let c1: [u8; 48] = repr[48..].try_into().unwrap();
        let c1: <Fp as PrimeField>::Repr = c1.into();
        let c1 = Fp::from_repr(c1);

        CtOption::new(Fp2::new(c0.unwrap(), c1.unwrap()), Choice::from(1))
    }

    fn to_repr(&self) -> Self::Repr {
        let mut res = Self::Repr::default();
        let c0 = self.c0().to_repr();
        let c1 = self.c1().to_repr();
        res[0..48].copy_from_slice(c0.as_ref());
        res[48..48 * 2].copy_from_slice(c1.as_ref());
        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr().as_ref()[0] & 1)
    }
}

const G2_A: Fp2 = Fp2::ZERO;
const G2_B: Fp2 = Fp2(blst_fp2 {
    fp: [
        blst_fp {
            // 0x04 in Montgomery form.
            l: [
                0xaa27_0000_000c_fff3,
                0x53cc_0032_fc34_000a,
                0x478f_e97a_6b0a_807f,
                0xb1d3_7ebe_e6ba_24d7,
                0x8ec9_733b_bf78_ab2f,
                0x09d6_4551_3d83_de7e,
            ],
        },
        // 0x04 in Montgomery form.
        blst_fp {
            l: [
                0xaa27_0000_000c_fff3,
                0x53cc_0032_fc34_000a,
                0x478f_e97a_6b0a_807f,
                0xb1d3_7ebe_e6ba_24d7,
                0x8ec9_733b_bf78_ab2f,
                0x09d6_4551_3d83_de7e,
            ],
        },
    ],
});

impl Default for G2Projective {
    fn default() -> Self {
        G2Projective::identity()
    }
}
impl CurveExt for G2Projective {
    type ScalarExt = Fq;
    type Base = Fp2;
    type AffineExt = G2Affine;
    const CURVE_ID: &'static str = "";

    fn endo(&self) -> Self {
        let x_zeta = self.x() * Fp2::ZETA;
        let raw = blst_p2 {
            x: x_zeta.0,
            y: self.y().0,
            z: self.z().0,
        };

        G2Projective(raw)
    }

    fn jacobian_coordinates(&self) -> (Self::Base, Self::Base, Self::Base) {
        // Homogeneous to Jacobian
        let x = self.x() * self.z();
        let y = self.y() * self.z().square();
        (x, y, self.z())
    }

    fn hash_to_curve<'a>(domain_prefix: &'a str) -> Box<dyn Fn(&[u8]) -> Self + 'a> {
        unimplemented!()
    }

    fn is_on_curve(&self) -> Choice {
        let is_on_curve = unsafe { Choice::from(blst_p2_on_curve(&self.0) as u8) };
        is_on_curve | self.is_identity()
    }

    fn a() -> Self::Base {
        G2_A
    }

    fn b() -> Self::Base {
        G2_B
    }

    fn new_jacobian(x: Self::Base, y: Self::Base, z: Self::Base) -> CtOption<Self> {
        // Jacobian to homogeneous
        let z_inv = z.invert().unwrap_or(Fp2::ZERO);
        let p_x = x * z_inv;
        let p_y = y * z_inv.square();
        let p = G2Projective::from_raw_unchecked(
            p_x,
            Fp2::conditional_select(&p_y, &Fp2::ONE, z.is_zero()),
            z,
        );
        CtOption::new(p, p.is_on_curve())
    }
}

impl CurveAffine for G2Affine {
    type ScalarExt = Fq;
    type Base = Fp2;
    type CurveExt = G2Projective;

    fn coordinates(&self) -> CtOption<Coordinates<Self>> {
        Coordinates::from_xy(self.x(), self.y())
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> CtOption<Self> {
        let raw = blst_p2_affine { x: x.0, y: y.0 };
        let p = G2Affine(raw);
        CtOption::new(p, p.is_on_curve())
    }

    fn is_on_curve(&self) -> Choice {
        unsafe { Choice::from(blst_p2_affine_on_curve(&self.0) as u8) }
    }

    fn a() -> Self::Base {
        G2_A
    }

    fn b() -> Self::Base {
        G2_B
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::eq_op)]

    use ff::Field;
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;
    use crate::fp::Fp;

    #[test]
    fn curve_tests() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Negation edge case with zero.
        {
            let mut z = G2Projective::identity();
            z = z.neg();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
        }

        // Doubling edge case with zero.
        {
            let mut z = G2Projective::identity();
            z = z.double();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
        }

        // Addition edge cases with zero
        {
            let mut r = G2Projective::random(&mut rng);
            let rcopy = r;
            r += &G2Projective::identity();
            assert_eq!(r, rcopy);
            r += &G2Affine::identity();
            assert_eq!(r, rcopy);

            let mut z = G2Projective::identity();
            z += &G2Projective::identity();
            assert_eq!(z.is_identity().unwrap_u8(), 1);
            z += &G2Affine::identity();
            assert_eq!(z.is_identity().unwrap_u8(), 1);

            let mut z2 = z;
            z2 += &r;

            z += &G2Affine::from(r);

            assert_eq!(z, z2);
            assert_eq!(z, r);
        }

        // Transformations
        {
            let a = G2Projective::random(&mut rng);
            let b: G2Projective = G2Affine::from(a).into();
            let c = G2Projective::from(G2Affine::from(G2Projective::from(G2Affine::from(a))));

            assert_eq!(a, b);
            assert_eq!(b, c);
        }
    }

    #[test]
    fn g2_test_is_valid() {
        // Reject point on isomorphic twist (b = 3 * (u + 1))
        {
            let p = G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xa757072d9fa35ba9,
                        0xae3fb2fb418f6e8a,
                        0xc1598ec46faa0c7c,
                        0x7a17a004747e3dbe,
                        0xcc65406a7c2e5a73,
                        0x10b8c03d64db4d0c,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xd30e70fe2f029778,
                        0xda30772df0f5212e,
                        0x5b47a9ff9a233a50,
                        0xfb777e5b9b568608,
                        0x789bac1fec71a2b9,
                        0x1342f02e2da54405,
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xfe0812043de54dca,
                        0xe455171a3d47a646,
                        0xa493f36bc20be98a,
                        0x663015d9410eb608,
                        0x78e82a79d829a544,
                        0x40a00545bb3c1e,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x4709802348e79377,
                        0xb5ac4dc9204bcfbd,
                        0xda361c97d02f42b2,
                        0x15008b1dc399e8df,
                        0x68128fd0548a3829,
                        0x16a613db5c873aaa,
                    ])
                    .unwrap(),
                ),
                false,
            );
            assert_eq!(p.is_on_curve().unwrap_u8(), 0);
        }

        // Reject point on a twist (b = 2 * (u + 1))
        {
            let p = G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xf4fdfe95a705f917,
                        0xc2914df688233238,
                        0x37c6b12cca35a34b,
                        0x41abba710d6c692c,
                        0xffcc4b2b62ce8484,
                        0x6993ec01b8934ed,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xb94e92d5f874e26,
                        0x44516408bc115d95,
                        0xe93946b290caa591,
                        0xa5a0c2b7131f3555,
                        0x83800965822367e7,
                        0x10cf1d3ad8d90bfa,
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xbf00334c79701d97,
                        0x4fe714f9ff204f9a,
                        0xab70b28002f3d825,
                        0x5a9171720e73eb51,
                        0x38eb4fd8d658adb7,
                        0xb649051bbc1164d,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x9225814253d7df75,
                        0xc196c2513477f887,
                        0xe05e2fbd15a804e0,
                        0x55f2b8efad953e04,
                        0x7379345eda55265e,
                        0x377f2e6208fd4cb,
                    ])
                    .unwrap(),
                ),
                false,
            );
            assert_eq!(p.is_on_curve().unwrap_u8(), 0);
            assert_eq!(p.is_torsion_free().unwrap_u8(), 0);
        }

        // Reject point in an invalid subgroup
        // There is only one r-order subgroup, as r does not divide the cofactor.
        {
            let p = G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x262cea73ea1906c,
                        0x2f08540770fabd6,
                        0x4ceb92d0a76057be,
                        0x2199bc19c48c393d,
                        0x4a151b732a6075bf,
                        0x17762a3b9108c4a7,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x26f461e944bbd3d1,
                        0x298f3189a9cf6ed6,
                        0x74328ad8bc2aa150,
                        0x7e147f3f9e6e241,
                        0x72a9b63583963fff,
                        0x158b0083c000462,
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x91fb0b225ecf103b,
                        0x55d42edc1dc46ba0,
                        0x43939b11997b1943,
                        0x68cad19430706b4d,
                        0x3ccfb97b924dcea8,
                        0x1660f93434588f8d,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xaaed3985b6dcb9c7,
                        0xc1e985d6d898d9f4,
                        0x618bd2ac3271ac42,
                        0x3940a2dbb914b529,
                        0xbeb88137cf34f3e7,
                        0x1699ee577c61b694,
                    ])
                    .unwrap(),
                ),
                false,
            );
            assert_eq!(p.is_on_curve().unwrap_u8(), 1);
            assert_eq!(p.is_torsion_free().unwrap_u8(), 0);
        }
    }

    #[test]
    fn test_g2_addition_correctness() {
        let mut p = G2Projective::from_raw_unchecked(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x6c994cc1e303094e,
                    0xf034642d2c9e85bd,
                    0x275094f1352123a9,
                    0x72556c999f3707ac,
                    0x4617f2e6774e9711,
                    0x100b2fe5bffe030b,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x7a33555977ec608,
                    0xe23039d1fe9c0881,
                    0x19ce4678aed4fcb5,
                    0x4637c4f417667e2e,
                    0x93ebe7c3e41f6acc,
                    0xde884f89a9a371b,
                ])
                .unwrap(),
            ),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xe073119472e1eb62,
                    0x44fb3391fe3c9c30,
                    0xaa9b066d74694006,
                    0x25fd427b4122f231,
                    0xd83112aace35cae,
                    0x191b2432407cbb7f,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xf68ae82fe97662f5,
                    0xe986057068b50b7d,
                    0x96c30f0411590b48,
                    0x9eaa6d19de569196,
                    0xf6a03d31e2ec2183,
                    0x3bdafaf7ca9b39b,
                ])
                .unwrap(),
            ),
            Fp2::ONE,
        );

        p.add_assign(&G2Projective::from_raw_unchecked(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xa8c763d25910bdd3,
                    0x408777b30ca3add4,
                    0x6115fcc12e2769e,
                    0x8e73a96b329ad190,
                    0x27c546f75ee1f3ab,
                    0xa33d27add5e7e82,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x93b1ebcd54870dfe,
                    0xf1578300e1342e11,
                    0x8270dca3a912407b,
                    0x2089faf462438296,
                    0x828e5848cd48ea66,
                    0x141ecbac1deb038b,
                ])
                .unwrap(),
            ),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xf5d2c28857229c3f,
                    0x8c1574228757ca23,
                    0xe8d8102175f5dc19,
                    0x2767032fc37cc31d,
                    0xd5ee2aba84fd10fe,
                    0x16576ccd3dd0a4e8,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x4da9b6f6a96d1dd2,
                    0x9657f7da77f1650e,
                    0xbc150712f9ffe6da,
                    0x31898db63f87363a,
                    0xabab040ddbd097cc,
                    0x11ad236b9ba02990,
                ])
                .unwrap(),
            ),
            Fp2::ONE,
        ));

        let p = G2Affine::from(p);

        assert_eq!(
            p,
            G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xcde7ee8a3f2ac8af,
                        0xfc642eb35975b069,
                        0xa7de72b7dd0e64b7,
                        0xf1273e6406eef9cc,
                        0xababd760ff05cb92,
                        0xd7c20456617e89
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xd1a50b8572cbd2b8,
                        0x238f0ac6119d07df,
                        0x4dbe924fe5fd6ac2,
                        0x8b203284c51edf6b,
                        0xc8a0b730bbb21f5e,
                        0x1a3b59d29a31274
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x9e709e78a8eaa4c9,
                        0xd30921c93ec342f4,
                        0x6d1ef332486f5e34,
                        0x64528ab3863633dc,
                        0x159384333d7cba97,
                        0x4cb84741f3cafe8
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x242af0dc3640e1a4,
                        0xe90a73ad65c66919,
                        0x2bd7ca7f4346f9ec,
                        0x38528f92b689644d,
                        0xb6884deec59fb21f,
                        0x3c075d3ec52ba90
                    ])
                    .unwrap(),
                ),
                false,
            )
        );
    }

    #[test]
    fn test_g2_doubling_correctness() {
        let mut p = G2Projective::from_raw_unchecked(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x6c994cc1e303094e,
                    0xf034642d2c9e85bd,
                    0x275094f1352123a9,
                    0x72556c999f3707ac,
                    0x4617f2e6774e9711,
                    0x100b2fe5bffe030b,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x7a33555977ec608,
                    0xe23039d1fe9c0881,
                    0x19ce4678aed4fcb5,
                    0x4637c4f417667e2e,
                    0x93ebe7c3e41f6acc,
                    0xde884f89a9a371b,
                ])
                .unwrap(),
            ),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xe073119472e1eb62,
                    0x44fb3391fe3c9c30,
                    0xaa9b066d74694006,
                    0x25fd427b4122f231,
                    0xd83112aace35cae,
                    0x191b2432407cbb7f,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xf68ae82fe97662f5,
                    0xe986057068b50b7d,
                    0x96c30f0411590b48,
                    0x9eaa6d19de569196,
                    0xf6a03d31e2ec2183,
                    0x3bdafaf7ca9b39b,
                ])
                .unwrap(),
            ),
            Fp2::ONE,
        );

        p = p.double();

        let p = G2Affine::from(p);

        assert_eq!(
            p,
            G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x91ccb1292727c404,
                        0x91a6cb182438fad7,
                        0x116aee59434de902,
                        0xbcedcfce1e52d986,
                        0x9755d4a3926e9862,
                        0x18bab73760fd8024
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x4e7c5e0a2ae5b99e,
                        0x96e582a27f028961,
                        0xc74d1cf4ef2d5926,
                        0xeb0cf5e610ef4fe7,
                        0x7b4c2bae8db6e70b,
                        0xf136e43909fca0
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x954d4466ab13e58,
                        0x3ee42eec614cf890,
                        0x853bb1d28877577e,
                        0xa5a2a51f7fde787b,
                        0x8b92866bc6384188,
                        0x81a53fe531d64ef
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x4c5d607666239b34,
                        0xeddb5f48304d14b3,
                        0x337167ee6e8e3cb6,
                        0xb271f52f12ead742,
                        0x244e6c2015c83348,
                        0x19e2deae6eb9b441
                    ])
                    .unwrap(),
                ),
                false,
            )
        );
    }

    #[test]
    fn test_affine_point_equality() {
        let a = G2Affine::generator();
        let b = G2Affine::identity();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);
    }

    #[test]
    fn test_projective_point_equality() {
        let a = G2Projective::generator();
        let b = G2Projective::identity();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);
    }

    #[test]
    fn g2_curve_tests() {
        use group::tests::curve_tests;
        curve_tests::<G2Projective>();
    }

    #[test]
    fn test_g2_is_identity() {
        assert_eq!(G2Projective::identity().is_identity().unwrap_u8(), 1);
        assert_eq!(G2Projective::generator().is_identity().unwrap_u8(), 0);
        assert_eq!(G2Affine::identity().is_identity().unwrap_u8(), 1);
        assert_eq!(G2Affine::generator().is_identity().unwrap_u8(), 0);
    }

    #[test]
    fn test_g2_serialization_roundtrip() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let el: G2Affine = G2Projective::random(&mut rng).into();
            let c = el.to_compressed();
            assert_eq!(G2Affine::from_compressed(&c).unwrap(), el);
            assert_eq!(G2Affine::from_compressed_unchecked(&c).unwrap(), el);

            let u = el.to_uncompressed();
            assert_eq!(G2Affine::from_uncompressed(&u).unwrap(), el);
            assert_eq!(G2Affine::from_uncompressed_unchecked(&u).unwrap(), el);

            let c = el.to_bytes();
            assert_eq!(G2Affine::from_bytes(&c).unwrap(), el);
            assert_eq!(G2Affine::from_bytes_unchecked(&c).unwrap(), el);

            let el = G2Projective::random(&mut rng);
            let c = el.to_compressed();
            assert_eq!(G2Projective::from_compressed(&c).unwrap(), el);
            assert_eq!(G2Projective::from_compressed_unchecked(&c).unwrap(), el);

            let c = el.to_bytes();
            assert_eq!(G2Projective::from_bytes(&c).unwrap(), el);
            assert_eq!(G2Projective::from_bytes_unchecked(&c).unwrap(), el);
        }
    }

    #[test]
    fn test_multi_exp() {
        const SIZE: usize = 128;
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let points: Vec<G2Projective> = (0..SIZE).map(|_| G2Projective::random(&mut rng)).collect();
        let scalars: Vec<Fq> = (0..SIZE).map(|_| Fq::random(&mut rng)).collect();

        let mut naive = points[0] * scalars[0];
        for i in 1..SIZE {
            naive += points[i] * scalars[i];
        }

        let pippenger = G2Projective::multi_exp(points.as_slice(), scalars.as_slice());

        assert_eq!(naive, pippenger);
    }
}

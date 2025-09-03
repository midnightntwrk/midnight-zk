//! This module implements arithmetic over the quadratic extension field Fp2.

use core::{
    cmp::{Ord, Ordering, PartialOrd},
    fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use blst::*;
use ff::Field;
use halo2curves::serde::SerdeObject;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::fp::{Fp, FROBENIUS_COEFF_FP2_C1};

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Fp2(pub(crate) blst_fp2);

impl fmt::Debug for Fp2 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Fp2")
            .field("c0", &self.c0())
            .field("c1", &self.c1())
            .finish()
    }
}

impl fmt::Display for Fp2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fq2({:?} + {:?} * u)", self.c0(), self.c1())
    }
}

impl core::hash::Hash for Fp2 {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.fp[0].l.hash::<H>(state);
        self.0.fp[1].l.hash::<H>(state)
    }
}

impl From<Fp> for Fp2 {
    fn from(f: Fp) -> Fp2 {
        Fp2::new(f, Fp::ZERO)
    }
}

impl From<blst_fp2> for Fp2 {
    fn from(val: blst_fp2) -> Fp2 {
        Fp2(val)
    }
}

impl From<Fp2> for blst_fp2 {
    fn from(val: Fp2) -> blst_fp2 {
        val.0
    }
}

impl From<u64> for Fp2 {
    fn from(val: u64) -> Fp2 {
        Fp2::new(Fp::from(val), Fp::ZERO)
    }
}

impl Default for Fp2 {
    fn default() -> Self {
        Fp2::ZERO
    }
}

/// `Fq2` elements are ordered lexicographically.
impl Ord for Fp2 {
    #[inline(always)]
    fn cmp(&self, other: &Fp2) -> Ordering {
        match self.c1().cmp(&other.c1()) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.c0().cmp(&other.c0()),
        }
    }
}

impl PartialOrd for Fp2 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fp2) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for Fp2 {}

impl PartialEq for Fp2 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.fp == other.0.fp
    }
}

impl ConstantTimeEq for Fp2 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0().ct_eq(&other.c0()) & self.c1().ct_eq(&other.c1())
    }
}

impl ConditionallySelectable for Fp2 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp2(blst_fp2 {
            fp: [
                Fp::conditional_select(&a.c0(), &b.c0(), choice).0,
                Fp::conditional_select(&a.c1(), &b.c1(), choice).0,
            ],
        })
    }
}

impl Neg for &Fp2 {
    type Output = Fp2;

    #[inline]
    fn neg(self) -> Fp2 {
        -*self
    }
}

impl Neg for Fp2 {
    type Output = Fp2;

    #[inline]
    fn neg(mut self) -> Fp2 {
        unsafe { blst_fp2_cneg(&mut self.0, &self.0, true) };
        self
    }
}

impl Add<&Fp2> for &Fp2 {
    type Output = Fp2;

    #[inline]
    fn add(self, rhs: &Fp2) -> Fp2 {
        let mut out = *self;
        out += rhs;
        out
    }
}

impl Sub<&Fp2> for &Fp2 {
    type Output = Fp2;

    #[inline]
    fn sub(self, rhs: &Fp2) -> Fp2 {
        let mut out = *self;
        out -= rhs;
        out
    }
}

impl Mul<&Fp2> for &Fp2 {
    type Output = Fp2;

    #[inline]
    fn mul(self, rhs: &Fp2) -> Fp2 {
        let mut out = *self;
        out *= rhs;
        out
    }
}

impl AddAssign<&Fp2> for Fp2 {
    #[inline]
    fn add_assign(&mut self, rhs: &Fp2) {
        unsafe { blst_fp2_add(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&Fp2> for Fp2 {
    #[inline]
    fn sub_assign(&mut self, rhs: &Fp2) {
        unsafe { blst_fp2_sub(&mut self.0, &self.0, &rhs.0) };
    }
}

impl MulAssign<&Fp2> for Fp2 {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fp2) {
        unsafe { blst_fp2_mul(&mut self.0, &self.0, &rhs.0) };
    }
}

impl_add_sub!(Fp2);
impl_add_sub_assign!(Fp2);
impl_mul!(Fp2);
impl_mul_assign!(Fp2);
impl_sum!(Fp2);
impl_product!(Fp2);

impl Fp2 {
    /// Constructs an element of `Fp2`.
    pub const fn new(c0: Fp, c1: Fp) -> Fp2 {
        Fp2(blst_fp2 { fp: [c0.0, c1.0] })
    }

    /// Multiplies `self` with `3`, returning the result.
    pub fn mul3(&self) -> Self {
        let mut out = *self;
        unsafe { blst_fp2_mul_by_3(&mut out.0, &self.0) };
        out
    }

    /// Multiplies `self` with `8`, returning the result.
    pub fn mul8(&self) -> Self {
        let mut out = *self;
        unsafe { blst_fp2_mul_by_8(&mut out.0, &self.0) };
        out
    }

    /// Left shift `self` by `count`, returning the result.
    pub fn shl(&self, count: usize) -> Self {
        let mut out = *self;
        unsafe { blst_fp2_lshift(&mut out.0, &self.0, count) };
        out
    }

    pub fn c0(&self) -> Fp {
        Fp(self.0.fp[0])
    }

    pub fn c1(&self) -> Fp {
        Fp(self.0.fp[1])
    }

    /// Multiply this element by the cubic and quadratic nonresidue 1 + u.
    pub fn mul_by_nonresidue(&mut self) {
        let t0 = self.c0();
        let c0 = self.c0() - self.c1();
        let c1 = self.c1() + t0;

        self.0.fp[0] = c0.0;
        self.0.fp[1] = c1.0;
    }

    /// Norm of Fq2 as extension field in i over Fq
    pub fn norm(&self) -> Fp {
        self.c0().square() + self.c1().square()
    }

    pub fn frobenius_map(&mut self, power: usize) {
        let mut c1 = self.c1();
        c1 *= &FROBENIUS_COEFF_FP2_C1[power % 2];
        self.0.fp[1] = c1.0;
    }

    pub fn is_quad_res(&self) -> bool {
        self.sqrt().is_some().into()
    }
}

impl Field for Fp2 {
    fn random(mut rng: impl RngCore) -> Self {
        Fp2::new(Fp::random(&mut rng), Fp::random(&mut rng))
    }

    const ZERO: Self = Fp2(blst_fp2 {
        fp: [Fp::ZERO.0, Fp::ZERO.0],
    });

    const ONE: Self = Fp2(blst_fp2 {
        fp: [Fp::ONE.0, Fp::ZERO.0],
    });

    fn is_zero(&self) -> Choice {
        self.c0().is_zero() & self.c1().is_zero()
    }

    fn square(&self) -> Self {
        let mut sq = *self;
        unsafe { blst_fp2_sqr(&mut sq.0, &self.0) }
        sq
    }

    fn double(&self) -> Self {
        let mut out = *self;
        out += self;
        out
    }

    fn invert(&self) -> CtOption<Self> {
        let is_zero = self.is_zero();
        let mut out = *self;
        unsafe { blst_fp2_eucl_inverse(&mut out.0, &self.0) };
        CtOption::new(out, !is_zero)
    }

    fn sqrt(&self) -> CtOption<Self> {
        let mut out = Self::default();
        let is_quad_res = unsafe { blst_fp2_sqrt(&mut out.0, &self.0) };
        CtOption::new(out, Choice::from(is_quad_res as u8))
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        // ff::helpers::sqrt_ratio_generic(num, div)
        unimplemented!()
    }
}

// Instead of implmenting [`SerdeObject`] for Fp2, we implement just
// `write_raw`. This is all we need to implement [`SerdeObject`] for
// [`G2Affine`].
impl Fp2 {
    pub fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        self.c0().write_raw(writer)?;
        self.c1().write_raw(writer)
    }
}

impl ff::WithSmallOrderMulGroup<3> for Fp2 {
    const ZETA: Self = Fp2::new(Fp::ZETA, Fp::ZERO);
}

impl halo2curves::ff_ext::Legendre for Fp2 {
    fn legendre(&self) -> i64 {
        self.norm().legendre()
    }
}

#[cfg(test)]
mod tests {
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    #[test]
    fn test_fp2_ordering() {
        let mut a = Fp2::new(Fp::ZERO, Fp::ZERO);
        let mut b = a;

        assert!(a.cmp(&b) == Ordering::Equal);
        b.0.fp[0] = (b.c0() + Fp::ONE).0;
        assert!(a.cmp(&b) == Ordering::Less);
        a.0.fp[0] = (a.c0() + Fp::ONE).0;
        assert!(a.cmp(&b) == Ordering::Equal);
        b.0.fp[1] = (b.c1() + Fp::ONE).0;
        assert!(a.cmp(&b) == Ordering::Less);
        a.0.fp[0] = (a.c0() + Fp::ONE).0;
        assert!(a.cmp(&b) == Ordering::Less);
        a.0.fp[1] = (a.c1() + Fp::ONE).0;
        assert!(a.cmp(&b) == Ordering::Greater);
        b.0.fp[0] = (b.c0() + Fp::ONE).0;
        assert!(a.cmp(&b) == Ordering::Equal);
    }

    #[test]
    fn test_fp2_basics() {
        assert_eq!(Fp2::new(Fp::ZERO, Fp::ZERO), Fp2::ZERO);
        assert_eq!(Fp2::new(Fp::ONE, Fp::ZERO), Fp2::ONE);
        assert!(bool::from(Fp2::ZERO.is_zero()));
        assert!(!bool::from(Fp2::ONE.is_zero()));
        assert!(!bool::from(Fp2::new(Fp::ZERO, Fp::ONE,).is_zero()));
    }

    #[test]
    fn test_fp2_squaring() {
        let a = Fp2::new(Fp::ONE, Fp::ONE); // u + 1
        let a_sq = a.square();
        assert_eq!(a_sq, Fp2::new(Fp::ZERO, Fp::from(2))); // 2u

        let a = Fp2::new(Fp::ZERO, Fp::ONE); // u
        let a_sq = a.square();
        assert_eq!(a_sq, Fp2::new(-Fp::ONE, Fp::ZERO)); // -1

        let a = Fp2::new(
            Fp::from_u64s_le(&[
                0x9c2c6309bbf8b598,
                0x4eef5c946536f602,
                0x90e34aab6fb6a6bd,
                0xf7f295a94e58ae7c,
                0x41b76dcc1c3fbe5e,
                0x7080c5fa1d8e042,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x38f473b3c870a4ab,
                0x6ad3291177c8c7e5,
                0xdac5a4c911a4353e,
                0xbfb99020604137a0,
                0xfc58a7b7be815407,
                0x10d1615e75250a21,
            ])
            .unwrap(),
        );
        let a_sq = a.square();
        assert_eq!(
            a_sq,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xf262c28c538bcf68,
                    0xb9f2a66eae1073ba,
                    0xdc46ab8fad67ae0,
                    0xcb674157618da176,
                    0x4cf17b5893c3d327,
                    0x7eac81369c43361
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xc1579cf58e980cf8,
                    0xa23eb7e12dd54d98,
                    0xe75138bce4cec7aa,
                    0x38d0d7275a9689e1,
                    0x739c983042779a65,
                    0x1542a61c8a8db994
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_mul() {
        let mut a = Fp2::new(
            Fp::from_u64s_le(&[
                0x85c9f989e1461f03,
                0xa2e33c333449a1d6,
                0x41e461154a7354a3,
                0x9ee53e7e84d7532e,
                0x1c202d8ed97afb45,
                0x51d3f9253e2516f,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0xa7348a8b511aedcf,
                0x143c215d8176b319,
                0x4cc48081c09b8903,
                0x9533e4a9a5158be,
                0x7a5e1ecb676d65f9,
                0x180c3ee46656b008,
            ])
            .unwrap(),
        );
        a *= &Fp2::new(
            Fp::from_u64s_le(&[
                0xe21f9169805f537e,
                0xfc87e62e179c285d,
                0x27ece175be07a531,
                0xcd460f9f0c23e430,
                0x6c9110292bfa409,
                0x2c93a72eb8af83e,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x4b1c3f936d8992d4,
                0x1d2a72916dba4c8a,
                0x8871c508658d1e5f,
                0x57a06d3135a752ae,
                0x634cd3c6c565096d,
                0x19e17334d4e93558,
            ])
            .unwrap(),
        );
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x95b5127e6360c7e4,
                    0xde29c31a19a6937e,
                    0xf61a96dacf5a39bc,
                    0x5511fe4d84ee5f78,
                    0x5310a202d92f9963,
                    0x1751afbe166e5399
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x84af0e1bd630117a,
                    0x6c63cd4da2c2aa7,
                    0x5ba6e5430e883d40,
                    0xc975106579c275ee,
                    0x33a9ac82ce4c5083,
                    0x1ef1a36c201589d
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_inverse() {
        assert_eq!(Fp2::ZERO.invert().is_none().unwrap_u8(), 1);

        let a = Fp2::new(
            Fp::from_u64s_le(&[
                0x85c9f989e1461f03,
                0xa2e33c333449a1d6,
                0x41e461154a7354a3,
                0x9ee53e7e84d7532e,
                0x1c202d8ed97afb45,
                0x51d3f9253e2516f,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0xa7348a8b511aedcf,
                0x143c215d8176b319,
                0x4cc48081c09b8903,
                0x9533e4a9a5158be,
                0x7a5e1ecb676d65f9,
                0x180c3ee46656b008,
            ])
            .unwrap(),
        );
        let a = a.invert().unwrap();
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x70300f9bcb9e594,
                    0xe5ecda5fdafddbb2,
                    0x64bef617d2915a8f,
                    0xdfba703293941c30,
                    0xa6c3d8f9586f2636,
                    0x1351ef01941b70c4
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x8c39fd76a8312cb4,
                    0x15d7b6b95defbff0,
                    0x947143f89faedee9,
                    0xcbf651a0f367afb2,
                    0xdf4e54f0d3ef15a6,
                    0x103bdf241afb0019
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_addition() {
        let mut a = Fp2::new(
            Fp::from_u64s_le(&[
                0x2d0078036923ffc7,
                0x11e59ea221a3b6d2,
                0x8b1a52e0a90f59ed,
                0xb966ce3bc2108b13,
                0xccc649c4b9532bf3,
                0xf8d295b2ded9dc,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x977df6efcdaee0db,
                0x946ae52d684fa7ed,
                0xbe203411c66fb3a5,
                0xb3f8afc0ee248cad,
                0x4e464dea5bcfd41e,
                0x12d1137b8a6a837,
            ])
            .unwrap(),
        );
        a += &Fp2::new(
            Fp::from_u64s_le(&[
                0x619a02d78dc70ef2,
                0xb93adfc9119e33e8,
                0x4bf0b99a9f0dca12,
                0x3b88899a42a6318f,
                0x986a4a62fa82a49d,
                0x13ce433fa26027f5,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x66323bf80b58b9b9,
                0xa1379b6facf6e596,
                0x402aef1fb797e32f,
                0x2236f55246d0d44d,
                0x4c8c1800eb104566,
                0x11d6e20e986c2085,
            ])
            .unwrap(),
        );
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x8e9a7adaf6eb0eb9,
                    0xcb207e6b3341eaba,
                    0xd70b0c7b481d23ff,
                    0xf4ef57d604b6bca2,
                    0x65309427b3d5d090,
                    0x14c715d5553f01d2
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xfdb032e7d9079a94,
                    0x35a2809d15468d83,
                    0xfe4b23317e0796d5,
                    0xd62fa51334f560fa,
                    0x9ad265eb46e01984,
                    0x1303f3465112c8bc
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_subtraction() {
        let mut a = Fp2::new(
            Fp::from_u64s_le(&[
                0x2d0078036923ffc7,
                0x11e59ea221a3b6d2,
                0x8b1a52e0a90f59ed,
                0xb966ce3bc2108b13,
                0xccc649c4b9532bf3,
                0xf8d295b2ded9dc,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x977df6efcdaee0db,
                0x946ae52d684fa7ed,
                0xbe203411c66fb3a5,
                0xb3f8afc0ee248cad,
                0x4e464dea5bcfd41e,
                0x12d1137b8a6a837,
            ])
            .unwrap(),
        );
        a -= &Fp2::new(
            Fp::from_u64s_le(&[
                0x619a02d78dc70ef2,
                0xb93adfc9119e33e8,
                0x4bf0b99a9f0dca12,
                0x3b88899a42a6318f,
                0x986a4a62fa82a49d,
                0x13ce433fa26027f5,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x66323bf80b58b9b9,
                0xa1379b6facf6e596,
                0x402aef1fb797e32f,
                0x2236f55246d0d44d,
                0x4c8c1800eb104566,
                0x11d6e20e986c2085,
            ])
            .unwrap(),
        );
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x8565752bdb5c9b80,
                    0x7756bed7c15982e9,
                    0xa65a6be700b285fe,
                    0xe255902672ef6c43,
                    0x7f77a718021c342d,
                    0x72ba14049fe9881
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xeb4abaf7c255d1cd,
                    0x11df49bc6cacc256,
                    0xe52617930588c69a,
                    0xf63905f39ad8cb1f,
                    0x4cd5dd9fb40b3b8f,
                    0x957411359ba6e4c
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_negaton() {
        let a = Fp2::new(
            Fp::from_u64s_le(&[
                0x2d0078036923ffc7,
                0x11e59ea221a3b6d2,
                0x8b1a52e0a90f59ed,
                0xb966ce3bc2108b13,
                0xccc649c4b9532bf3,
                0xf8d295b2ded9dc,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x977df6efcdaee0db,
                0x946ae52d684fa7ed,
                0xbe203411c66fb3a5,
                0xb3f8afc0ee248cad,
                0x4e464dea5bcfd41e,
                0x12d1137b8a6a837,
            ])
            .unwrap(),
        );
        assert_eq!(
            -a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x8cfe87fc96dbaae4,
                    0xcc6615c8fb0492d,
                    0xdc167fc04da19c37,
                    0xab107d49317487ab,
                    0x7e555df189f880e3,
                    0x19083f5486a10cbd
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x228109103250c9d0,
                    0x8a411ad149045812,
                    0xa9109e8f3041427e,
                    0xb07e9bc405608611,
                    0xfcd559cbe77bd8b8,
                    0x18d400b280d93e62
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_doubling() {
        let a = Fp2::new(
            Fp::from_u64s_le(&[
                0x2d0078036923ffc7,
                0x11e59ea221a3b6d2,
                0x8b1a52e0a90f59ed,
                0xb966ce3bc2108b13,
                0xccc649c4b9532bf3,
                0xf8d295b2ded9dc,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x977df6efcdaee0db,
                0x946ae52d684fa7ed,
                0xbe203411c66fb3a5,
                0xb3f8afc0ee248cad,
                0x4e464dea5bcfd41e,
                0x12d1137b8a6a837,
            ])
            .unwrap(),
        );
        assert_eq!(
            a.double(),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x5a00f006d247ff8e,
                    0x23cb3d4443476da4,
                    0x1634a5c1521eb3da,
                    0x72cd9c7784211627,
                    0x998c938972a657e7,
                    0x1f1a52b65bdb3b9
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x2efbeddf9b5dc1b6,
                    0x28d5ca5ad09f4fdb,
                    0x7c4068238cdf674b,
                    0x67f15f81dc49195b,
                    0x9c8c9bd4b79fa83d,
                    0x25a226f714d506e
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_frobenius_map() {
        let mut a = Fp2::new(
            Fp::from_u64s_le(&[
                0x2d0078036923ffc7,
                0x11e59ea221a3b6d2,
                0x8b1a52e0a90f59ed,
                0xb966ce3bc2108b13,
                0xccc649c4b9532bf3,
                0xf8d295b2ded9dc,
            ])
            .unwrap(),
            Fp::from_u64s_le(&[
                0x977df6efcdaee0db,
                0x946ae52d684fa7ed,
                0xbe203411c66fb3a5,
                0xb3f8afc0ee248cad,
                0x4e464dea5bcfd41e,
                0x12d1137b8a6a837,
            ])
            .unwrap(),
        );
        a.frobenius_map(0);
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x2d0078036923ffc7,
                    0x11e59ea221a3b6d2,
                    0x8b1a52e0a90f59ed,
                    0xb966ce3bc2108b13,
                    0xccc649c4b9532bf3,
                    0xf8d295b2ded9dc
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x977df6efcdaee0db,
                    0x946ae52d684fa7ed,
                    0xbe203411c66fb3a5,
                    0xb3f8afc0ee248cad,
                    0x4e464dea5bcfd41e,
                    0x12d1137b8a6a837
                ])
                .unwrap(),
            )
        );
        a.frobenius_map(1);
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x2d0078036923ffc7,
                    0x11e59ea221a3b6d2,
                    0x8b1a52e0a90f59ed,
                    0xb966ce3bc2108b13,
                    0xccc649c4b9532bf3,
                    0xf8d295b2ded9dc
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x228109103250c9d0,
                    0x8a411ad149045812,
                    0xa9109e8f3041427e,
                    0xb07e9bc405608611,
                    0xfcd559cbe77bd8b8,
                    0x18d400b280d93e62
                ])
                .unwrap(),
            )
        );
        a.frobenius_map(1);
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x2d0078036923ffc7,
                    0x11e59ea221a3b6d2,
                    0x8b1a52e0a90f59ed,
                    0xb966ce3bc2108b13,
                    0xccc649c4b9532bf3,
                    0xf8d295b2ded9dc
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x977df6efcdaee0db,
                    0x946ae52d684fa7ed,
                    0xbe203411c66fb3a5,
                    0xb3f8afc0ee248cad,
                    0x4e464dea5bcfd41e,
                    0x12d1137b8a6a837
                ])
                .unwrap(),
            )
        );
        a.frobenius_map(2);
        assert_eq!(
            a,
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x2d0078036923ffc7,
                    0x11e59ea221a3b6d2,
                    0x8b1a52e0a90f59ed,
                    0xb966ce3bc2108b13,
                    0xccc649c4b9532bf3,
                    0xf8d295b2ded9dc
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x977df6efcdaee0db,
                    0x946ae52d684fa7ed,
                    0xbe203411c66fb3a5,
                    0xb3f8afc0ee248cad,
                    0x4e464dea5bcfd41e,
                    0x12d1137b8a6a837
                ])
                .unwrap(),
            )
        );
    }

    #[test]
    fn test_fp2_sqrt_2() {
        // a = 1488924004771393321054797166853618474668089414631333405711627789629391903630694737978065425271543178763948256226639*u + 784063022264861764559335808165825052288770346101304131934508881646553551234697082295473567906267937225174620141295
        let a = Fp2::new(
            Fp::from_mont_unchecked([
                0x2bee_d146_27d7_f9e9,
                0xb661_4e06_660e_5dce,
                0x06c4_cc7c_2f91_d42c,
                0x996d_7847_4b7a_63cc,
                0xebae_bc4c_820d_574e,
                0x1886_5e12_d93f_d845,
            ]),
            Fp::from_mont_unchecked([
                0x7d82_8664_baf4_f566,
                0xd17e_6639_96ec_7339,
                0x679e_ad55_cb40_78d0,
                0xfe3b_2260_e001_ec28,
                0x3059_93d0_43d9_1b68,
                0x0626_f03c_0489_b72d,
            ]),
        );

        assert_eq!(a.sqrt().unwrap().square(), a);

        // b = 5, which is a generator of the p - 1 order
        // multiplicative subgroup
        let b = Fp2::new(
            Fp::from_mont_unchecked([
                0x6631_0000_0010_5545,
                0x2114_0040_0eec_000d,
                0x3fa7_af30_c820_e316,
                0xc52a_8b8d_6387_695d,
                0x9fb4_e61d_1e83_eac5,
                0x005c_b922_afe8_4dc7,
            ]),
            Fp::ZERO,
        );

        assert_eq!(b.sqrt().unwrap().square(), b);

        // c = 25, which is a generator of the (p - 1) / 2 order
        // multiplicative subgroup
        let c = Fp2::new(
            Fp::from_mont_unchecked([
                0x44f6_0000_0051_ffae,
                0x86b8_0141_9948_0043,
                0xd715_9952_f1f3_794a,
                0x755d_6e3d_fe1f_fc12,
                0xd36c_d6db_5547_e905,
                0x02f8_c8ec_bf18_67bb,
            ]),
            Fp::ZERO,
        );

        assert_eq!(c.sqrt().unwrap().square(), c);

        // 2155129644831861015726826462986972654175647013268275306775721078997042729172900466542651176384766902407257452753362*u + 2796889544896299244102912275102369318775038861758288697415827248356648685135290329705805931514906495247464901062529
        // is nonsquare.
        assert!(bool::from(
            Fp2::new(
                Fp::from_mont_unchecked([
                    0xc5fa_1bc8_fd00_d7f6,
                    0x3830_ca45_4606_003b,
                    0x2b28_7f11_04b1_02da,
                    0xa7fb_30f2_8230_f23e,
                    0x339c_db9e_e953_dbf0,
                    0x0d78_ec51_d989_fc57,
                ]),
                Fp::from_mont_unchecked([
                    0x27ec_4898_cf87_f613,
                    0x9de1_394e_1abb_05a5,
                    0x0947_f85d_c170_fc14,
                    0x586f_bc69_6b61_14b7,
                    0x2b34_75a4_077d_7169,
                    0x13e1_c895_cc4b_6c22,
                ])
            )
            .sqrt()
            .is_none()
        ));
    }

    #[test]
    fn test_fp2_sqrt() {
        assert_eq!(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x476b4c309720e227,
                    0x34c2d04faffdab6,
                    0xa57e6fc1bab51fd9,
                    0xdb4a116b5bf74aa1,
                    0x1e58b2159dfe10e2,
                    0x7ca7da1f13606ac
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xfa8de88b7516d2c3,
                    0x371a75ed14f41629,
                    0x4cec2dca577a3eb6,
                    0x212611bca4e99121,
                    0x8ee5394d77afb3d,
                    0xec92336650e49d5
                ])
                .unwrap()
            )
            .sqrt()
            .unwrap(),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x40b299b2704258c5,
                    0x6ef7de92e8c68b63,
                    0x6d2ddbe552203e82,
                    0x8d7f1f723d02c1d3,
                    0x881b3e01b611c070,
                    0x10f6963bbad2ebc5
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xc099534fc209e752,
                    0x7670594665676447,
                    0x28a20faed211efe7,
                    0x6b852aeaf2afcb1b,
                    0xa4c93b08105d71a9,
                    0x8d7cfff94216330
                ])
                .unwrap()
            )
            .neg()
        );

        assert_eq!(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xb9f78429d1517a6b,
                    0x1eabfffeb153ffff,
                    0x6730d2a0f6b0f624,
                    0x64774b84f38512bf,
                    0x4b1ba7b6434bacd7,
                    0x1a0111ea397fe69a
                ])
                .unwrap(),
                Fp::ZERO,
            )
            .sqrt()
            .unwrap(),
            Fp2::new(
                Fp::ZERO,
                Fp::from_u64s_le(&[
                    0xb9fefffffd4357a3,
                    0x1eabfffeb153ffff,
                    0x6730d2a0f6b0f624,
                    0x64774b84f38512bf,
                    0x4b1ba7b6434bacd7,
                    0x1a0111ea397fe69a
                ])
                .unwrap()
            )
        );
    }

    #[test]
    fn test_fp2_legendre() {
        assert_eq!(Fp2::ZERO.sqrt().unwrap(), Fp2::ZERO);
        // i^2 = -1
        let mut a = -Fp2::ONE;
        assert!(a.is_quad_res());
        a.mul_by_nonresidue();
        assert!(!a.is_quad_res());
    }

    #[test]
    fn test_fp2_mul_nonresidue() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let nqr = Fp2::new(Fp::ONE, Fp::ONE);

        for _ in 0..1000 {
            let mut a = Fp2::random(&mut rng);
            let mut b = a;
            a.mul_by_nonresidue();
            b *= &nqr;

            assert_eq!(a, b);
        }
    }

    #[test]
    fn fp2_field_tests() {
        crate::tests::field::random_field_tests::<Fp2>();
        crate::tests::field::random_sqrt_tests::<Fp2>();
    }

    #[test]
    fn test_fp2_frobenius() {
        use std::convert::TryFrom;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let characteristic: Vec<u64> = Fp::char()
            .chunks(8)
            .map(|chunk| u64::from_le_bytes(<[u8; 8]>::try_from(chunk).unwrap()))
            .collect();

        let maxpower = 13;

        for _ in 0..100 {
            for i in 0..(maxpower + 1) {
                let mut a = Fp2::random(&mut rng);
                let mut b = a;

                for _ in 0..i {
                    a = a.pow_vartime(&characteristic);
                }
                b.frobenius_map(i);

                assert_eq!(a, b);
            }
        }
    }
}

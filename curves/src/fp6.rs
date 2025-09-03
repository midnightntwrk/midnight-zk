//! This module implements arithmetic over the quadratic extension field Fp6.

use core::{
    fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use blst::*;
use ff::Field;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{
    fp::{Fp, FROBENIUS_COEFF_FP6_C1, FROBENIUS_COEFF_FP6_C2},
    fp2::Fp2,
};

/// This represents an element $c_0 + c_1 v + c_2 v^2$ of $\mathbb{F}_{p^6} =
/// \mathbb{F}_{p^2} / v^3 - u - 1$.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Fp6(pub(crate) blst_fp6);

impl fmt::Debug for Fp6 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Fp6")
            .field("c0", &self.c0())
            .field("c1", &self.c1())
            .field("c2", &self.c2())
            .finish()
    }
}

impl fmt::Display for Fp6 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Fp6({:?} + ({:?}) * v, ({:?}) * v^2)",
            self.c0(),
            self.c1(),
            self.c2()
        )
    }
}

impl core::hash::Hash for Fp6 {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        for i in 0..3 {
            for j in 0..2 {
                self.0.fp2[i].fp[j].l.hash::<H>(state);
            }
        }
    }
}

impl From<Fp> for Fp6 {
    fn from(f: Fp) -> Fp6 {
        Fp6::new(Fp2::from(f), Fp2::ZERO, Fp2::ZERO)
    }
}

impl From<Fp2> for Fp6 {
    fn from(f: Fp2) -> Fp6 {
        Fp6::new(f, Fp2::ZERO, Fp2::ZERO)
    }
}

impl From<blst_fp6> for Fp6 {
    fn from(val: blst_fp6) -> Fp6 {
        Fp6(val)
    }
}

impl From<Fp6> for blst_fp6 {
    fn from(val: Fp6) -> blst_fp6 {
        val.0
    }
}

impl From<u64> for Fp6 {
    fn from(val: u64) -> Fp6 {
        Fp6::from(Fp2::from(val))
    }
}

impl Default for Fp6 {
    fn default() -> Self {
        Fp6::ZERO
    }
}

impl Eq for Fp6 {}

impl PartialEq for Fp6 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.fp2[0].fp[0].l == other.0.fp2[0].fp[0].l
            && self.0.fp2[0].fp[1].l == other.0.fp2[0].fp[1].l
            && self.0.fp2[1].fp[0].l == other.0.fp2[1].fp[0].l
            && self.0.fp2[1].fp[1].l == other.0.fp2[1].fp[1].l
            && self.0.fp2[2].fp[0].l == other.0.fp2[2].fp[0].l
            && self.0.fp2[2].fp[1].l == other.0.fp2[2].fp[1].l
    }
}

impl ConstantTimeEq for Fp6 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0().ct_eq(&other.c0()) & self.c1().ct_eq(&other.c1()) & self.c2().ct_eq(&other.c2())
    }
}

impl ConditionallySelectable for Fp6 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp6(blst_fp6 {
            fp2: [
                Fp2::conditional_select(&a.c0(), &b.c0(), choice).0,
                Fp2::conditional_select(&a.c1(), &b.c1(), choice).0,
                Fp2::conditional_select(&a.c2(), &b.c2(), choice).0,
            ],
        })
    }
}

macro_rules! op {
    ($lhs:expr, $op:expr, $rhs:expr) => {
        unsafe {
            $op(&mut $lhs.0.fp2[0], &$lhs.0.fp2[0], &$rhs.0.fp2[0]);
            $op(&mut $lhs.0.fp2[1], &$lhs.0.fp2[1], &$rhs.0.fp2[1]);
            $op(&mut $lhs.0.fp2[2], &$lhs.0.fp2[2], &$rhs.0.fp2[2]);
        }
    };
}

impl Neg for &Fp6 {
    type Output = Fp6;

    #[inline]
    fn neg(self) -> Fp6 {
        -*self
    }
}

impl Neg for Fp6 {
    type Output = Fp6;

    #[inline]
    fn neg(mut self) -> Fp6 {
        unsafe {
            blst_fp2_cneg(&mut self.0.fp2[0], &self.0.fp2[0], true);
            blst_fp2_cneg(&mut self.0.fp2[1], &self.0.fp2[1], true);
            blst_fp2_cneg(&mut self.0.fp2[2], &self.0.fp2[2], true);
        }
        self
    }
}

impl Sub<&Fp6> for &Fp6 {
    type Output = Fp6;

    #[inline]
    fn sub(self, rhs: &Fp6) -> Fp6 {
        let mut out = *self;
        out -= rhs;
        out
    }
}

impl Add<&Fp6> for &Fp6 {
    type Output = Fp6;

    #[inline]
    fn add(self, rhs: &Fp6) -> Fp6 {
        let mut out = *self;
        out += rhs;
        out
    }
}

impl Mul<&Fp6> for &Fp6 {
    type Output = Fp6;

    #[inline]
    fn mul(self, rhs: &Fp6) -> Fp6 {
        let mut out = *self;
        out *= rhs;
        out
    }
}

impl AddAssign<&Fp6> for Fp6 {
    #[inline]
    fn add_assign(&mut self, rhs: &Fp6) {
        op!(self, blst_fp2_add, rhs);
    }
}

impl SubAssign<&Fp6> for Fp6 {
    #[inline]
    fn sub_assign(&mut self, rhs: &Fp6) {
        op!(self, blst_fp2_sub, rhs);
    }
}

impl MulAssign<&Fp6> for Fp6 {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fp6) {
        let mut a_a = self.c0();
        let mut b_b = self.c1();
        let mut c_c = self.c2();
        a_a *= &rhs.c0();
        b_b *= &rhs.c1();
        c_c *= &rhs.c2();

        let mut t1 = rhs.c1();
        t1 += &rhs.c2();
        {
            let mut tmp = self.c1();
            tmp += &self.c2();

            t1 *= &tmp;
            t1 -= &b_b;
            t1 -= &c_c;
            t1.mul_by_nonresidue();
            t1 += &a_a;
        }

        let mut t3 = rhs.c0();
        t3 += &rhs.c2();
        {
            let mut tmp = self.c0();
            tmp += &self.c2();

            t3 *= &tmp;
            t3 -= &a_a;
            t3 += &b_b;
            t3 -= &c_c;
        }

        let mut t2 = rhs.c0();
        t2 += &rhs.c1();
        {
            let mut tmp = self.c0();
            tmp += &self.c1();

            t2 *= &tmp;
            t2 -= &a_a;
            t2 -= &b_b;
            c_c.mul_by_nonresidue();
            t2 += &c_c;
        }

        self.0.fp2[0] = t1.0;
        self.0.fp2[1] = t2.0;
        self.0.fp2[2] = t3.0;
    }
}

impl_add_sub!(Fp6);
impl_add_sub_assign!(Fp6);
impl_mul!(Fp6);
impl_mul_assign!(Fp6);
impl_sum!(Fp6);
impl_product!(Fp6);

impl Field for Fp6 {
    fn random(mut rng: impl RngCore) -> Self {
        Fp6::new(
            Fp2::random(&mut rng),
            Fp2::random(&mut rng),
            Fp2::random(&mut rng),
        )
    }

    const ZERO: Self = Fp6::new(Fp2::ZERO, Fp2::ZERO, Fp2::ZERO);

    const ONE: Self = Fp6::new(Fp2::ONE, Fp2::ZERO, Fp2::ZERO);

    fn is_zero(&self) -> Choice {
        self.c0().is_zero() & self.c1().is_zero() & self.c2().is_zero()
    }

    fn double(&self) -> Self {
        let mut out = *self;
        out += self;
        out
    }

    fn square(&self) -> Self {
        let mut s0 = self.c0();
        s0 = s0.square();
        let mut ab = self.c0();
        ab *= &self.c1();
        let mut s1 = ab;
        s1 = s1.double();
        let mut s2 = self.c0();
        s2 -= &self.c1();
        s2 += &self.c2();
        s2 = s2.square();
        let mut bc = self.c1();
        bc *= &self.c2();
        let mut s3 = bc;
        s3 = s3.double();
        let mut s4 = self.c2();
        s4 = s4.square();

        let mut c0 = s3;
        c0.mul_by_nonresidue();
        c0 += &s0;

        let mut c1 = s4;
        c1.mul_by_nonresidue();
        c1 += &s1;

        let mut c2 = s1;
        c2 += &s2;
        c2 += &s3;
        c2 -= &s0;
        c2 -= &s4;

        Fp6::new(c0, c1, c2)
    }

    fn invert(&self) -> CtOption<Self> {
        let mut c0 = self.c2();
        c0.mul_by_nonresidue();
        c0 *= &self.c1();
        c0 = -c0;
        {
            let mut c0s = self.c0();
            c0s = c0s.square();
            c0 += &c0s;
        }
        let mut c1 = self.c2();
        c1 = c1.square();
        c1.mul_by_nonresidue();
        {
            let mut c01 = self.c0();
            c01 *= &self.c1();
            c1 -= &c01;
        }
        let mut c2 = self.c1();
        c2 = c2.square();
        {
            let mut c02 = self.c0();
            c02 *= &self.c2();
            c2 -= &c02;
        }
        let mut tmp1 = self.c2();
        tmp1 *= &c1;
        let mut tmp2 = self.c1();
        tmp2 *= &c2;
        tmp1 += &tmp2;
        tmp1.mul_by_nonresidue();
        tmp2 = self.c0();
        tmp2 *= &c0;
        tmp1 += &tmp2;
        tmp1.invert().map(|t| Fp6::new(t * c0, t * c1, t * c2))
    }

    fn sqrt(&self) -> CtOption<Self> {
        unimplemented!()
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        // ff::helpers::sqrt_ratio_generic(num, div)
        unimplemented!()
    }
}

impl Fp6 {
    /// Constructs an element of `Fp6`.
    pub const fn new(c0: Fp2, c1: Fp2, c2: Fp2) -> Fp6 {
        Fp6(blst_fp6 {
            fp2: [c0.0, c1.0, c2.0],
        })
    }

    pub fn c0(&self) -> Fp2 {
        Fp2(self.0.fp2[0])
    }

    pub fn c1(&self) -> Fp2 {
        Fp2(self.0.fp2[1])
    }

    pub fn c2(&self) -> Fp2 {
        Fp2(self.0.fp2[2])
    }

    /// Multiply by quadratic nonresidue v.
    pub fn mul_by_nonresidue(&mut self) {
        self.0.fp2.swap(0, 1);
        self.0.fp2.swap(0, 2);

        let mut c0 = self.c0();
        c0.mul_by_nonresidue();
        self.0.fp2[0] = c0.0;
    }

    pub fn frobenius_map(&mut self, power: usize) {
        let mut c0 = self.c0();
        c0.frobenius_map(power);
        let mut c1 = self.c1();
        c1.frobenius_map(power);
        let mut c2 = self.c2();
        c2.frobenius_map(power);

        c1 *= &FROBENIUS_COEFF_FP6_C1[power % 6];
        c2 *= &FROBENIUS_COEFF_FP6_C2[power % 6];

        self.0.fp2[0] = c0.0;
        self.0.fp2[1] = c1.0;
        self.0.fp2[2] = c2.0;
    }
}

#[cfg(test)]
mod tests {
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    #[test]
    fn test_fp6_mul_nonresidue() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let nqr = Fp6::new(Fp2::ZERO, Fp2::ONE, Fp2::ZERO);

        for _ in 0..1000 {
            let mut a = Fp6::random(&mut rng);
            let mut b = a;
            a.mul_by_nonresidue();
            b.mul_assign(&nqr);

            assert_eq!(a, b);
        }
    }

    #[test]
    fn fp6_random_field_tests() {
        crate::tests::field::random_field_tests::<Fp6>();
    }

    #[test]
    fn test_fp6_frobenius_map() {
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
                let mut a = Fp6::random(&mut rng);
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

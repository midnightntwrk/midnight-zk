use core::convert::TryInto;
use std::cmp::Ordering;

use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use subtle::{Choice, CtOption};

use super::{
    ext_field::quadratic::{QuadExtField, QuadExtFieldArith, SQRT},
    fq::Fq,
    ExtField,
};
use crate::ff_ext::Legendre;

crate::impl_binops_additive!(Fq2, Fq2);
crate::impl_binops_multiplicative!(Fq2, Fq2);
crate::impl_binops_calls!(Fq2);
crate::impl_sum_prod!(Fq2);

pub type Fq2 = QuadExtField<Fq>;

impl Fq2 {
    pub const SIZE: usize = Fq::SIZE * 2;
}

impl Ord for Fq2 {
    #[inline(always)]
    fn cmp(&self, other: &Fq2) -> Ordering {
        match self.c1.cmp(&other.c1) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.c0.cmp(&other.c0),
        }
    }
}

impl PartialOrd for Fq2 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq2) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<u64> for Fq2 {
    fn from(val: u64) -> Self {
        Fq2 {
            c0: Fq::from(val),
            c1: Fq::ZERO,
        }
    }
}

impl Fq2 {
    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Fq`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; Fq::SIZE * 2]) -> CtOption<Fq2> {
        let (c0, c1) = bytes.split_at(Fq::SIZE);
        let c0 = Fq::from_bytes(c0.try_into().unwrap());
        let c1 = Fq::from_bytes(c1.try_into().unwrap());

        c0.and_then(|c0| c1.map(|c1| Fq2::new(c0, c1)))
    }

    /// Converts an element of `Fq` into a byte representation in
    /// little-endian byte order.
    #[allow(clippy::wrong_self_convention)]
    pub fn to_bytes(&self) -> [u8; Fq::SIZE * 2] {
        let mut res = [0u8; Fq::SIZE * 2];
        let (c0, c1) = res.split_at_mut(Fq::SIZE);
        c0.copy_from_slice(&self.c0.to_bytes());
        c1.copy_from_slice(&self.c1.to_bytes());
        res
    }

    #[inline]
    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    pub fn lexicographically_largest(&self) -> Choice {
        // If this element's c1 coefficient is lexicographically largest
        // then it is lexicographically largest. Otherwise, in the event
        // the c1 coefficient is zero and the c0 coefficient is
        // lexicographically largest, then this element is lexicographically
        // largest.
        self.c1.lexicographically_largest()
            | (self.c1.is_zero() & self.c0.lexicographically_largest())
    }
}

impl WithSmallOrderMulGroup<3> for Fq2 {
    const ZETA: Self = Fq2 {
        c0: Fq::ZETA.mul_const(&Fq::ZETA),
        c1: Fq::ZERO,
    };
}

impl Legendre for Fq2 {
    fn legendre(&self) -> i64 {
        self.norm().legendre()
    }
}

impl PrimeField for Fq2 {
    type Repr = crate::serde::Repr<{ Fq::SIZE * 2 }>;

    const MODULUS: &'static str = <Fq as PrimeField>::MODULUS;
    const MULTIPLICATIVE_GENERATOR: Self = Fq2 {
        c0: Fq::MULTIPLICATIVE_GENERATOR,
        c1: Fq::ZERO,
    };
    const NUM_BITS: u32 = Fq::NUM_BITS;
    const CAPACITY: u32 = Fq::NUM_BITS;
    const S: u32 = Fq::S;

    // TODO: Check that we can just 0 this and forget.
    const ROOT_OF_UNITY: Self = Fq2::ZERO;
    const ROOT_OF_UNITY_INV: Self = Fq2::ZERO;
    const DELTA: Self = Fq2::ZERO;

    const TWO_INV: Self = Fq2 {
        c0: Fq::TWO_INV,
        c1: Fq::ZERO,
    };

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        Self::from_bytes(&repr.into())
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_bytes().into()
    }

    fn is_odd(&self) -> Choice {
        // The little-endian representation places `c0` first, so the parity of
        // the whole element is the parity of `c0`.
        self.c0.is_odd()
    }
}

impl crate::serde::SerdeObject for Fq2 {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), Fq::SIZE * 2);
        let (c0, c1) = bytes.split_at(Fq::SIZE);
        Self {
            c0: Fq::from_raw_bytes_unchecked(c0),
            c1: Fq::from_raw_bytes_unchecked(c1),
        }
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != Fq::SIZE * 2 {
            return None;
        }
        let (c0, c1) = bytes.split_at(Fq::SIZE);
        let c0 = Fq::from_raw_bytes(c0)?;
        let c1 = Fq::from_raw_bytes(c1)?;
        Some(Self { c0, c1 })
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(Fq::SIZE * 2);
        for limb in self.c0.0.iter().chain(self.c1.0.iter()) {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let [c0, c1] = [(); 2].map(|_| Fq::read_raw_unchecked(reader));
        Self { c0, c1 }
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let c0 = Fq::read_raw(reader)?;
        let c1 = Fq::read_raw(reader)?;
        Ok(Self { c0, c1 })
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        self.c0.write_raw(writer)?;
        self.c1.write_raw(writer)
    }
}

impl FromUniformBytes<96> for Fq2 {
    fn from_uniform_bytes(bytes: &[u8; 96]) -> Self {
        const SIZE: usize = 96 / 2;
        let c0: [u8; SIZE] = bytes[SIZE..].try_into().unwrap();
        let c1: [u8; SIZE] = bytes[..SIZE].try_into().unwrap();
        Self::new(Fq::from_uniform_bytes(&c0), Fq::from_uniform_bytes(&c1))
    }
}
impl QuadExtFieldArith for Fq2 {
    type Base = Fq;
    const SQRT: SQRT<Fq> = SQRT::Algorithm9 {
        q_minus_3_over_4: &[
            0x4f082305b61f3f51,
            0x65e05aa45a1c72a3,
            0x6e14116da0605617,
            0x0c19139cb84c680a,
        ],
        q_minus_1_over_2: &[
            0x9e10460b6c3e7ea3,
            0xcbc0b548b438e546,
            0xdc2822db40c0ac2e,
            0x183227397098d014,
        ],
    };

    fn square_assign(el: &mut QuadExtField<Self::Base>) {
        let a = el.c0 + el.c1;
        let b = el.c0 - el.c1;
        let c = el.c0.double();
        el.c0 = a * b;
        el.c1 = c * el.c1;
    }
}

impl ExtField for Fq2 {
    const NON_RESIDUE: Self = Fq2::new(Fq::from_raw([9u64, 0, 0, 0]), Fq::ONE);

    fn mul_by_nonresidue(&self) -> Self {
        // (xu+y)(u+9) = (9x+y)u+(9y-x)
        let t0 = self.c0;
        let t1 = self.c1;
        // 8*x*i + 8*y
        let t = self.double().double().double();
        Self {
            // 9*y
            c0: t.c0 + t0 - t1,
            // (9*x + y)
            c1: t.c1 + t0 + t1,
        }
    }

    fn frobenius_map(&mut self, power: usize) {
        if !power.is_multiple_of(2) {
            self.conjugate();
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;
    crate::field_testing_suite!(Fq2, "field_arithmetic");
    crate::field_testing_suite!(Fq2, "conversion");
    crate::field_testing_suite!(Fq2, "serdeobject");
    crate::field_testing_suite!(Fq2, "quadratic_residue");
    crate::field_testing_suite!(Fq2, "sqrt");
    crate::field_testing_suite!(Fq2, "zeta", Fq);
    // extension field-specific
    crate::field_testing_suite!(Fq2, "f2_tests", Fq);
    crate::field_testing_suite!(
        Fq2,
        "frobenius",
        // Frobenius endomorphism power parameter for extension field
        //  ϕ: E → E
        //  (x, y) ↦ (x^p, y^p)
        // p: modulus of base field (Here, Fq::MODULUS)
        Fq::MODULUS_LIMBS
    );

    #[test]
    fn test_fq2_mul_nonresidue() {
        let e = Fq2::random(rand_core::OsRng);
        let a0 = e.mul_by_nonresidue();
        let a1 = e * Fq2::NON_RESIDUE;
        assert_eq!(a0, a1);
    }
}

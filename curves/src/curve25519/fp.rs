use core::convert::TryInto;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

impl Fp {
    #[inline(always)]
    pub const fn add(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, sbb};
        let (d_0, carry) = adc(self.0[0usize], rhs.0[0usize], 0);
        let (d_1, carry) = adc(self.0[1usize], rhs.0[1usize], carry);
        let (d_2, carry) = adc(self.0[2usize], rhs.0[2usize], carry);
        let (d_3, carry) = adc(self.0[3usize], rhs.0[3usize], carry);
        let (d_0, borrow) = sbb(d_0, Self::MODULUS_LIMBS[0usize], 0);
        let (d_1, borrow) = sbb(d_1, Self::MODULUS_LIMBS[1usize], borrow);
        let (d_2, borrow) = sbb(d_2, Self::MODULUS_LIMBS[2usize], borrow);
        let (d_3, borrow) = sbb(d_3, Self::MODULUS_LIMBS[3usize], borrow);
        let (_, borrow) = sbb(carry, 0, borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0usize] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1usize] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2usize] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3usize] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline]
    pub const fn double(&self) -> Self {
        self.add(self)
    }
    #[inline(always)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, sbb};
        let (d_0, borrow) = sbb(self.0[0usize], rhs.0[0usize], 0);
        let (d_1, borrow) = sbb(self.0[1usize], rhs.0[1usize], borrow);
        let (d_2, borrow) = sbb(self.0[2usize], rhs.0[2usize], borrow);
        let (d_3, borrow) = sbb(self.0[3usize], rhs.0[3usize], borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0usize] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1usize] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2usize] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3usize] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline(always)]
    pub const fn neg(&self) -> Self {
        use crate::arithmetic::{adc, sbb};
        let (d_0, borrow) = sbb(Self::MODULUS_LIMBS[0usize], self.0[0usize], 0);
        let (d_1, borrow) = sbb(Self::MODULUS_LIMBS[1usize], self.0[1usize], borrow);
        let (d_2, borrow) = sbb(Self::MODULUS_LIMBS[2usize], self.0[2usize], borrow);
        let (d_3, _) = sbb(Self::MODULUS_LIMBS[3usize], self.0[3usize], borrow);
        let mask = (((self.0[0usize] | self.0[1usize] | self.0[2usize] | self.0[3usize]) == 0)
            as u64)
            .wrapping_sub(1);
        Fp([d_0 & mask, d_1 & mask, d_2 & mask, d_3 & mask])
    }
    #[inline(always)]
    pub const fn mul(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, mac, sbb};
        let (r_0, carry) = mac(0, self.0[0usize], rhs.0[0usize], 0);
        let (r_1, carry) = mac(0, self.0[0usize], rhs.0[1usize], carry);
        let (r_2, carry) = mac(0, self.0[0usize], rhs.0[2usize], carry);
        let (r_3, r_4) = mac(0, self.0[0usize], rhs.0[3usize], carry);
        let (r_1, carry) = mac(r_1, self.0[1usize], rhs.0[0usize], 0);
        let (r_2, carry) = mac(r_2, self.0[1usize], rhs.0[1usize], carry);
        let (r_3, carry) = mac(r_3, self.0[1usize], rhs.0[2usize], carry);
        let (r_4, r_5) = mac(r_4, self.0[1usize], rhs.0[3usize], carry);
        let (r_2, carry) = mac(r_2, self.0[2usize], rhs.0[0usize], 0);
        let (r_3, carry) = mac(r_3, self.0[2usize], rhs.0[1usize], carry);
        let (r_4, carry) = mac(r_4, self.0[2usize], rhs.0[2usize], carry);
        let (r_5, r_6) = mac(r_5, self.0[2usize], rhs.0[3usize], carry);
        let (r_3, carry) = mac(r_3, self.0[3usize], rhs.0[0usize], 0);
        let (r_4, carry) = mac(r_4, self.0[3usize], rhs.0[1usize], carry);
        let (r_5, carry) = mac(r_5, self.0[3usize], rhs.0[2usize], carry);
        let (r_6, r_7) = mac(r_6, self.0[3usize], rhs.0[3usize], carry);
        Fp::montgomery_reduce(&[r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7])
    }
    #[inline(always)]
    pub const fn square(&self) -> Self {
        use crate::arithmetic::{adc, mac, sbb};
        let (r_1, carry) = mac(0, self.0[0usize], self.0[1usize], 0);
        let (r_2, carry) = mac(0, self.0[0usize], self.0[2usize], carry);
        let (r_3, r_4) = mac(0, self.0[0usize], self.0[3usize], carry);
        let (r_3, carry) = mac(r_3, self.0[1usize], self.0[2usize], 0);
        let (r_4, r_5) = mac(r_4, self.0[1usize], self.0[3usize], carry);
        let (r_5, r_6) = mac(r_5, self.0[2usize], self.0[3usize], 0);
        let r_7 = r_6 >> 63;
        let r_6 = (r_6 << 1) | (r_5 >> 63);
        let r_5 = (r_5 << 1) | (r_4 >> 63);
        let r_4 = (r_4 << 1) | (r_3 >> 63);
        let r_3 = (r_3 << 1) | (r_2 >> 63);
        let r_2 = (r_2 << 1) | (r_1 >> 63);
        let r_1 = (r_1 << 1);
        let (r_0, carry) = mac(0, self.0[0usize], self.0[0usize], 0);
        let (r_1, carry) = adc(0, r_1, carry);
        let (r_2, carry) = mac(r_2, self.0[1usize], self.0[1usize], carry);
        let (r_3, carry) = adc(0, r_3, carry);
        let (r_4, carry) = mac(r_4, self.0[2usize], self.0[2usize], carry);
        let (r_5, carry) = adc(0, r_5, carry);
        let (r_6, carry) = mac(r_6, self.0[3usize], self.0[3usize], carry);
        let (r_7, _) = adc(0, r_7, carry);
        Fp::montgomery_reduce(&[r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7])
    }
    #[inline(always)]
    pub(crate) const fn montgomery_reduce(r: &[u64; 8usize]) -> Self {
        use crate::arithmetic::{adc, mac, sbb};
        let k = r[0].wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r[0usize], k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_1, carry) = mac(r[1usize], k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_2, carry) = mac(r[2usize], k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_3, carry) = mac(r[3usize], k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_4, carry2) = adc(r[4usize], 0, carry);
        let k = r_1.wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r_1, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_2, carry) = mac(r_2, k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_3, carry) = mac(r_3, k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_5, carry2) = adc(r[5usize], carry2, carry);
        let k = r_2.wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r_2, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_3, carry) = mac(r_3, k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_5, carry) = mac(r_5, k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_6, carry2) = adc(r[6usize], carry2, carry);
        let k = r_3.wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r_3, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_5, carry) = mac(r_5, k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_6, carry) = mac(r_6, k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_7, carry2) = adc(r[7usize], carry2, carry);
        let (d_0, borrow) = sbb(r_4, Self::MODULUS_LIMBS[0usize], 0);
        let (d_1, borrow) = sbb(r_5, Self::MODULUS_LIMBS[1usize], borrow);
        let (d_2, borrow) = sbb(r_6, Self::MODULUS_LIMBS[2usize], borrow);
        let (d_3, borrow) = sbb(r_7, Self::MODULUS_LIMBS[3usize], borrow);
        let (_, borrow) = sbb(carry2, 0, borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0usize] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1usize] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2usize] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3usize] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline(always)]
    pub(crate) const fn from_mont(&self) -> [u64; 4usize] {
        use crate::arithmetic::{adc, mac, sbb};
        let k = self.0[0].wrapping_mul(9708812670373448219u64);
        let (_, r_0) = mac(self.0[0usize], k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_1, r_0) = mac(self.0[1usize], k, Self::MODULUS_LIMBS[1usize], r_0);
        let (r_2, r_0) = mac(self.0[2usize], k, Self::MODULUS_LIMBS[2usize], r_0);
        let (r_3, r_0) = mac(self.0[3usize], k, Self::MODULUS_LIMBS[3usize], r_0);
        let k = r_1.wrapping_mul(9708812670373448219u64);
        let (_, r_1) = mac(r_1, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_2, r_1) = mac(r_2, k, Self::MODULUS_LIMBS[1usize], r_1);
        let (r_3, r_1) = mac(r_3, k, Self::MODULUS_LIMBS[2usize], r_1);
        let (r_0, r_1) = mac(r_0, k, Self::MODULUS_LIMBS[3usize], r_1);
        let k = r_2.wrapping_mul(9708812670373448219u64);
        let (_, r_2) = mac(r_2, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_3, r_2) = mac(r_3, k, Self::MODULUS_LIMBS[1usize], r_2);
        let (r_0, r_2) = mac(r_0, k, Self::MODULUS_LIMBS[2usize], r_2);
        let (r_1, r_2) = mac(r_1, k, Self::MODULUS_LIMBS[3usize], r_2);
        let k = r_3.wrapping_mul(9708812670373448219u64);
        let (_, r_3) = mac(r_3, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_0, r_3) = mac(r_0, k, Self::MODULUS_LIMBS[1usize], r_3);
        let (r_1, r_3) = mac(r_1, k, Self::MODULUS_LIMBS[2usize], r_3);
        let (r_2, r_3) = mac(r_2, k, Self::MODULUS_LIMBS[3usize], r_3);
        Fp([r_0, r_1, r_2, r_3]).sub(&Fp(Self::MODULUS_LIMBS)).0
    }
}
impl Fp {
    #[inline(always)]
    pub(crate) const fn sub_const(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, sbb};
        let (d_0, borrow) = sbb(self.0[0usize], rhs.0[0usize], 0);
        let (d_1, borrow) = sbb(self.0[1usize], rhs.0[1usize], borrow);
        let (d_2, borrow) = sbb(self.0[2usize], rhs.0[2usize], borrow);
        let (d_3, borrow) = sbb(self.0[3usize], rhs.0[3usize], borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0usize] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1usize] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2usize] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3usize] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline(always)]
    pub(crate) const fn mul_const(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, mac, sbb};
        let (r_0, carry) = mac(0, self.0[0usize], rhs.0[0usize], 0);
        let (r_1, carry) = mac(0, self.0[0usize], rhs.0[1usize], carry);
        let (r_2, carry) = mac(0, self.0[0usize], rhs.0[2usize], carry);
        let (r_3, r_4) = mac(0, self.0[0usize], rhs.0[3usize], carry);
        let (r_1, carry) = mac(r_1, self.0[1usize], rhs.0[0usize], 0);
        let (r_2, carry) = mac(r_2, self.0[1usize], rhs.0[1usize], carry);
        let (r_3, carry) = mac(r_3, self.0[1usize], rhs.0[2usize], carry);
        let (r_4, r_5) = mac(r_4, self.0[1usize], rhs.0[3usize], carry);
        let (r_2, carry) = mac(r_2, self.0[2usize], rhs.0[0usize], 0);
        let (r_3, carry) = mac(r_3, self.0[2usize], rhs.0[1usize], carry);
        let (r_4, carry) = mac(r_4, self.0[2usize], rhs.0[2usize], carry);
        let (r_5, r_6) = mac(r_5, self.0[2usize], rhs.0[3usize], carry);
        let (r_3, carry) = mac(r_3, self.0[3usize], rhs.0[0usize], 0);
        let (r_4, carry) = mac(r_4, self.0[3usize], rhs.0[1usize], carry);
        let (r_5, carry) = mac(r_5, self.0[3usize], rhs.0[2usize], carry);
        let (r_6, r_7) = mac(r_6, self.0[3usize], rhs.0[3usize], carry);
        Fp::montgomery_reduce_const(&[r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7])
    }
    #[inline(always)]
    pub(crate) const fn montgomery_reduce_const(r: &[u64; 8usize]) -> Self {
        use crate::arithmetic::{adc, mac, sbb};
        let k = r[0].wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r[0usize], k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_1, carry) = mac(r[1usize], k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_2, carry) = mac(r[2usize], k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_3, carry) = mac(r[3usize], k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_4, carry2) = adc(r[4usize], 0, carry);
        let k = r_1.wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r_1, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_2, carry) = mac(r_2, k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_3, carry) = mac(r_3, k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_5, carry2) = adc(r[5usize], carry2, carry);
        let k = r_2.wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r_2, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_3, carry) = mac(r_3, k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_5, carry) = mac(r_5, k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_6, carry2) = adc(r[6usize], carry2, carry);
        let k = r_3.wrapping_mul(9708812670373448219u64);
        let (_, carry) = mac(r_3, k, Self::MODULUS_LIMBS[0usize], 0);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[1usize], carry);
        let (r_5, carry) = mac(r_5, k, Self::MODULUS_LIMBS[2usize], carry);
        let (r_6, carry) = mac(r_6, k, Self::MODULUS_LIMBS[3usize], carry);
        let (r_7, carry2) = adc(r[7usize], carry2, carry);
        let (d_0, borrow) = sbb(r_4, Self::MODULUS_LIMBS[0usize], 0);
        let (d_1, borrow) = sbb(r_5, Self::MODULUS_LIMBS[1usize], borrow);
        let (d_2, borrow) = sbb(r_6, Self::MODULUS_LIMBS[2usize], borrow);
        let (d_3, borrow) = sbb(r_7, Self::MODULUS_LIMBS[3usize], borrow);
        let (_, borrow) = sbb(carry2, 0, borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0usize] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1usize] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2usize] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3usize] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
}
pub struct Fp(#[doc(hidden)] pub [u64; 4usize]);
#[automatically_derived]
impl ::core::clone::Clone for Fp {
    #[inline]
    fn clone(&self) -> Fp {
        *self
    }
}
#[automatically_derived]
impl ::core::marker::Copy for Fp {}
#[automatically_derived]
impl ::core::cmp::PartialEq for Fp {
    #[inline]
    fn eq(&self, other: &Fp) -> bool {
        self.0 == other.0
    }
}
#[automatically_derived]
impl ::core::cmp::Eq for Fp {}
#[automatically_derived]
impl ::core::hash::Hash for Fp {
    #[inline]
    fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
        ::core::hash::Hash::hash(&self.0, state)
    }
}
#[automatically_derived]
impl ::core::default::Default for Fp {
    #[inline]
    fn default() -> Fp {
        Fp(::core::default::Default::default())
    }
}
impl core::fmt::Debug for Fp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use ff::PrimeField;
        let tmp = self.to_repr();
        f.write_fmt(format_args!("0x"))?;
        for &b in tmp.as_ref().iter().rev() {
            f.write_fmt(format_args!("{0:02x}", b))?;
        }
        Ok(())
    }
}
impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        Choice::from(self.0.iter().zip(other.0).all(|(a, b)| bool::from(a.ct_eq(&b))) as u8)
    }
}
impl ConditionallySelectable for Fp {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let limbs = (0..4usize)
            .map(|i| u64::conditional_select(&a.0[i], &b.0[i], choice))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        Fp(limbs)
    }
}
impl core::cmp::PartialOrd for Fp {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl core::cmp::Ord for Fp {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        use ff::PrimeField;
        let left = self.to_repr();
        let right = other.to_repr();
        left.as_ref()
            .iter()
            .zip(right.as_ref().iter())
            .rev()
            .find_map(|(left_byte, right_byte)| match left_byte.cmp(right_byte) {
                core::cmp::Ordering::Equal => None,
                res => Some(res),
            })
            .unwrap_or(core::cmp::Ordering::Equal)
    }
}
impl<T: ::core::borrow::Borrow<Fp>> ::core::iter::Sum<T> for Fp {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, item| acc + item.borrow())
    }
}
impl<T: ::core::borrow::Borrow<Fp>> ::core::iter::Product<T> for Fp {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::one(), |acc, item| acc * item.borrow())
    }
}
impl crate::serde::endian::EndianRepr for Fp {
    const ENDIAN: crate::serde::endian::Endian = crate::serde::endian::Endian::LE;
    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }
    fn from_bytes(bytes: &[u8]) -> subtle::CtOption<Self> {
        Fp::from_bytes(bytes[..Fp::SIZE].try_into().unwrap())
    }
}
impl Fp {
    pub const SIZE: usize = 4usize * 8;
    pub const NUM_LIMBS: usize = 4usize;
    pub(crate) const MODULUS_LIMBS: [u64; Self::NUM_LIMBS] = [
        18446744073709551597u64,
        18446744073709551615u64,
        18446744073709551615u64,
        18446744073709551615u64,
    ];
    pub(crate) const MODULUS_LIMBS_32: [u32; Self::NUM_LIMBS * 2] = [
        4294967277u32,
        4294967295u32,
        4294967295u32,
        4294967295u32,
        4294967295u32,
        4294967295u32,
        4294967295u32,
        4294967295u32,
    ];
    const R: Self = Self([19u64, 0u64, 0u64, 0u64]);
    const R2: Self = Self([361u64, 0u64, 0u64, 0u64]);
    const R3: Self = Self([6859u64, 0u64, 0u64, 0u64]);
    /// Returns zero, the additive identity.
    #[inline(always)]
    pub const fn zero() -> Fp {
        Fp([0; Self::NUM_LIMBS])
    }
    /// Returns one, the multiplicative identity.
    #[inline(always)]
    pub const fn one() -> Fp {
        Self::R
    }
    /// Converts from an integer represented in little endian
    /// into its (congruent) `$field` representation.
    pub const fn from_raw(val: [u64; Self::NUM_LIMBS]) -> Self {
        Self(val).mul_const(&Self::R2)
    }
    /// Attempts to convert a <#endian>-endian byte representation of
    /// a scalar into a `$field`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; Self::SIZE]) -> subtle::CtOption<Self> {
        use crate::serde::endian::EndianRepr;
        let mut el = Fp::default();
        Fp::ENDIAN.from_bytes(bytes, &mut el.0);
        subtle::CtOption::new(
            el * Self::R2,
            subtle::Choice::from(Self::is_less_than_modulus(&el.0) as u8),
        )
    }
    /// Converts an element of `$field` into a byte representation in
    /// <#endian>-endian byte order.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        use crate::serde::endian::EndianRepr;
        let el = self.from_mont();
        let mut res = [0; Self::SIZE];
        Fp::ENDIAN.to_bytes(&mut res, &el);
        res.into()
    }
    #[inline(always)]
    fn jacobi(&self) -> i64 {
        crate::ff_ext::jacobi::jacobi::<5usize>(
            &self.0,
            &[
                18446744073709551597u64,
                18446744073709551615u64,
                18446744073709551615u64,
                18446744073709551615u64,
            ],
        )
    }
    #[inline(always)]
    pub(crate) fn is_less_than_modulus(limbs: &[u64; Self::NUM_LIMBS]) -> bool {
        let borrow = limbs.iter().enumerate().fold(0, |borrow, (i, limb)| {
            crate::arithmetic::sbb(*limb, Self::MODULUS_LIMBS[i], borrow).1
        });
        (borrow as u8) & 1 == 1
    }
    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    pub fn lexicographically_largest(&self) -> Choice {
        const HALF_MODULUS: [u64; 4usize] = [
            18446744073709551606u64,
            18446744073709551615u64,
            18446744073709551615u64,
            9223372036854775807u64,
        ];
        let tmp = self.from_mont();
        let borrow = tmp
            .iter()
            .zip(HALF_MODULUS.iter())
            .fold(0, |borrow, (t, m)| crate::arithmetic::sbb(*t, *m, borrow).1);
        !Choice::from((borrow as u8) & 1)
    }
}
impl ff::Field for Fp {
    const ZERO: Self = Self::zero();
    const ONE: Self = Self::one();
    fn random(mut rng: impl RngCore) -> Self {
        let mut wide = [0u8; Self::SIZE * 2];
        rng.fill_bytes(&mut wide);
        <Fp as ff::FromUniformBytes<{ Fp::SIZE * 2 }>>::from_uniform_bytes(&wide)
    }
    #[inline(always)]
    fn double(&self) -> Self {
        self.double()
    }
    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }
    #[inline(always)]
    fn invert(&self) -> CtOption<Self> {
        const BYINVERTOR: crate::ff_ext::inverse::BYInverter<6usize> =
            crate::ff_ext::inverse::BYInverter::<6usize>::new(
                &[
                    18446744073709551597u64,
                    18446744073709551615u64,
                    18446744073709551615u64,
                    18446744073709551615u64,
                ],
                &[361u64, 0u64, 0u64, 0u64],
            );
        if let Some(inverse) = BYINVERTOR.invert::<{ Self::NUM_LIMBS }>(&self.0) {
            subtle::CtOption::new(Self(inverse), subtle::Choice::from(1))
        } else {
            subtle::CtOption::new(Self::zero(), subtle::Choice::from(0))
        }
    }
    fn sqrt(&self) -> subtle::CtOption<Self> {
        panic!("not implemented");
    }
    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        ff::helpers::sqrt_ratio_generic(num, div)
    }
}
impl From<Fp> for crate::serde::Repr<{ Fp::SIZE }> {
    fn from(value: Fp) -> crate::serde::Repr<{ Fp::SIZE }> {
        use ff::PrimeField;
        value.to_repr()
    }
}
impl<'a> From<&'a Fp> for crate::serde::Repr<{ Fp::SIZE }> {
    fn from(value: &'a Fp) -> crate::serde::Repr<{ Fp::SIZE }> {
        use ff::PrimeField;
        value.to_repr()
    }
}
impl ff::PrimeField for Fp {
    const NUM_BITS: u32 = 256u32;
    const CAPACITY: u32 = 256u32 - 1;
    const TWO_INV: Self = Self([
        7444465171802213905u64,
        8938587983385191397u64,
        16502324200923288628u64,
        4317787185005063841u64,
    ]);
    const MULTIPLICATIVE_GENERATOR: Self = Self([38u64, 0u64, 0u64, 0u64]);
    const S: u32 = 2u32;
    const ROOT_OF_UNITY: Self = Self([
        11509591633293059158u64,
        8716947078699447859u64,
        5419872930474550763u64,
        2346920571886282567u64,
    ]);
    const ROOT_OF_UNITY_INV: Self = Self([
        15549255515587436669u64,
        11596391619009908987u64,
        8505003924796416633u64,
        13134666729782424472u64,
    ]);
    const DELTA: Self = Self([304u64, 0u64, 0u64, 0u64]);
    const MODULUS: &'static str =
        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed";
    type Repr = crate::serde::Repr<{ Fp::SIZE }>;
    fn from_u128(v: u128) -> Self {
        let mut limbs = [0u64; 4];
        limbs[0] = v as u64;
        limbs[1] = (v >> 64) as u64;
        Self::R2 * Self(limbs)
    }
    fn from_repr(repr: Self::Repr) -> subtle::CtOption<Self> {
        let mut el = Fp::default();
        crate::serde::endian::Endian::LE.from_bytes(repr.as_ref(), &mut el.0);
        subtle::CtOption::new(
            el * Self::R2,
            subtle::Choice::from(Self::is_less_than_modulus(&el.0) as u8),
        )
    }
    fn to_repr(&self) -> Self::Repr {
        let el = self.from_mont();
        let mut res = [0; 32usize];
        crate::serde::endian::Endian::LE.to_bytes(&mut res, &el);
        res.into()
    }
    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }
}
impl crate::serde::SerdeObject for Fp {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 32usize);
        let inner = (0..4usize)
            .map(|off| u64::from_le_bytes(bytes[off * 8..(off + 1) * 8].try_into().unwrap()))
            .collect::<Vec<_>>();
        Self(inner.try_into().unwrap())
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 32usize {
            return None;
        }
        let elt = Self::from_raw_bytes_unchecked(bytes);
        Self::is_less_than_modulus(&elt.0).then(|| elt)
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(4usize * 4);
        for limb in self.0.iter() {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let inner = [(); 4usize].map(|_| {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf).unwrap();
            u64::from_le_bytes(buf)
        });
        Self(inner)
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut inner = [0u64; 4usize];
        for limb in inner.iter_mut() {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf)?;
            *limb = u64::from_le_bytes(buf);
        }
        let elt = Self(inner);
        Self::is_less_than_modulus(&elt.0).then(|| elt).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "input number is not less than field modulus",
            )
        })
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        for limb in self.0.iter() {
            writer.write_all(&limb.to_le_bytes())?;
        }
        Ok(())
    }
}
impl ff::FromUniformBytes<48usize> for Fp {
    fn from_uniform_bytes(bytes: &[u8; 48usize]) -> Self {
        let mut wide = [0u8; Self::SIZE * 2];
        wide[..48usize].copy_from_slice(bytes);
        let (a0, a1) = wide.split_at(Self::SIZE);
        let a0: [u64; Self::NUM_LIMBS] = (0..Self::NUM_LIMBS)
            .map(|off| u64::from_le_bytes(a0[off * 8..(off + 1) * 8].try_into().unwrap()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let a0 = Fp(a0);
        let a1: [u64; Self::NUM_LIMBS] = (0..Self::NUM_LIMBS)
            .map(|off| u64::from_le_bytes(a1[off * 8..(off + 1) * 8].try_into().unwrap()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let a1 = Fp(a1);
        a0.mul_const(&Self::R2) + a1.mul_const(&Self::R3)
    }
}
impl ff::FromUniformBytes<64usize> for Fp {
    fn from_uniform_bytes(bytes: &[u8; 64usize]) -> Self {
        let mut wide = [0u8; Self::SIZE * 2];
        wide[..64usize].copy_from_slice(bytes);
        let (a0, a1) = wide.split_at(Self::SIZE);
        let a0: [u64; Self::NUM_LIMBS] = (0..Self::NUM_LIMBS)
            .map(|off| u64::from_le_bytes(a0[off * 8..(off + 1) * 8].try_into().unwrap()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let a0 = Fp(a0);
        let a1: [u64; Self::NUM_LIMBS] = (0..Self::NUM_LIMBS)
            .map(|off| u64::from_le_bytes(a1[off * 8..(off + 1) * 8].try_into().unwrap()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let a1 = Fp(a1);
        a0.mul_const(&Self::R2) + a1.mul_const(&Self::R3)
    }
}
impl ff::WithSmallOrderMulGroup<3> for Fp {
    const ZETA: Self = Self([
        6287877203167225173u64,
        11949584387797497373u64,
        3562717594913860950u64,
        2257113996185601592u64,
    ]);
}
impl crate::ff_ext::Legendre for Fp {
    #[inline(always)]
    fn legendre(&self) -> i64 {
        self.jacobi()
    }
}
impl ::core::ops::Neg for Fp {
    type Output = Fp;
    #[inline]
    fn neg(self) -> Fp {
        -&self
    }
}
impl<'a> ::core::ops::Neg for &'a Fp {
    type Output = Fp;
    #[inline]
    fn neg(self) -> Fp {
        self.neg()
    }
}
impl<'a, 'b> ::core::ops::Sub<&'b Fp> for &'a Fp {
    type Output = Fp;
    #[inline]
    fn sub(self, rhs: &'b Fp) -> Fp {
        self.sub(rhs)
    }
}
impl<'a, 'b> ::core::ops::Add<&'b Fp> for &'a Fp {
    type Output = Fp;
    #[inline]
    fn add(self, rhs: &'b Fp) -> Fp {
        self.add(rhs)
    }
}
impl<'a, 'b> ::core::ops::Mul<&'b Fp> for &'a Fp {
    type Output = Fp;
    #[inline]
    fn mul(self, rhs: &'b Fp) -> Fp {
        self.mul(rhs)
    }
}
impl<'b> ::core::ops::Add<&'b Fp> for Fp {
    type Output = Fp;
    #[inline]
    fn add(self, rhs: &'b Fp) -> Fp {
        &self + rhs
    }
}
impl<'a> ::core::ops::Add<Fp> for &'a Fp {
    type Output = Fp;
    #[inline]
    fn add(self, rhs: Fp) -> Fp {
        self + &rhs
    }
}
impl ::core::ops::Add<Fp> for Fp {
    type Output = Fp;
    #[inline]
    fn add(self, rhs: Fp) -> Fp {
        &self + &rhs
    }
}
impl<'b> ::core::ops::Sub<&'b Fp> for Fp {
    type Output = Fp;
    #[inline]
    fn sub(self, rhs: &'b Fp) -> Fp {
        &self - rhs
    }
}
impl<'a> ::core::ops::Sub<Fp> for &'a Fp {
    type Output = Fp;
    #[inline]
    fn sub(self, rhs: Fp) -> Fp {
        self - &rhs
    }
}
impl ::core::ops::Sub<Fp> for Fp {
    type Output = Fp;
    #[inline]
    fn sub(self, rhs: Fp) -> Fp {
        &self - &rhs
    }
}
impl ::core::ops::SubAssign<Fp> for Fp {
    #[inline]
    fn sub_assign(&mut self, rhs: Fp) {
        *self = &*self - &rhs;
    }
}
impl ::core::ops::AddAssign<Fp> for Fp {
    #[inline]
    fn add_assign(&mut self, rhs: Fp) {
        *self = &*self + &rhs;
    }
}
impl<'b> ::core::ops::SubAssign<&'b Fp> for Fp {
    #[inline]
    fn sub_assign(&mut self, rhs: &'b Fp) {
        *self = &*self - rhs;
    }
}
impl<'b> ::core::ops::AddAssign<&'b Fp> for Fp {
    #[inline]
    fn add_assign(&mut self, rhs: &'b Fp) {
        *self = &*self + rhs;
    }
}
impl<'b> ::core::ops::Mul<&'b Fp> for Fp {
    type Output = Fp;
    #[inline]
    fn mul(self, rhs: &'b Fp) -> Fp {
        &self * rhs
    }
}
impl<'a> ::core::ops::Mul<Fp> for &'a Fp {
    type Output = Fp;
    #[inline]
    fn mul(self, rhs: Fp) -> Fp {
        self * &rhs
    }
}
impl ::core::ops::Mul<Fp> for Fp {
    type Output = Fp;
    #[inline]
    fn mul(self, rhs: Fp) -> Fp {
        &self * &rhs
    }
}
impl ::core::ops::MulAssign<Fp> for Fp {
    #[inline]
    fn mul_assign(&mut self, rhs: Fp) {
        *self = &*self * &rhs;
    }
}
impl<'b> ::core::ops::MulAssign<&'b Fp> for Fp {
    #[inline]
    fn mul_assign(&mut self, rhs: &'b Fp) {
        *self = &*self * rhs;
    }
}
impl ff::PrimeFieldBits for Fp {
    type ReprBits = [u64; Self::NUM_LIMBS];
    fn to_le_bits(&self) -> ff::FieldBits<Self::ReprBits> {
        use ff::PrimeField;
        let bytes: [u8; Self::SIZE] = self.to_repr().into();
        const STEP: usize = 8;
        let limbs = (0..Self::NUM_LIMBS * 8 / STEP)
            .map(|off| {
                let limb =
                    u64::from_le_bytes(bytes[off * STEP..(off + 1) * STEP].try_into().unwrap());
                limb
            })
            .collect::<Vec<u64>>();
        ff::FieldBits::new(limbs.try_into().unwrap())
    }
    fn char_le_bits() -> ff::FieldBits<Self::ReprBits> {
        let bits = ff::FieldBits::new(Self::MODULUS_LIMBS);
        bits
    }
}
impl<'de> ::serde::Deserialize<'de> for Fp {
    fn deserialize<D: ::serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::Error as _;
        let bytes = if deserializer.is_human_readable() {
            hex::serde::deserialize(deserializer)?
        } else {
            ::serde_arrays::deserialize::<_, u8, { Fp::SIZE }>(deserializer)?
        };
        use ff::PrimeField;
        Option::from(Self::from_repr(bytes.into())).ok_or_else(|| {
            D::Error::custom("deserialized bytes don't encode a valid field element")
        })
    }
}
impl ::serde::Serialize for Fp {
    fn serialize<S: ::serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use ff::PrimeField;
        if serializer.is_human_readable() {
            hex::serde::serialize(self.to_repr().as_ref(), serializer)
        } else {
            let bytes: [u8; Fp::SIZE] = self.to_repr().into();
            ::serde_arrays::serialize(&bytes, serializer)
        }
    }
}
impl From<u64> for Fp {
    fn from(val: u64) -> Fp {
        let limbs = std::iter::once(val)
            .chain(std::iter::repeat(0))
            .take(Self::NUM_LIMBS)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        Fp(limbs) * Self::R2
    }
}
impl From<bool> for Fp {
    fn from(val: bool) -> Fp {
        let limbs = std::iter::once(u64::from(val))
            .chain(std::iter::repeat(0))
            .take(Self::NUM_LIMBS)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        Fp(limbs) * Self::R2
    }
}

#[cfg(test)]
mod test {
    // use super::*;
    // crate::field_testing_suite!(Fp, "field_arithmetic");
    // crate::field_testing_suite!(Fp, "conversion");
    // crate::field_testing_suite!(Fp, "serdeobject");
    // crate::field_testing_suite!(Fp, "quadratic_residue");
    // crate::field_testing_suite!(Fp, "bits");
    // crate::field_testing_suite!(Fp, "constants");
    // crate::field_testing_suite!(Fp, "sqrt");
    // crate::field_testing_suite!(Fp, "zeta");
    // crate::field_testing_suite!(Fp, "from_uniform_bytes", 48, 64);
}

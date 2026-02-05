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

//! Curve25519 Base Field Arithmetic
//!
//! This module implements the base field Fp for Curve25519, where
//! p = 2^255 - 19.
//!
//! # Representation
//!
//! Field elements are represented in Montgomery form using 4 limbs of 64-bit
//! unsigned integers (256 bits total) in little-endian order.
//!
//! For a field element `a`, we store `aR mod p` where R = 2^256.
//! This allows efficient modular multiplication using Montgomery reduction.
//!
//! This implementation is necessary until the base field is exposed in
//! the curve25519_dalek:
//! [PR](https://github.com/dalek-cryptography/curve25519-dalek/pull/816)
//! The internal curve operations use their own base field representation.
//! This is only used to represent the point values for the circuits.
//!
//! # References
//!
//! - [Curve25519 Paper](https://cr.yp.to/ecdh/curve25519-20060209.pdf)

use core::convert::TryInto;

use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// A field element represented as 4 limbs (256 bits)
type Limbs = [u64; 4];

/// Extended limbs used during multiplication (512 bits)
type ExtendedLimbs = [u64; 8];

#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct Fp(#[doc(hidden)] pub Limbs);

/// INV = -(p^{-1} mod 2^64) mod 2^64.
const INV: u64 = 0x86bca1af286bca1bu64;
impl Fp {
    #[inline(always)]
    pub const fn add(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, sbb};
        let (d_0, carry) = adc(self.0[0], rhs.0[0], 0);
        let (d_1, carry) = adc(self.0[1], rhs.0[1], carry);
        let (d_2, carry) = adc(self.0[2], rhs.0[2], carry);
        let (d_3, carry) = adc(self.0[3], rhs.0[3], carry);
        let (d_0, borrow) = sbb(d_0, Self::MODULUS_LIMBS[0], 0);
        let (d_1, borrow) = sbb(d_1, Self::MODULUS_LIMBS[1], borrow);
        let (d_2, borrow) = sbb(d_2, Self::MODULUS_LIMBS[2], borrow);
        let (d_3, borrow) = sbb(d_3, Self::MODULUS_LIMBS[3], borrow);
        let (_, borrow) = sbb(carry, 0, borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline]
    pub const fn double(&self) -> Self {
        self.add(self)
    }
    #[inline(always)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        use crate::arithmetic::{adc, sbb};
        let (d_0, borrow) = sbb(self.0[0], rhs.0[0], 0);
        let (d_1, borrow) = sbb(self.0[1], rhs.0[1], borrow);
        let (d_2, borrow) = sbb(self.0[2], rhs.0[2], borrow);
        let (d_3, borrow) = sbb(self.0[3], rhs.0[3], borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline(always)]
    pub const fn neg(&self) -> Self {
        use crate::arithmetic::sbb;
        let (d_0, borrow) = sbb(Self::MODULUS_LIMBS[0], self.0[0], 0);
        let (d_1, borrow) = sbb(Self::MODULUS_LIMBS[1], self.0[1], borrow);
        let (d_2, borrow) = sbb(Self::MODULUS_LIMBS[2], self.0[2], borrow);
        let (d_3, _) = sbb(Self::MODULUS_LIMBS[3], self.0[3], borrow);
        let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0) as u64).wrapping_sub(1);
        Fp([d_0 & mask, d_1 & mask, d_2 & mask, d_3 & mask])
    }
    #[inline(always)]
    pub const fn mul(&self, rhs: &Self) -> Self {
        use crate::arithmetic::mac;
        let (r_0, carry) = mac(0, self.0[0], rhs.0[0], 0);
        let (r_1, carry) = mac(0, self.0[0], rhs.0[1], carry);
        let (r_2, carry) = mac(0, self.0[0], rhs.0[2], carry);
        let (r_3, r_4) = mac(0, self.0[0], rhs.0[3], carry);
        let (r_1, carry) = mac(r_1, self.0[1], rhs.0[0], 0);
        let (r_2, carry) = mac(r_2, self.0[1], rhs.0[1], carry);
        let (r_3, carry) = mac(r_3, self.0[1], rhs.0[2], carry);
        let (r_4, r_5) = mac(r_4, self.0[1], rhs.0[3], carry);
        let (r_2, carry) = mac(r_2, self.0[2], rhs.0[0], 0);
        let (r_3, carry) = mac(r_3, self.0[2], rhs.0[1], carry);
        let (r_4, carry) = mac(r_4, self.0[2], rhs.0[2], carry);
        let (r_5, r_6) = mac(r_5, self.0[2], rhs.0[3], carry);
        let (r_3, carry) = mac(r_3, self.0[3], rhs.0[0], 0);
        let (r_4, carry) = mac(r_4, self.0[3], rhs.0[1], carry);
        let (r_5, carry) = mac(r_5, self.0[3], rhs.0[2], carry);
        let (r_6, r_7) = mac(r_6, self.0[3], rhs.0[3], carry);
        Fp::montgomery_reduce(&[r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7])
    }
    #[inline(always)]
    pub const fn square(&self) -> Self {
        use crate::arithmetic::{adc, mac};
        let (r_1, carry) = mac(0, self.0[0], self.0[1], 0);
        let (r_2, carry) = mac(0, self.0[0], self.0[2], carry);
        let (r_3, r_4) = mac(0, self.0[0], self.0[3], carry);
        let (r_3, carry) = mac(r_3, self.0[1], self.0[2], 0);
        let (r_4, r_5) = mac(r_4, self.0[1], self.0[3], carry);
        let (r_5, r_6) = mac(r_5, self.0[2], self.0[3], 0);
        let r_7 = r_6 >> 63;
        let r_6 = (r_6 << 1) | (r_5 >> 63);
        let r_5 = (r_5 << 1) | (r_4 >> 63);
        let r_4 = (r_4 << 1) | (r_3 >> 63);
        let r_3 = (r_3 << 1) | (r_2 >> 63);
        let r_2 = (r_2 << 1) | (r_1 >> 63);
        let r_1 = r_1 << 1;
        let (r_0, carry) = mac(0, self.0[0], self.0[0], 0);
        let (r_1, carry) = adc(0, r_1, carry);
        let (r_2, carry) = mac(r_2, self.0[1], self.0[1], carry);
        let (r_3, carry) = adc(0, r_3, carry);
        let (r_4, carry) = mac(r_4, self.0[2], self.0[2], carry);
        let (r_5, carry) = adc(0, r_5, carry);
        let (r_6, carry) = mac(r_6, self.0[3], self.0[3], carry);
        let (r_7, _) = adc(0, r_7, carry);
        Fp::montgomery_reduce(&[r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7])
    }

    #[inline(always)]
    pub(crate) const fn montgomery_reduce(r: &ExtendedLimbs) -> Self {
        use crate::arithmetic::{adc, mac, sbb};
        let k = r[0].wrapping_mul(INV);
        let (_, carry) = mac(r[0], k, Self::MODULUS_LIMBS[0], 0);
        let (r_1, carry) = mac(r[1], k, Self::MODULUS_LIMBS[1], carry);
        let (r_2, carry) = mac(r[2], k, Self::MODULUS_LIMBS[2], carry);
        let (r_3, carry) = mac(r[3], k, Self::MODULUS_LIMBS[3], carry);
        let (r_4, carry2) = adc(r[4], 0, carry);
        let k = r_1.wrapping_mul(INV);
        let (_, carry) = mac(r_1, k, Self::MODULUS_LIMBS[0], 0);
        let (r_2, carry) = mac(r_2, k, Self::MODULUS_LIMBS[1], carry);
        let (r_3, carry) = mac(r_3, k, Self::MODULUS_LIMBS[2], carry);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[3], carry);
        let (r_5, carry2) = adc(r[5], carry2, carry);
        let k = r_2.wrapping_mul(INV);
        let (_, carry) = mac(r_2, k, Self::MODULUS_LIMBS[0], 0);
        let (r_3, carry) = mac(r_3, k, Self::MODULUS_LIMBS[1], carry);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[2], carry);
        let (r_5, carry) = mac(r_5, k, Self::MODULUS_LIMBS[3], carry);
        let (r_6, carry2) = adc(r[6], carry2, carry);
        let k = r_3.wrapping_mul(INV);
        let (_, carry) = mac(r_3, k, Self::MODULUS_LIMBS[0], 0);
        let (r_4, carry) = mac(r_4, k, Self::MODULUS_LIMBS[1], carry);
        let (r_5, carry) = mac(r_5, k, Self::MODULUS_LIMBS[2], carry);
        let (r_6, carry) = mac(r_6, k, Self::MODULUS_LIMBS[3], carry);
        let (r_7, carry2) = adc(r[7], carry2, carry);
        let (d_0, borrow) = sbb(r_4, Self::MODULUS_LIMBS[0], 0);
        let (d_1, borrow) = sbb(r_5, Self::MODULUS_LIMBS[1], borrow);
        let (d_2, borrow) = sbb(r_6, Self::MODULUS_LIMBS[2], borrow);
        let (d_3, borrow) = sbb(r_7, Self::MODULUS_LIMBS[3], borrow);
        let (_, borrow) = sbb(carry2, 0, borrow);
        let (d_0, carry) = adc(d_0, Self::MODULUS_LIMBS[0] & borrow, 0);
        let (d_1, carry) = adc(d_1, Self::MODULUS_LIMBS[1] & borrow, carry);
        let (d_2, carry) = adc(d_2, Self::MODULUS_LIMBS[2] & borrow, carry);
        let (d_3, _) = adc(d_3, Self::MODULUS_LIMBS[3] & borrow, carry);
        Fp([d_0, d_1, d_2, d_3])
    }
    #[inline(always)]
    pub(crate) const fn from_mont(&self) -> [u64; 4] {
        use crate::arithmetic::mac;
        let k = self.0[0].wrapping_mul(INV);
        let (_, r_0) = mac(self.0[0], k, Self::MODULUS_LIMBS[0], 0);
        let (r_1, r_0) = mac(self.0[1], k, Self::MODULUS_LIMBS[1], r_0);
        let (r_2, r_0) = mac(self.0[2], k, Self::MODULUS_LIMBS[2], r_0);
        let (r_3, r_0) = mac(self.0[3], k, Self::MODULUS_LIMBS[3], r_0);
        let k = r_1.wrapping_mul(INV);
        let (_, r_1) = mac(r_1, k, Self::MODULUS_LIMBS[0], 0);
        let (r_2, r_1) = mac(r_2, k, Self::MODULUS_LIMBS[1], r_1);
        let (r_3, r_1) = mac(r_3, k, Self::MODULUS_LIMBS[2], r_1);
        let (r_0, r_1) = mac(r_0, k, Self::MODULUS_LIMBS[3], r_1);
        let k = r_2.wrapping_mul(INV);
        let (_, r_2) = mac(r_2, k, Self::MODULUS_LIMBS[0], 0);
        let (r_3, r_2) = mac(r_3, k, Self::MODULUS_LIMBS[1], r_2);
        let (r_0, r_2) = mac(r_0, k, Self::MODULUS_LIMBS[2], r_2);
        let (r_1, r_2) = mac(r_1, k, Self::MODULUS_LIMBS[3], r_2);
        let k = r_3.wrapping_mul(INV);
        let (_, r_3) = mac(r_3, k, Self::MODULUS_LIMBS[0], 0);
        let (r_0, r_3) = mac(r_0, k, Self::MODULUS_LIMBS[1], r_3);
        let (r_1, r_3) = mac(r_1, k, Self::MODULUS_LIMBS[2], r_3);
        let (r_2, r_3) = mac(r_2, k, Self::MODULUS_LIMBS[3], r_3);
        Fp([r_0, r_1, r_2, r_3]).sub(&Fp(Self::MODULUS_LIMBS)).0
    }
}
impl Fp {
    /// Const-compatible multiplication (delegates to `mul`).
    #[inline(always)]
    pub(crate) const fn mul_const(&self, rhs: &Self) -> Self {
        self.mul(rhs)
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
    pub const SIZE: usize = 4 * 8;
    pub const NUM_LIMBS: usize = 4;
    pub(crate) const MODULUS_LIMBS: [u64; Self::NUM_LIMBS] = [
        0xffffffffffffffed,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x7fffffffffffffff,
    ];
    #[allow(dead_code)]
    pub(crate) const MODULUS_LIMBS_32: [u32; Self::NUM_LIMBS * 2] = [
        0xffffffed, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0x7fffffff,
    ];
    const R: Self = Self([0x26, 0, 0, 0]);
    const R2: Self = Self([0x5a4, 0, 0, 0]);
    const R3: Self = Self([0xd658, 0, 0, 0]);

    /// Precomputed value: 2^((p-5)/8) mod p
    /// Used in sqrt() algorithm for p ≡ 5 (mod 8)
    const T_SQRT: Self = Self::from_raw([
        0x62770d93a507504f,
        0x97a18c035697f23c,
        0x95a6804c9efdebd3,
        0x55c1924027e0ef85,
    ]);

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
        res
    }
    #[inline(always)]
    fn jacobi(&self) -> i64 {
        crate::ff_ext::jacobi::jacobi::<5>(&self.0, &Self::MODULUS_LIMBS)
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
        const HALF_MODULUS: [u64; 4] = [
            0xfffffffffffffff6,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x3fffffffffffffff,
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
        const BYINVERTOR: crate::ff_ext::inverse::BYInverter<6> =
            crate::ff_ext::inverse::BYInverter::<6>::new(&Fp::MODULUS_LIMBS, &Fp::R2.0);
        if let Some(inverse) = BYINVERTOR.invert::<{ Self::NUM_LIMBS }>(&self.0) {
            subtle::CtOption::new(Self(inverse), subtle::Choice::from(1))
        } else {
            subtle::CtOption::new(Self::zero(), subtle::Choice::from(0))
        }
    }

    fn sqrt(&self) -> subtle::CtOption<Self> {
        // Algorithm 3 https://eprint.iacr.org/2012/685.pdf
        // for p = 5 mod 8
        const EXP: [u64; 4] = [
            0xfffffffffffffffd,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x0fffffffffffffff,
        ];
        let a1 = self.pow_vartime(EXP);
        let a0 = (a1.square() * self).square();

        let valid = a0.ct_eq(&-Self::ONE);

        let b = Self::T_SQRT * a1;
        let ab = b * self;
        let i = (ab * b).double();
        let x = ab * (i - Self::ONE);
        CtOption::new(x, !valid)
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
    const NUM_BITS: u32 = 255;
    const CAPACITY: u32 = 255 - 1;
    const TWO_INV: Self = Self([0x13, 0, 0, 0]);
    const MULTIPLICATIVE_GENERATOR: Self = Self([0x4c, 0, 0, 0]);
    const S: u32 = 2u32;
    const ROOT_OF_UNITY: Self = Self([
        0x3b5807d4fe2bdb04,
        0x3f590fdb51be9ed,
        0x6d6e16bf336202d1,
        0x75776b0bd6c71ba8,
    ]);
    const ROOT_OF_UNITY_INV: Self = Self([
        0xc4a7f82b01d424e9,
        0xfc0a6f024ae41612,
        0x9291e940cc9dfd2e,
        0xa8894f42938e457,
    ]);
    const DELTA: Self = Self([0x260, 0, 0, 0]);
    const MODULUS: &'static str =
        "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed";
    type Repr = crate::serde::Repr<{ Fp::SIZE }>;
    fn from_u128(v: u128) -> Self {
        Self::R2
            * Self(
                [v as u64, (v >> 64) as u64]
                    .iter()
                    .copied()
                    .chain(core::iter::repeat(0))
                    .take(Self::NUM_LIMBS)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
            )
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
        let mut res = [0; 32];
        crate::serde::endian::Endian::LE.to_bytes(&mut res, &el);
        res.into()
    }
    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }
}
impl crate::serde::SerdeObject for Fp {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 32);
        let inner = (0..4)
            .map(|off| u64::from_le_bytes(bytes[off * 8..(off + 1) * 8].try_into().unwrap()))
            .collect::<Vec<_>>();
        Self(inner.try_into().unwrap())
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 32 {
            return None;
        }
        let elt = Self::from_raw_bytes_unchecked(bytes);
        Self::is_less_than_modulus(&elt.0).then_some(elt)
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(4 * 4);
        for limb in self.0.iter() {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let inner = [(); 4].map(|_| {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf).unwrap();
            u64::from_le_bytes(buf)
        });
        Self(inner)
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut inner = [0u64; 4];
        for limb in inner.iter_mut() {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf)?;
            *limb = u64::from_le_bytes(buf);
        }
        let elt = Self(inner);
        Self::is_less_than_modulus(&elt.0).then_some(elt).ok_or_else(|| {
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
impl Fp {
    fn from_uniform_bytes_inner(bytes: &[u8]) -> Self {
        let mut wide = [0u8; Self::SIZE * 2];
        wide[..bytes.len()].copy_from_slice(bytes);
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

impl ff::FromUniformBytes<48> for Fp {
    fn from_uniform_bytes(bytes: &[u8; 48]) -> Self {
        Self::from_uniform_bytes_inner(bytes)
    }
}

impl ff::FromUniformBytes<64> for Fp {
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Self::from_uniform_bytes_inner(bytes)
    }
}
impl ff::WithSmallOrderMulGroup<3> for Fp {
    const ZETA: Self = Self([
        0x50042761e7b20780,
        0xdff5c6f9aea649f9,
        0x4a1118654ba1a419,
        0x5443a41d4b0d18fe,
    ]);
}

crate::extend_field_legendre!(Fp);
crate::impl_binops_calls!(Fp);
crate::impl_binops_additive!(Fp, Fp);
crate::impl_binops_multiplicative!(Fp, Fp);
crate::field_bits!(Fp);
crate::serialize_deserialize_primefield!(Fp);
crate::impl_from_u64!(Fp);
crate::impl_from_bool!(Fp);

#[cfg(test)]
mod test {
    use super::*;
    crate::field_testing_suite!(Fp, "field_arithmetic");
    crate::field_testing_suite!(Fp, "conversion");
    crate::field_testing_suite!(Fp, "serdeobject");
    crate::field_testing_suite!(Fp, "quadratic_residue");
    crate::field_testing_suite!(Fp, "bits");
    crate::field_testing_suite!(Fp, "constants");
    crate::field_testing_suite!(Fp, "sqrt");
    crate::field_testing_suite!(Fp, "zeta");
    crate::field_testing_suite!(Fp, "from_uniform_bytes", 48, 64);
}

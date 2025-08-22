//! This module provides an implementation of the BLS12-381 base field `GF(p)`
//! where `p =
//! 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`

use core::{
    cmp, fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::{convert::TryInto, ops::Deref};

use blst::*;
use ff::{Field, PrimeField, PrimeFieldBits, WithSmallOrderMulGroup};
use halo2curves::serde::SerdeObject;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::fp2::Fp2;

// Little-endian non-Montgomery form.
const MODULUS: [u64; NUM_LIMBS] = [
    0xb9fe_ffff_ffff_aaab,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

#[cfg(not(target_pointer_width = "64"))]
const MODULUS_32: [u32; 2 * NUM_LIMBS] = [
    0xffff_aaab,
    0xb9fe_ffff,
    0xb153_ffff,
    0x1eab_fffe,
    0xf6b0_f624,
    0x6730_d2a0,
    0xf385_12bf,
    0x6477_4b84,
    0x434b_acd7,
    0x4b1b_a7b6,
    0x397f_e69a,
    0x1a01_11ea,
];

// Little-endian non-Montgomery form.
const MODULUS_REPR: [u8; 48] = [
    0xab, 0xaa, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xb9, 0xff, 0xff, 0x53, 0xb1, 0xfe, 0xff, 0xab, 0x1e,
    0x24, 0xf6, 0xb0, 0xf6, 0xa0, 0xd2, 0x30, 0x67, 0xbf, 0x12, 0x85, 0xf3, 0x84, 0x4b, 0x77, 0x64,
    0xd7, 0xac, 0x4b, 0x43, 0xb6, 0xa7, 0x1b, 0x4b, 0x9a, 0xe6, 0x7f, 0x39, 0xea, 0x11, 0x01, 0x1a,
];

const ZERO: Fp = Fp(blst_fp {
    l: [0, 0, 0, 0, 0, 0],
});

/// R = 2^384 mod p
const R: Fp = Fp(blst_fp {
    l: [
        0x7609_0000_0002_fffd,
        0xebf4_000b_c40c_0002,
        0x5f48_9857_53c7_58ba,
        0x77ce_5853_7052_5745,
        0x5c07_1a97_a256_ec6d,
        0x15f6_5ec3_fa80_e493,
    ],
});

// These constant is needed to implement [`FormUniformBytes`].
// It is left here in case the trait is implemented in the future.
// /// R2 = 2^(384*2) mod p
// const R2: Fp = Fp(blst_fp {
//     l: [
//         0xf4df_1f34_1c34_1746,
//         0x0a76_e6a6_09d1_04f1,
//         0x8de5_476c_4c95_b6d5,
//         0x67eb_88a9_939d_83c0,
//         0x9a79_3e85_b519_952d,
//         0x1198_8fe5_92ca_e3aa,
//     ],
// });
//
// /// R3 = 2^(384*3) mod p
// const R3: Fp = Fp(blst_fp {
//     l: [
//         0xed48_ac6b_d94c_a1e0,
//         0x315f_831e_03a7_adf8,
//         0x9a53_352a_615e_29dd,
//         0x34c0_4e5e_921e_1761,
//         0x2512_d435_6572_4728,
//         0x0aa6_3460_9175_5d4d,
//     ],
// });

/// `Fp` values are always in Montgomery form; i.e., Fp(a) = aR mod p, with R =
/// 2^384. `blst_fp.l` is in little-endian `u64` limbs format.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Fp(pub(crate) blst_fp);

// Coefficients for the Frobenius automorphism.
pub(crate) const FROBENIUS_COEFF_FP2_C1: [Fp; 2] = [
    // Fp(-1)**(((q^0) - 1) / 2)
    Fp(blst_fp {
        l: [
            0x760900000002fffd,
            0xebf4000bc40c0002,
            0x5f48985753c758ba,
            0x77ce585370525745,
            0x5c071a97a256ec6d,
            0x15f65ec3fa80e493,
        ],
    }),
    // Fp(-1)**(((q^1) - 1) / 2)
    Fp(blst_fp {
        l: [
            0x43f5fffffffcaaae,
            0x32b7fff2ed47fffd,
            0x7e83a49a2e99d69,
            0xeca8f3318332bb7a,
            0xef148d1ea0f4c069,
            0x40ab3263eff0206,
        ],
    }),
];

pub const FROBENIUS_COEFF_FP6_C1: [Fp2; 6] = [
    // Fp2(u + 1)**(((q^0) - 1) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((q^1) - 1) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
        Fp(blst_fp {
            l: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ],
        }),
    ),
    // Fp2(u + 1)**(((q^2) - 1) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x51ba4ab241b6160,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((q^3) - 1) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
        Fp(blst_fp {
            l: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        }),
    ),
    // Fp2(u + 1)**(((q^4) - 1) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((q^5) - 1) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
        Fp(blst_fp {
            l: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x51ba4ab241b6160,
            ],
        }),
    ),
];

pub const FROBENIUS_COEFF_FP6_C2: [Fp2; 6] = [
    // Fp2(u + 1)**(((2q^0) - 2) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((2q^1) - 2) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0x890dc9e4867545c3,
                0x2af322533285a5d5,
                0x50880866309b7e2c,
                0xa20d1b8c7e881024,
                0x14e4f04fe2db9068,
                0x14e56d3f1564853a,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((2q^2) - 2) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((2q^3) - 2) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0x43f5fffffffcaaae,
                0x32b7fff2ed47fffd,
                0x7e83a49a2e99d69,
                0xeca8f3318332bb7a,
                0xef148d1ea0f4c069,
                0x40ab3263eff0206,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((2q^4) - 2) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0x30f1361b798a64e8,
                0xf3b8ddab7ece5a2a,
                0x16a8ca3ac61577f7,
                0xc26a2ff874fd029b,
                0x3636b76660701c6e,
                0x51ba4ab241b6160,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
    // Fp2(u + 1)**(((2q^5) - 2) / 3)
    Fp2::new(
        Fp(blst_fp {
            l: [
                0xecfb361b798dba3a,
                0xc100ddb891865a2c,
                0xec08ff1232bda8e,
                0xd5c13cc6f1ca4721,
                0x47222a47bf7b5c04,
                0x110f184e51c5f59,
            ],
        }),
        Fp(blst_fp {
            l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
        }),
    ),
];

impl From<u64> for Fp {
    fn from(val: u64) -> Fp {
        let mut repr = [0u8; 48];
        repr[..8].copy_from_slice(&val.to_le_bytes());
        Self::from_bytes_le(&repr).unwrap()
    }
}

impl Ord for Fp {
    #[allow(clippy::comparison_chain)]
    fn cmp(&self, other: &Fp) -> cmp::Ordering {
        for (a, b) in self.to_bytes_be().iter().zip(other.to_bytes_be().iter()) {
            if a > b {
                return cmp::Ordering::Greater;
            } else if a < b {
                return cmp::Ordering::Less;
            }
        }
        cmp::Ordering::Equal
    }
}

impl PartialOrd for Fp {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fp) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Fp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let be_bytes = self.to_bytes_be();
        write!(f, "Fp(0x")?;
        for &b in be_bytes.iter() {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl fmt::Display for Fp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl core::hash::Hash for Fp {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.l.hash::<H>(state)
    }
}

impl From<Fp> for blst_fp {
    fn from(val: Fp) -> blst_fp {
        val.0
    }
}

impl From<blst_fp> for Fp {
    fn from(val: blst_fp) -> Fp {
        Fp(val)
    }
}

impl Default for Fp {
    fn default() -> Self {
        Fp::ZERO
    }
}

impl Eq for Fp {}

impl PartialEq for Fp {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.l[0].ct_eq(&other.0.l[0])
            & self.0.l[1].ct_eq(&other.0.l[1])
            & self.0.l[2].ct_eq(&other.0.l[2])
            & self.0.l[3].ct_eq(&other.0.l[3])
            & self.0.l[4].ct_eq(&other.0.l[4])
            & self.0.l[5].ct_eq(&other.0.l[5])
    }
}

impl ConditionallySelectable for Fp {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp(blst_fp {
            l: [
                u64::conditional_select(&a.0.l[0], &b.0.l[0], choice),
                u64::conditional_select(&a.0.l[1], &b.0.l[1], choice),
                u64::conditional_select(&a.0.l[2], &b.0.l[2], choice),
                u64::conditional_select(&a.0.l[3], &b.0.l[3], choice),
                u64::conditional_select(&a.0.l[4], &b.0.l[4], choice),
                u64::conditional_select(&a.0.l[5], &b.0.l[5], choice),
            ],
        })
    }
}

impl Neg for &Fp {
    type Output = Fp;

    #[inline]
    fn neg(self) -> Fp {
        let mut out = *self;
        unsafe { blst_fp_cneg(&mut out.0, &self.0, true) };
        out
    }
}

impl Neg for Fp {
    type Output = Fp;

    #[inline]
    fn neg(mut self) -> Fp {
        unsafe { blst_fp_cneg(&mut self.0, &self.0, true) };
        self
    }
}

impl Sub<&Fp> for &Fp {
    type Output = Fp;

    #[inline]
    fn sub(self, rhs: &Fp) -> Fp {
        let mut out = *self;
        out -= rhs;
        out
    }
}

impl Add<&Fp> for &Fp {
    type Output = Fp;

    #[inline]
    fn add(self, rhs: &Fp) -> Fp {
        let mut out = *self;
        out += rhs;
        out
    }
}

impl Mul<&Fp> for &Fp {
    type Output = Fp;

    #[inline]
    fn mul(self, rhs: &Fp) -> Fp {
        let mut out = *self;
        out *= rhs;
        out
    }
}

impl AddAssign<&Fp> for Fp {
    #[inline]
    fn add_assign(&mut self, rhs: &Fp) {
        unsafe { blst_fp_add(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&Fp> for Fp {
    #[inline]
    fn sub_assign(&mut self, rhs: &Fp) {
        unsafe { blst_fp_sub(&mut self.0, &self.0, &rhs.0) };
    }
}

impl MulAssign<&Fp> for Fp {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fp) {
        unsafe { blst_fp_mul(&mut self.0, &self.0, &rhs.0) };
    }
}

impl_add_sub!(Fp);
impl_add_sub_assign!(Fp);
impl_mul!(Fp);
impl_mul_assign!(Fp);
impl_sum!(Fp);
impl_product!(Fp);

// Returns `true` if  `le_bytes` is less than the modulus (both are in
// non-Montgomery form).
#[allow(clippy::comparison_chain)]
fn is_valid(le_bytes: &[u8; 48]) -> bool {
    for (a, b) in le_bytes.iter().zip(MODULUS_REPR.iter()).rev() {
        if a > b {
            return false;
        } else if a < b {
            return true;
        }
    }
    // false if matching the modulus
    false
}

// Returns `true` if  `le_bytes` is less than the modulus (both are in
// non-Montgomery form).
#[allow(clippy::comparison_chain)]
fn is_valid_u64(le_bytes: &[u64; 6]) -> bool {
    for (a, b) in le_bytes.iter().zip(MODULUS.iter()).rev() {
        if a > b {
            return false;
        } else if a < b {
            return true;
        }
    }
    // false if matching the modulus
    false
}

fn u64s_from_bytes(bytes: &[u8; 48]) -> [u64; 6] {
    [
        u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
        u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
        u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
        u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
        u64::from_le_bytes(bytes[40..].try_into().unwrap()),
    ]
}

const NUM_BITS: u32 = 381;
// Number of 64-bit limbs.
const NUM_LIMBS: usize = 6;
// Size in bytes.
const SIZE: usize = 48;
/// The number of bits we should "shave" from a randomly sampled reputation.
const REPR_SHAVE_BITS: usize = 384 - NUM_BITS as usize;

impl Field for Fp {
    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let mut raw = [0u64; 6];
            for int in raw.iter_mut() {
                *int = rng.next_u64();
            }

            // Mask away the unused most-significant bits.
            raw[5] &= 0xffffffffffffffff >> REPR_SHAVE_BITS;

            if let Some(fp) = Fp::from_u64s_le(&raw).into() {
                return fp;
            }
        }
    }

    const ZERO: Self = ZERO;

    // Returns `1 mod p` in Montgomery form `1 * R mod p`;
    const ONE: Self = R;

    fn is_zero(&self) -> Choice {
        self.ct_eq(&ZERO)
    }

    fn square(&self) -> Self {
        let mut sq = *self;
        unsafe { blst_fp_sqr(&mut sq.0, &self.0) }
        sq
    }

    fn double(&self) -> Self {
        let mut out = *self;
        out += self;
        out
    }

    fn invert(&self) -> CtOption<Self> {
        let mut inv = Self::default();
        unsafe { blst_fp_eucl_inverse(&mut inv.0, &self.0) };
        let is_invertible = !self.ct_eq(&Fp::ZERO);
        CtOption::new(inv, is_invertible)
    }

    fn sqrt(&self) -> CtOption<Self> {
        let mut out = Self::default();
        let is_quad_res = unsafe { blst_fp_sqrt(&mut out.0, &self.0) };
        CtOption::new(out, Choice::from(is_quad_res as u8))
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        // ff::helpers::sqrt_ratio_generic(num, div)
        unimplemented!()
    }
}

impl Fp {
    pub fn char() -> [u8; 48] {
        MODULUS_REPR
    }

    /// Attempts to convert a little-endian byte representation of
    /// a scalar into an `Fp`, failing if the input is not canonical.
    pub fn from_bytes_le(bytes: &[u8; 48]) -> CtOption<Fp> {
        // TODO: constant time
        let is_some = Choice::from(is_valid(bytes) as u8);
        let mut out = blst_fp::default();
        unsafe { blst_fp_from_lendian(&mut out, bytes.as_ptr()) };

        CtOption::new(Fp(out), is_some)
    }

    /// Attempts to convert a big-endian byte representation of
    /// a scalar into an `Fp`, failing if the input is not canonical.
    pub fn from_bytes_be(be_bytes: &[u8; 48]) -> CtOption<Fp> {
        let mut le_bytes = *be_bytes;
        le_bytes.reverse();
        Self::from_bytes_le(&le_bytes)
    }

    /// Converts an element of `Fp` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes_le(&self) -> [u8; 48] {
        let mut repr = [0u8; 48];
        unsafe { blst_lendian_from_fp(repr.as_mut_ptr(), &self.0) };
        repr
    }

    /// Converts an element of `Fp` into a byte representation in
    /// big-endian byte order.
    pub fn to_bytes_be(&self) -> [u8; 48] {
        let mut bytes = self.to_bytes_le();
        bytes.reverse();
        bytes
    }

    /// Constructs an element of `Fp` from a little-endian array of limbs
    /// without checking that it is canonical and without converting it to
    /// Montgomery form (i.e. without multiplying by `R`).
    pub(super) fn from_mont_unchecked(l: [u64; 6]) -> Fp {
        Fp(blst_fp { l })
    }

    /// `u64s` represent a little-endian non-Montgomery form integer mod p.
    pub fn from_u64s_le(bytes: &[u64; 6]) -> CtOption<Self> {
        let is_some = Choice::from(is_valid_u64(bytes) as u8);
        let mut out = blst_fp::default();
        unsafe { blst_fp_from_uint64(&mut out, bytes.as_ptr()) };
        CtOption::new(Fp(out), is_some)
    }

    /// Multiplies `self` with `3`, returning the result.
    pub fn mul3(&self) -> Self {
        let mut out = *self;
        unsafe { blst_fp_mul_by_3(&mut out.0, &self.0) };
        out
    }

    /// Multiplies `self` with `8`, returning the result.
    pub fn mul8(&self) -> Self {
        let mut out = *self;
        unsafe { blst_fp_mul_by_8(&mut out.0, &self.0) };
        out
    }

    /// Left shift `self` by `count`, returning the result.
    pub fn shl(&self, count: usize) -> Self {
        let mut out = *self;
        unsafe { blst_fp_lshift(&mut out.0, &self.0, count) };
        out
    }

    pub fn num_bits(&self) -> u32 {
        let mut ret = 384;
        for i in self.to_bytes_be().iter() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 8 {
                break;
            }
        }

        ret
    }

    // Returns the Jacobi symbol, where the numerator and denominator
    // are the element and the characteristic of the field, respectively.
    // The Jacobi symbol is applicable to odd moduli
    // while the Legendre symbol is applicable to prime moduli.
    // They are equivalent for prime moduli.
    #[inline(always)]
    fn jacobi(&self) -> i64 {
        let mut res = [0u64; 6];
        let bytes = self.to_bytes_le();
        res.iter_mut().enumerate().for_each(|(i, limb)| {
            let off = i * 8;
            *limb = u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap());
        });
        halo2curves::ff_ext::jacobi::jacobi::<7>(&res, &MODULUS)
    }

    #[inline]
    pub fn square_assign(&mut self) {
        unsafe { blst_fp_sqr(&mut self.0, &self.0) };
    }
}

// Wrapper needed, because we don't have Default implemented for [0u8; 48]
#[derive(Copy, Clone)]
pub struct FpRepr([u8; 48]);

impl From<[u8; 48]> for FpRepr {
    fn from(bytes: [u8; 48]) -> Self {
        Self(bytes)
    }
}

impl Default for FpRepr {
    fn default() -> Self {
        Self([0u8; 48])
    }
}

impl Deref for FpRepr {
    type Target = [u8; 48];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<[u8]> for FpRepr {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for FpRepr {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

/// `ZETA^3 = 1 mod r` where `ZETA^2 != 1 mod r`
// computed with sage math:
// R.<k>=PolynomialRing(GF(0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab))
// L=(k^3-1).roots();L
// We keep the first root for consistency with ZETA_SCALAR
pub const ZETA_BASE: Fp = Fp(blst_fp {
    l: [
        0xcd03_c9e4_8671_f071,
        0x5dab_2246_1fcd_a5d2,
        0x5870_42af_d385_1b95,
        0x8eb6_0ebe_01ba_cb9e,
        0x03f9_7d6e_83d0_50d2,
        0x18f0_2065_5463_8741,
    ],
});

/// 2^-1
const TWO_INV: Fp = Fp(blst_fp {
    l: [
        0x1804_0000_0001_5554,
        0x8550_0005_3ab0_0001,
        0x633c_b57c_253c_276f,
        0x6e22_d1ec_31eb_b502,
        0xd391_6126_f2d1_4ca2,
        0x17fb_b857_1a00_6596,
    ],
});

/// GENERATOR = 2.
/// Montgomery form:
/// 0x11ebab9dbb81e28c6cf28d7901622c038b256521ed1f9bcb57605e0db0ddbb51b93c0018d6c40005321300000006554f
const GENERATOR: Fp = Fp(blst_fp {
    l: [
        0x3213_0000_0006_554f,
        0xb93c_0018_d6c4_0005,
        0x5760_5e0d_b0dd_bb51,
        0x8b25_6521_ed1f_9bcb,
        0x6cf2_8d79_0162_2c03,
        0x11eb_ab9d_bb81_e28c,
    ],
});

impl halo2curves::ff_ext::Legendre for Fp {
    #[inline(always)]
    fn legendre(&self) -> i64 {
        self.jacobi()
    }
}
impl WithSmallOrderMulGroup<3> for Fp {
    const ZETA: Self = ZETA_BASE;
}

impl PrimeField for Fp {
    type Repr = FpRepr;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        Fp::from_bytes_le(&repr)
    }

    fn to_repr(&self) -> Self::Repr {
        FpRepr(self.to_bytes_le())
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }

    const MODULUS: &'static str = "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
    const NUM_BITS: u32 = NUM_BITS;
    const CAPACITY: u32 = Self::NUM_BITS - 1;
    const TWO_INV: Self = TWO_INV;
    const MULTIPLICATIVE_GENERATOR: Self = GENERATOR;
    const S: u32 = 0;

    // These constants are not needed for the base field.
    const ROOT_OF_UNITY: Self = Fp::ONE;
    const ROOT_OF_UNITY_INV: Self = Fp::ONE;
    const DELTA: Self = Fp::ZERO;
}

impl PrimeFieldBits for Fp {
    #[cfg(target_pointer_width = "64")]
    type ReprBits = [u64; NUM_LIMBS];
    #[cfg(not(target_pointer_width = "64"))]
    type ReprBits = [u32; 2 * NUM_LIMBS];

    fn to_le_bits(&self) -> ff::FieldBits<Self::ReprBits> {
        let bytes: [u8; 48] = self.to_repr().0;

        #[cfg(target_pointer_width = "64")]
        const STEP: usize = 8;
        #[cfg(not(target_pointer_width = "64"))]
        const STEP: usize = 4;

        let limbs = (0..NUM_LIMBS * 8 / STEP)
            .map(|off| {
                #[cfg(target_pointer_width = "64")]
                let limb =
                    u64::from_le_bytes(bytes[off * STEP..(off + 1) * STEP].try_into().unwrap());
                #[cfg(not(target_pointer_width = "64"))]
                let limb =
                    u32::from_le_bytes(bytes[off * STEP..(off + 1) * STEP].try_into().unwrap());

                limb
            })
            .collect::<Vec<_>>();

        ff::FieldBits::new(limbs.try_into().unwrap())
    }

    fn char_le_bits() -> ff::FieldBits<Self::ReprBits> {
        #[cfg(target_pointer_width = "64")]
        let bits = ff::FieldBits::new(MODULUS);
        #[cfg(not(target_pointer_width = "64"))]
        let bits = ff::FieldBits::new(MODULUS_32);

        bits
    }
}

impl SerdeObject for Fp {
    // Don't call this method with untrusted input. No checks performed before
    // unsafe block.
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), SIZE);
        let bytes: [u8; SIZE] = bytes.try_into().unwrap();
        let inner = u64s_from_bytes(&bytes);
        Fp(blst_fp { l: inner })
    }

    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != SIZE {
            return None;
        }
        Some(Self::from_raw_bytes_unchecked(bytes))
    }

    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(NUM_LIMBS * 8);
        for limb in self.0.l.iter() {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }

    // Don't call this method with untrusted input. No checks performed before
    // unsafe block.
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let mut bytes = [0u8; SIZE];
        reader
            .read_exact(&mut bytes)
            .unwrap_or_else(|_| panic!("Expected {} bytes.", SIZE));
        Self::from_raw_bytes_unchecked(&bytes)
    }

    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        use std::io::{Error, ErrorKind};
        let mut bytes = [0u8; SIZE];
        reader.read_exact(&mut bytes)?;
        let out = Self::from_raw_bytes(&bytes);
        if let Some(out) = out {
            Ok(out)
        } else {
            Err(Error::new(ErrorKind::InvalidData, "Invalid data."))
        }
    }

    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        for limb in self.0.l.iter() {
            writer.write_all(&limb.to_le_bytes())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fp_neg_one() {
        assert_eq!(
            -Fp::ONE,
            Fp(blst::blst_fp {
                l: [
                    0x43f5fffffffcaaae,
                    0x32b7fff2ed47fffd,
                    0x7e83a49a2e99d69,
                    0xeca8f3318332bb7a,
                    0xef148d1ea0f4c069,
                    0x40ab3263eff0206,
                ]
            }),
        );
    }

    #[test]
    fn test_fp_from_u64() {
        let a = Fp::from(100);
        let mut expected_bytes = [0u8; 48];
        expected_bytes[0] = 100;
        assert_eq!(a.to_bytes_le(), expected_bytes);
    }

    #[test]
    fn test_fp_is_zero() {
        assert!(bool::from(Fp::from(0).is_zero()));
        assert!(!bool::from(Fp::from(1).is_zero()));
        assert!(!bool::from(
            Fp::from_u64s_le(&[0, 0, 0, 0, 1, 0]).unwrap().is_zero()
        ));
    }

    #[test]
    fn test_fp_add_assign() {
        {
            // Random number
            let mut tmp = Fp(blst::blst_fp {
                l: [
                    0x624434821df92b69,
                    0x503260c04fd2e2ea,
                    0xd9df726e0d16e8ce,
                    0xfbcb39adfd5dfaeb,
                    0x86b8a22b0c88b112,
                    0x165a2ed809e4201b,
                ],
            });
            assert!(!bool::from(tmp.is_zero()));
            // Test that adding zero has no effect.
            tmp.add_assign(&Fp::from(0));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0x624434821df92b69,
                        0x503260c04fd2e2ea,
                        0xd9df726e0d16e8ce,
                        0xfbcb39adfd5dfaeb,
                        0x86b8a22b0c88b112,
                        0x165a2ed809e4201b
                    ]
                })
            );
            // Add one and test for the result.
            tmp.add_assign(&Fp(blst::blst_fp {
                l: [1, 0, 0, 0, 0, 0],
            }));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0x624434821df92b6a,
                        0x503260c04fd2e2ea,
                        0xd9df726e0d16e8ce,
                        0xfbcb39adfd5dfaeb,
                        0x86b8a22b0c88b112,
                        0x165a2ed809e4201b
                    ]
                })
            );
            // Add another random number that exercises the reduction.
            tmp.add_assign(&Fp(blst::blst_fp {
                l: [
                    0x374d8f8ea7a648d8,
                    0xe318bb0ebb8bfa9b,
                    0x613d996f0a95b400,
                    0x9fac233cb7e4fef1,
                    0x67e47552d253c52,
                    0x5c31b227edf25da,
                ],
            }));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0xdf92c410c59fc997,
                        0x149f1bd05a0add85,
                        0xd3ec393c20fba6ab,
                        0x37001165c1bde71d,
                        0x421b41c9f662408e,
                        0x21c38104f435f5b
                    ]
                })
            );
            // Add one to (q - 1) and test for the result.
            tmp = Fp(blst::blst_fp {
                l: [
                    0xb9feffffffffaaaa,
                    0x1eabfffeb153ffff,
                    0x6730d2a0f6b0f624,
                    0x64774b84f38512bf,
                    0x4b1ba7b6434bacd7,
                    0x1a0111ea397fe69a,
                ],
            });
            tmp.add_assign(&Fp(blst::blst_fp {
                l: [1, 0, 0, 0, 0, 0],
            }));
            assert!(bool::from(tmp.is_zero()));
            // Add a random number to another one such that the result is q - 1
            tmp = Fp(blst::blst_fp {
                l: [
                    0x531221a410efc95b,
                    0x72819306027e9717,
                    0x5ecefb937068b746,
                    0x97de59cd6feaefd7,
                    0xdc35c51158644588,
                    0xb2d176c04f2100,
                ],
            });
            tmp.add_assign(&Fp(blst::blst_fp {
                l: [
                    0x66ecde5bef0fe14f,
                    0xac2a6cf8aed568e8,
                    0x861d70d86483edd,
                    0xcc98f1b7839a22e8,
                    0x6ee5e2a4eae7674e,
                    0x194e40737930c599,
                ],
            }));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0xb9feffffffffaaaa,
                        0x1eabfffeb153ffff,
                        0x6730d2a0f6b0f624,
                        0x64774b84f38512bf,
                        0x4b1ba7b6434bacd7,
                        0x1a0111ea397fe69a
                    ]
                })
            );
            // Add one to the result and test for it.
            tmp.add_assign(&Fp(blst::blst_fp {
                l: [1, 0, 0, 0, 0, 0],
            }));
            assert!(bool::from(tmp.is_zero()));
        }

        // Test associativity

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Generate a, b, c and ensure (a + b) + c == a + (b + c).
            let a = Fp::random(&mut rng);
            let b = Fp::random(&mut rng);
            let c = Fp::random(&mut rng);

            let mut tmp1 = a;
            tmp1.add_assign(&b);
            tmp1.add_assign(&c);

            let mut tmp2 = b;
            tmp2.add_assign(&c);
            tmp2.add_assign(&a);

            // assert!(tmp1.is_valid());
            // assert!(tmp2.is_valid());
            assert_eq!(tmp1, tmp2);
        }
    }

    #[test]
    fn test_fp_sub_assign() {
        {
            // Test arbitrary subtraction that tests reduction.
            let mut tmp = Fp(blst::blst_fp {
                l: [
                    0x531221a410efc95b,
                    0x72819306027e9717,
                    0x5ecefb937068b746,
                    0x97de59cd6feaefd7,
                    0xdc35c51158644588,
                    0xb2d176c04f2100,
                ],
            });
            tmp.sub_assign(&Fp(blst::blst_fp {
                l: [
                    0x98910d20877e4ada,
                    0x940c983013f4b8ba,
                    0xf677dc9b8345ba33,
                    0xbef2ce6b7f577eba,
                    0xe1ae288ac3222c44,
                    0x5968bb602790806,
                ],
            }));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0x748014838971292c,
                        0xfd20fad49fddde5c,
                        0xcf87f198e3d3f336,
                        0x3d62d6e6e41883db,
                        0x45a3443cd88dc61b,
                        0x151d57aaf755ff94
                    ]
                })
            );

            // Test the opposite subtraction which doesn't test reduction.
            tmp = Fp(blst::blst_fp {
                l: [
                    0x98910d20877e4ada,
                    0x940c983013f4b8ba,
                    0xf677dc9b8345ba33,
                    0xbef2ce6b7f577eba,
                    0xe1ae288ac3222c44,
                    0x5968bb602790806,
                ],
            });
            tmp.sub_assign(&Fp(blst::blst_fp {
                l: [
                    0x531221a410efc95b,
                    0x72819306027e9717,
                    0x5ecefb937068b746,
                    0x97de59cd6feaefd7,
                    0xdc35c51158644588,
                    0xb2d176c04f2100,
                ],
            }));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0x457eeb7c768e817f,
                        0x218b052a117621a3,
                        0x97a8e10812dd02ed,
                        0x2714749e0f6c8ee3,
                        0x57863796abde6bc,
                        0x4e3ba3f4229e706
                    ]
                })
            );

            // Test for sensible results with zero
            tmp = Fp::from(0);
            tmp.sub_assign(&Fp::from(0));
            assert!(bool::from(tmp.is_zero()));

            tmp = Fp(blst::blst_fp {
                l: [
                    0x98910d20877e4ada,
                    0x940c983013f4b8ba,
                    0xf677dc9b8345ba33,
                    0xbef2ce6b7f577eba,
                    0xe1ae288ac3222c44,
                    0x5968bb602790806,
                ],
            });
            tmp.sub_assign(&Fp::from(0));
            assert_eq!(
                tmp,
                Fp(blst::blst_fp {
                    l: [
                        0x98910d20877e4ada,
                        0x940c983013f4b8ba,
                        0xf677dc9b8345ba33,
                        0xbef2ce6b7f577eba,
                        0xe1ae288ac3222c44,
                        0x5968bb602790806
                    ]
                })
            );
        }

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure that (a - b) + (b - a) = 0.
            let a = Fp::random(&mut rng);
            let b = Fp::random(&mut rng);

            let mut tmp1 = a;
            tmp1.sub_assign(&b);

            let mut tmp2 = b;
            tmp2.sub_assign(&a);

            tmp1.add_assign(&tmp2);
            assert!(bool::from(tmp1.is_zero()));
        }
    }

    #[test]
    fn test_fp_mul_assign() {
        assert_eq!(
            Fp(blst::blst_fp {
                l: [
                    0xcc6200000020aa8a,
                    0x422800801dd8001a,
                    0x7f4f5e619041c62c,
                    0x8a55171ac70ed2ba,
                    0x3f69cc3a3d07d58b,
                    0xb972455fd09b8ef,
                ]
            }) * Fp(blst::blst_fp {
                l: [
                    0x329300000030ffcf,
                    0x633c00c02cc40028,
                    0xbef70d925862a942,
                    0x4f7fa2a82a963c17,
                    0xdf1eb2575b8bc051,
                    0x1162b680fb8e9566,
                ]
            }),
            Fp(blst::blst_fp {
                l: [
                    0x9dc4000001ebfe14,
                    0x2850078997b00193,
                    0xa8197f1abb4d7bf,
                    0xc0309573f4bfe871,
                    0xf48d0923ffaf7620,
                    0x11d4b58c7a926e66
                ]
            })
        );

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000000 {
            // Ensure that (a * b) * c = a * (b * c)
            let a = Fp::random(&mut rng);
            let b = Fp::random(&mut rng);
            let c = Fp::random(&mut rng);

            let mut tmp1 = a;
            tmp1.mul_assign(&b);
            tmp1.mul_assign(&c);

            let mut tmp2 = b;
            tmp2.mul_assign(&c);
            tmp2.mul_assign(&a);

            assert_eq!(tmp1, tmp2);
        }

        for _ in 0..1000000 {
            // Ensure that r * (a + b + c) = r*a + r*b + r*c

            let r = Fp::random(&mut rng);
            let mut a = Fp::random(&mut rng);
            let mut b = Fp::random(&mut rng);
            let mut c = Fp::random(&mut rng);

            let mut tmp1 = a;
            tmp1.add_assign(&b);
            tmp1.add_assign(&c);
            tmp1.mul_assign(&r);

            a.mul_assign(&r);
            b.mul_assign(&r);
            c.mul_assign(&r);

            a.add_assign(&b);
            a.add_assign(&c);

            assert_eq!(tmp1, a);
        }
    }

    #[test]
    fn test_fp_squaring() {
        let a = Fp(blst::blst_fp {
            l: [
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0x19ffffffffffffff,
            ],
        });
        assert!(!bool::from(a.is_zero()));
        assert_eq!(
            a.square(),
            Fp::from_u64s_le(&[
                0x1cfb28fe7dfbbb86,
                0x24cbe1731577a59,
                0xcce1d4edc120e66e,
                0xdc05c659b4e15b27,
                0x79361e5a802c6a23,
                0x24bcbe5d51b9a6f
            ])
            .unwrap()
        );

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000000 {
            // Ensure that (a * a) = a^2
            let a = Fp::random(&mut rng);

            let tmp = a.square();

            let mut tmp2 = a;
            tmp2.mul_assign(&a);

            assert_eq!(tmp, tmp2);
        }
    }

    #[test]
    fn test_fp_inverse() {
        assert_eq!(Fp::ZERO.invert().is_none().unwrap_u8(), 1);

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let one = Fp::ONE;

        for _ in 0..1000 {
            // Ensure that a * a^-1 = 1
            let mut a = Fp::random(&mut rng);
            let ainv = a.invert().unwrap();
            a.mul_assign(&ainv);
            assert_eq!(a, one);
        }
    }

    #[test]
    fn test_fp_double() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure doubling a is equivalent to adding a to itself.
            let a = Fp::random(&mut rng);
            assert_eq!(a.double(), a + a, "{}", a);
        }
    }

    #[test]
    fn test_fp_negate() {
        {
            let a = Fp::ZERO;
            assert!(bool::from((-a).is_zero()));
        }

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure (a - (-a)) = 0.
            let mut a = Fp::random(&mut rng);
            let b = -a;
            a.add_assign(&b);

            assert!(bool::from(a.is_zero()));
        }
    }

    #[test]
    fn test_fp_pow() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..1000 {
            // Exponentiate by various small numbers and ensure it consists with repeated
            // multiplication.
            let a = Fp::random(&mut rng);
            let target = a.pow_vartime([i]);
            let mut c = Fp::ONE;
            for _ in 0..i {
                c.mul_assign(&a);
            }
            assert_eq!(c, target);
        }

        for _ in 0..1000 {
            // Exponentiating by the modulus should have no effect in a prime field.
            let a = Fp::random(&mut rng);

            assert_eq!(a, a.pow_vartime(MODULUS));
        }
    }

    #[test]
    fn test_fp_sqrt() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        assert_eq!(Fp::ZERO.sqrt().unwrap(), Fp::ZERO);
        assert_eq!(Fp::ONE.sqrt().unwrap(), Fp::ONE);

        for _ in 0..1000 {
            // Ensure sqrt(a^2) = a or -a
            let a = Fp::random(&mut rng);
            let a_new = a.square().sqrt().unwrap();
            assert!(a_new == a || a_new == -a);
        }

        for _ in 0..1000 {
            // Ensure sqrt(a)^2 = a for random a
            let a = Fp::random(&mut rng);
            let sqrt = a.sqrt();
            if sqrt.is_some().into() {
                assert_eq!(sqrt.unwrap().square(), a);
            }
        }
        // a = 4
        let a = Fp::from_mont_unchecked([
            0xaa27_0000_000c_fff3,
            0x53cc_0032_fc34_000a,
            0x478f_e97a_6b0a_807f,
            0xb1d3_7ebe_e6ba_24d7,
            0x8ec9_733b_bf78_ab2f,
            0x09d6_4551_3d83_de7e,
        ]);

        assert_eq!(
            // sqrt(4) = -2
            -a.sqrt().unwrap(),
            // 2
            Fp::from_mont_unchecked([
                0x3213_0000_0006_554f,
                0xb93c_0018_d6c4_0005,
                0x5760_5e0d_b0dd_bb51,
                0x8b25_6521_ed1f_9bcb,
                0x6cf2_8d79_0162_2c03,
                0x11eb_ab9d_bb81_e28c,
            ])
        );
    }

    #[test]
    fn test_fp_from_into_repr() {
        // q + 1 should not be in the field
        assert!(bool::from(
            Fp::from_u64s_le(&[
                0xb9feffffffffaaac,
                0x1eabfffeb153ffff,
                0x6730d2a0f6b0f624,
                0x64774b84f38512bf,
                0x4b1ba7b6434bacd7,
                0x1a0111ea397fe69a
            ])
            .is_none()
        ));

        // Multiply some arbitrary representations to see if the result is as expected.
        let mut a = Fp::from_u64s_le(&[
            0x4a49dad4ff6cde2d,
            0xac62a82a8f51cd50,
            0x2b1f41ab9f36d640,
            0x908a387f480735f1,
            0xae30740c08a875d7,
            0x6c80918a365ef78,
        ])
        .unwrap();
        let b = Fp::from_u64s_le(&[
            0xbba57917c32f0cf0,
            0xe7f878cf87f05e5d,
            0x9498b4292fd27459,
            0xd59fd94ee4572cfa,
            0x1f607186d5bb0059,
            0xb13955f5ac7f6a3,
        ])
        .unwrap();
        let c = Fp::from_u64s_le(&[
            0xf5f70713b717914c,
            0x355ea5ac64cbbab1,
            0xce60dd43417ec960,
            0xf16b9d77b0ad7d10,
            0xa44c204c1de7cdb7,
            0x1684487772bc9a5a,
        ])
        .unwrap();
        a.mul_assign(&b);
        assert_eq!(a, c);

        // Zero should be in the field.
        assert!(bool::from(Fp::from(0).is_zero()));

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Try to turn Fp elements into representations and back again, and compare.
            let a = Fp::random(&mut rng);
            let a_repr = a.to_bytes_le();
            let b = Fp::from_bytes_le(&a_repr).unwrap();
            let b_repr = b.to_bytes_le();
            assert_eq!(a, b);
            assert_eq!(a_repr, b_repr);
        }
    }

    #[test]
    fn test_fp_display() {
        assert_eq!(
            format!("{}", Fp::from_u64s_le(&[
                0xa956babf9301ea24,
                0x39a8f184f3535c7b,
                0xb38d35b3f6779585,
                0x676cc4eef4c46f2c,
                0xb1d4aad87651e694,
                0x1947f0d5f4fe325a
            ])
            .unwrap()),
            "Fp(0x1947f0d5f4fe325ab1d4aad87651e694676cc4eef4c46f2cb38d35b3f677958539a8f184f3535c7ba956babf9301ea24)".to_string()
        );

        assert_eq!(
            format!("{}", Fp::from_u64s_le(&[
               0xe28e79396ac2bbf8,
               0x413f6f7f06ea87eb,
               0xa4b62af4a792a689,
               0xb7f89f88f59c1dc5,
               0x9a551859b1e43a9a,
               0x6c9f5a1060de974
            ])
            .unwrap()),
            "Fp(0x06c9f5a1060de9749a551859b1e43a9ab7f89f88f59c1dc5a4b62af4a792a689413f6f7f06ea87ebe28e79396ac2bbf8)".to_string()
        );
    }

    #[test]
    fn test_fp_num_bits() {
        assert_eq!(NUM_BITS, 381);

        let mut a = Fp::from(0);
        assert_eq!(0, a.num_bits());
        a = Fp::from(1);
        assert_eq!(1, a.num_bits());
        for i in 2..NUM_BITS {
            a = a.shl(1);
            assert_eq!(i, a.num_bits());
        }
    }

    #[test]
    fn fp_field_tests() {
        crate::tests::field::random_field_tests::<Fp>();
        crate::tests::field::random_sqrt_tests::<Fp>();
    }

    #[test]
    fn test_fp_ordering() {
        // FpRepr's ordering is well-tested, but we still need to make sure the Fp
        // elements aren't being compared in Montgomery form.
        for i in 0..100 {
            let a = Fp::from(i + 1);
            let b = Fp::from(i);
            assert!(a > b, "{}: {:?} > {:?}", i, a, b);
        }
    }

    #[test]
    fn test_inversion() {
        let a = Fp::from_mont_unchecked([
            0x43b4_3a50_78ac_2076,
            0x1ce0_7630_46f8_962b,
            0x724a_5276_486d_735c,
            0x6f05_c2a6_282d_48fd,
            0x2095_bd5b_b4ca_9331,
            0x03b3_5b38_94b0_f7da,
        ]);
        let b = Fp::from_mont_unchecked([
            0x69ec_d704_0952_148f,
            0x985c_cc20_2219_0f55,
            0xe19b_ba36_a9ad_2f41,
            0x19bb_16c9_5219_dbd8,
            0x14dc_acfd_fb47_8693,
            0x115f_f58a_fff9_a8e1,
        ]);

        assert_eq!(a.invert().unwrap(), b);
        assert!(bool::from(Fp::ZERO.invert().is_none()));
    }

    crate::field_testing_suite!(Fp, "field_arithmetic");
    crate::field_testing_suite!(Fp, "conversion");
    crate::field_testing_suite!(Fp, "quadratic_residue");
    crate::field_testing_suite!(Fp, "bits");
    crate::field_testing_suite!(Fp, "serdeobject");
    crate::field_testing_suite!(Fp, "constants");
    crate::field_testing_suite!(Fp, "sqrt");
    crate::field_testing_suite!(Fp, "zeta");
}

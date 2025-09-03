//! This module implements arithmetic over the quadratic extension field Fp12.

use core::{
    fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use blst::*;
use ff::Field;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{fp::Fp, fp2::Fp2, fp6::Fp6};

/// This represents an element $c_0 + c_1 w$ of $\mathbb{F}_{p^12} =
/// \mathbb{F}_{p^6} / w^2 - v$.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct Fp12(pub(crate) blst_fp12);

impl fmt::Debug for Fp12 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Fp12")
            .field("c0", &self.c0())
            .field("c1", &self.c1())
            .finish()
    }
}

impl fmt::Display for Fp12 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} + {:?}*u", self.c0(), self.c1())
    }
}

impl core::hash::Hash for Fp12 {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        for i in 0..2 {
            for j in 0..3 {
                for k in 0..2 {
                    self.0.fp6[i].fp2[j].fp[k].l.hash::<H>(state);
                }
            }
        }
    }
}

impl From<Fp> for Fp12 {
    fn from(f: Fp) -> Fp12 {
        Fp12::new(Fp6::from(f), Fp6::ZERO)
    }
}

impl From<Fp2> for Fp12 {
    fn from(f: Fp2) -> Fp12 {
        Fp12::new(Fp6::from(f), Fp6::ZERO)
    }
}

impl From<Fp6> for Fp12 {
    fn from(f: Fp6) -> Fp12 {
        Fp12::new(f, Fp6::ZERO)
    }
}

impl From<blst_fp12> for Fp12 {
    fn from(val: blst_fp12) -> Fp12 {
        Fp12(val)
    }
}

impl From<Fp12> for blst_fp12 {
    fn from(val: Fp12) -> blst_fp12 {
        val.0
    }
}

impl ConstantTimeEq for Fp12 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0().ct_eq(&other.c0()) & self.c1().ct_eq(&other.c1())
    }
}

impl ConditionallySelectable for Fp12 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp12(blst_fp12 {
            fp6: [
                Fp6::conditional_select(&a.c0(), &b.c0(), choice).0,
                Fp6::conditional_select(&a.c1(), &b.c1(), choice).0,
            ],
        })
    }
}

impl Default for Fp12 {
    fn default() -> Self {
        Fp12::ZERO
    }
}

macro_rules! op {
    ($lhs:expr, $op:expr, $rhs:expr) => {
        unsafe {
            $op(
                &mut $lhs.0.fp6[0].fp2[0],
                &$lhs.0.fp6[0].fp2[0],
                &$rhs.0.fp6[0].fp2[0],
            );
            $op(
                &mut $lhs.0.fp6[0].fp2[1],
                &$lhs.0.fp6[0].fp2[1],
                &$rhs.0.fp6[0].fp2[1],
            );
            $op(
                &mut $lhs.0.fp6[0].fp2[2],
                &$lhs.0.fp6[0].fp2[2],
                &$rhs.0.fp6[0].fp2[2],
            );
            $op(
                &mut $lhs.0.fp6[1].fp2[0],
                &$lhs.0.fp6[1].fp2[0],
                &$rhs.0.fp6[1].fp2[0],
            );
            $op(
                &mut $lhs.0.fp6[1].fp2[1],
                &$lhs.0.fp6[1].fp2[1],
                &$rhs.0.fp6[1].fp2[1],
            );
            $op(
                &mut $lhs.0.fp6[1].fp2[2],
                &$lhs.0.fp6[1].fp2[2],
                &$rhs.0.fp6[1].fp2[2],
            );
        }
    };
}

impl Neg for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn neg(self) -> Fp12 {
        -*self
    }
}

impl Neg for Fp12 {
    type Output = Fp12;

    #[inline]
    fn neg(mut self) -> Fp12 {
        unsafe {
            blst_fp2_cneg(&mut self.0.fp6[0].fp2[0], &self.0.fp6[0].fp2[0], true);
            blst_fp2_cneg(&mut self.0.fp6[0].fp2[1], &self.0.fp6[0].fp2[1], true);
            blst_fp2_cneg(&mut self.0.fp6[0].fp2[2], &self.0.fp6[0].fp2[2], true);
            blst_fp2_cneg(&mut self.0.fp6[1].fp2[0], &self.0.fp6[1].fp2[0], true);
            blst_fp2_cneg(&mut self.0.fp6[1].fp2[1], &self.0.fp6[1].fp2[1], true);
            blst_fp2_cneg(&mut self.0.fp6[1].fp2[2], &self.0.fp6[1].fp2[2], true);
        }
        self
    }
}

impl Sub<&Fp12> for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn sub(self, rhs: &Fp12) -> Fp12 {
        let mut out = *self;
        out -= rhs;
        out
    }
}

impl Add<&Fp12> for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn add(self, rhs: &Fp12) -> Fp12 {
        let mut out = *self;
        out += rhs;
        out
    }
}

impl Mul<&Fp12> for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn mul(self, rhs: &Fp12) -> Fp12 {
        let mut out = blst_fp12::default();
        unsafe { blst_fp12_mul(&mut out, &self.0, &rhs.0) };
        Fp12(out)
    }
}

impl AddAssign<&Fp12> for Fp12 {
    #[inline]
    fn add_assign(&mut self, rhs: &Fp12) {
        op!(self, blst_fp2_add, rhs);
    }
}

impl SubAssign<&Fp12> for Fp12 {
    #[inline]
    fn sub_assign(&mut self, rhs: &Fp12) {
        op!(self, blst_fp2_sub, rhs);
    }
}

impl MulAssign<&Fp12> for Fp12 {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fp12) {
        unsafe { blst_fp12_mul(&mut self.0, &self.0, &rhs.0) };
    }
}

impl_add_sub!(Fp12);
impl_add_sub_assign!(Fp12);
impl_mul!(Fp12);
impl_mul_assign!(Fp12);
impl_sum!(Fp12);
impl_product!(Fp12);

impl Field for Fp12 {
    fn random(mut rng: impl RngCore) -> Self {
        Fp12::new(Fp6::random(&mut rng), Fp6::random(&mut rng))
    }

    const ZERO: Self = Fp12::new(Fp6::ZERO, Fp6::ZERO);

    const ONE: Self = Fp12::new(Fp6::ONE, Fp6::ZERO);

    fn is_zero(&self) -> Choice {
        self.c0().is_zero() & self.c1().is_zero()
    }

    fn double(&self) -> Self {
        let mut out = *self;
        out += self;
        out
    }

    fn square(&self) -> Self {
        let mut sq = *self;
        unsafe { blst_fp12_sqr(&mut sq.0, &self.0) };
        sq
    }

    fn invert(&self) -> CtOption<Self> {
        let is_zero = self.ct_eq(&Self::ZERO);
        let mut inv = *self;
        unsafe { blst_fp12_inverse(&mut inv.0, &self.0) }
        CtOption::new(inv, !is_zero)
    }

    fn sqrt(&self) -> CtOption<Self> {
        unimplemented!()
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        // ff::helpers::sqrt_ratio_generic(num, div)
        unimplemented!()
    }
}

impl Fp12 {
    /// Constructs an element of `Fp12`.
    pub const fn new(c0: Fp6, c1: Fp6) -> Fp12 {
        Fp12(blst_fp12 { fp6: [c0.0, c1.0] })
    }

    pub fn frobenius_map(&mut self, power: usize) {
        if power > 0 && power < 4 {
            unsafe { blst_fp12_frobenius_map(&mut self.0, &self.0, power) }
        } else {
            let mut c0 = self.c0();
            c0.frobenius_map(power);
            let mut c1 = self.c1();
            c1.frobenius_map(power);

            let mut c0_raw = blst_fp2::default();
            let mut c1_raw = blst_fp2::default();
            let mut c2_raw = blst_fp2::default();
            unsafe {
                blst_fp2_mul(
                    &mut c0_raw,
                    &c1.0.fp2[0],
                    &FROBENIUS_COEFF_FP12_C1[power % 12],
                );
                blst_fp2_mul(
                    &mut c1_raw,
                    &c1.0.fp2[1],
                    &FROBENIUS_COEFF_FP12_C1[power % 12],
                );
                blst_fp2_mul(
                    &mut c2_raw,
                    &c1.0.fp2[2],
                    &FROBENIUS_COEFF_FP12_C1[power % 12],
                );
            }
            c1.0.fp2 = [c0_raw, c1_raw, c2_raw];

            self.0.fp6 = [c0.0, c1.0];
        }
    }

    pub fn c0(&self) -> Fp6 {
        Fp6(self.0.fp6[0])
    }

    pub fn c1(&self) -> Fp6 {
        Fp6(self.0.fp6[1])
    }

    pub fn conjugate(&mut self) {
        unsafe { blst_fp12_conjugate(&mut self.0) };
    }
}

// non_residue^((modulus^i-1)/6) for i=0,...,11
const FROBENIUS_COEFF_FP12_C1: [blst_fp2; 12] = [
    // Fp2(u + 1)**(((q^0) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x760900000002fffd,
                    0xebf4000bc40c0002,
                    0x5f48985753c758ba,
                    0x77ce585370525745,
                    0x5c071a97a256ec6d,
                    0x15f65ec3fa80e493,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^1) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x7089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0xa35baecab2dc29ee,
                    0x1ce393ea5daace4d,
                    0x8f2220fb0fb66eb,
                ],
            },
            blst_fp {
                l: [
                    0xb2f66aad4ce5d646,
                    0x5842a06bfc497cec,
                    0xcf4895d42599d394,
                    0xc11b9cba40a8e8d0,
                    0x2e3813cbe5a0de89,
                    0x110eefda88847faf,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^2) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0xecfb361b798dba3a,
                    0xc100ddb891865a2c,
                    0xec08ff1232bda8e,
                    0xd5c13cc6f1ca4721,
                    0x47222a47bf7b5c04,
                    0x110f184e51c5f59,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^3) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x3e2f585da55c9ad1,
                    0x4294213d86c18183,
                    0x382844c88b623732,
                    0x92ad2afd19103e18,
                    0x1d794e4fac7cf0b9,
                    0xbd592fc7d825ec8,
                ],
            },
            blst_fp {
                l: [
                    0x7bcfa7a25aa30fda,
                    0xdc17dec12a927e7c,
                    0x2f088dd86b4ebef1,
                    0xd1ca2087da74d4a7,
                    0x2da2596696cebc1d,
                    0xe2b7eedbbfd87d2,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^4) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x30f1361b798a64e8,
                    0xf3b8ddab7ece5a2a,
                    0x16a8ca3ac61577f7,
                    0xc26a2ff874fd029b,
                    0x3636b76660701c6e,
                    0x51ba4ab241b6160,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^5) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x3726c30af242c66c,
                    0x7c2ac1aad1b6fe70,
                    0xa04007fbba4b14a2,
                    0xef517c3266341429,
                    0x95ba654ed2226b,
                    0x2e370eccc86f7dd,
                ],
            },
            blst_fp {
                l: [
                    0x82d83cf50dbce43f,
                    0xa2813e53df9d018f,
                    0xc6f0caa53c65e181,
                    0x7525cf528d50fe95,
                    0x4a85ed50f4798a6b,
                    0x171da0fd6cf8eebd,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^6) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x43f5fffffffcaaae,
                    0x32b7fff2ed47fffd,
                    0x7e83a49a2e99d69,
                    0xeca8f3318332bb7a,
                    0xef148d1ea0f4c069,
                    0x40ab3263eff0206,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^7) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0xb2f66aad4ce5d646,
                    0x5842a06bfc497cec,
                    0xcf4895d42599d394,
                    0xc11b9cba40a8e8d0,
                    0x2e3813cbe5a0de89,
                    0x110eefda88847faf,
                ],
            },
            blst_fp {
                l: [
                    0x7089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0xa35baecab2dc29ee,
                    0x1ce393ea5daace4d,
                    0x8f2220fb0fb66eb,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^8) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0xcd03c9e48671f071,
                    0x5dab22461fcda5d2,
                    0x587042afd3851b95,
                    0x8eb60ebe01bacb9e,
                    0x3f97d6e83d050d2,
                    0x18f0206554638741,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^9) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x7bcfa7a25aa30fda,
                    0xdc17dec12a927e7c,
                    0x2f088dd86b4ebef1,
                    0xd1ca2087da74d4a7,
                    0x2da2596696cebc1d,
                    0xe2b7eedbbfd87d2,
                ],
            },
            blst_fp {
                l: [
                    0x3e2f585da55c9ad1,
                    0x4294213d86c18183,
                    0x382844c88b623732,
                    0x92ad2afd19103e18,
                    0x1d794e4fac7cf0b9,
                    0xbd592fc7d825ec8,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^10) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x890dc9e4867545c3,
                    0x2af322533285a5d5,
                    0x50880866309b7e2c,
                    0xa20d1b8c7e881024,
                    0x14e4f04fe2db9068,
                    0x14e56d3f1564853a,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^11) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x82d83cf50dbce43f,
                    0xa2813e53df9d018f,
                    0xc6f0caa53c65e181,
                    0x7525cf528d50fe95,
                    0x4a85ed50f4798a6b,
                    0x171da0fd6cf8eebd,
                ],
            },
            blst_fp {
                l: [
                    0x3726c30af242c66c,
                    0x7c2ac1aad1b6fe70,
                    0xa04007fbba4b14a2,
                    0xef517c3266341429,
                    0x95ba654ed2226b,
                    0x2e370eccc86f7dd,
                ],
            },
        ],
    },
];

#[cfg(test)]
mod tests {
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    #[test]
    fn test_fp12_eq() {
        assert_eq!(Fp12::ONE, Fp12::ONE);
        assert_eq!(Fp12::ZERO, Fp12::ZERO);
        assert_ne!(Fp12::ZERO, Fp12::ONE);
    }

    #[test]
    fn fp12_random_frobenius_tests() {
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
                let mut a = Fp12::random(&mut rng);
                let mut b = a;

                for _ in 0..i {
                    a = a.pow_vartime(&characteristic);
                }
                b.frobenius_map(i);

                assert_eq!(a, b, "{}", i);
            }
        }
    }

    #[test]
    fn fp12_random_field_tests() {
        crate::tests::field::random_field_tests::<Fp12>();
    }
}

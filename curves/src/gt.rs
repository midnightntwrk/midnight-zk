use core::{
    borrow::Borrow,
    fmt,
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use blst::*;
use ff::Field;
use group::Group;
use rand_core::RngCore;
use subtle::{Choice, ConstantTimeEq};

use crate::{fp::Fp, fp12::Fp12, fp2::Fp2, fp6::Fp6, Fq};

/// This is an element of $\mathbb{G}_T$, the target group of the pairing
/// function. As with $\mathbb{G}_1$ and $\mathbb{G}_2$ this group has order
/// $q$.
///
/// Typically, $\mathbb{G}_T$ is written multiplicatively but we will write it
/// additively to keep code and abstractions consistent.
#[derive(Copy, Clone, Debug, Default)]
#[repr(transparent)]
pub struct Gt(pub(crate) Fp12);

impl fmt::Display for Gt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl core::hash::Hash for Gt {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.hash::<H>(state)
    }
}

impl From<Fp12> for Gt {
    fn from(fp12: Fp12) -> Self {
        Gt(fp12)
    }
}

impl From<Gt> for Fp12 {
    fn from(gt: Gt) -> Self {
        gt.0
    }
}

impl Eq for Gt {}

impl PartialEq for Gt {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Neg for &Gt {
    type Output = Gt;

    #[inline]
    fn neg(self) -> Gt {
        // The element is unitary, so we just conjugate.
        let mut res = *self;
        res.0.conjugate();
        res
    }
}

impl Neg for Gt {
    type Output = Gt;

    #[inline]
    fn neg(self) -> Gt {
        -&self
    }
}

impl Add<&Gt> for &Gt {
    type Output = Gt;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: &Gt) -> Gt {
        Gt(self.0 * rhs.0)
    }
}

impl Sub<&Gt> for &Gt {
    type Output = Gt;

    #[inline]
    fn sub(self, rhs: &Gt) -> Gt {
        self + (-rhs)
    }
}

impl Mul<&Fq> for &Gt {
    type Output = Gt;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, scalar: &Fq) -> Self::Output {
        let mut acc = Gt::identity();

        // This is a simple double-and-add implementation of group element
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading bit because it's always unset for Fq
        // elements.
        for bit in scalar
            .to_bytes_be()
            .iter()
            .flat_map(|byte| (0..8).rev().map(move |i| (byte >> i) & 1 == 1))
            .skip(1)
        {
            acc = acc.double();
            if bit {
                acc += self;
            }
        }

        acc
    }
}

impl AddAssign<&Gt> for Gt {
    #[inline]
    fn add_assign(&mut self, rhs: &Gt) {
        *self = *self + rhs;
    }
}

impl SubAssign<&Gt> for Gt {
    #[inline]
    fn sub_assign(&mut self, rhs: &Gt) {
        *self = *self - rhs;
    }
}

impl MulAssign<&Fq> for Gt {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fq) {
        *self = *self * rhs;
    }
}

impl_add_sub!(Gt);
impl_add_sub_assign!(Gt);
impl_mul!(Gt, Fq);
impl_mul_assign!(Gt, Fq);

impl<T> Sum<T> for Gt
where
    T: Borrow<Gt>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl Group for Gt {
    type Scalar = Fq;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let mut out = Fp12::random(&mut rng);

            // Not all elements of Fp12 are elements of the prime-order multiplicative
            // subgroup. We run the random element through final_exponentiation to obtain
            // a valid element, which requires that it is non-zero.
            if !bool::from(out.is_zero()) {
                unsafe { blst_final_exp(&mut out.0, &out.0) };
                return Gt(out);
            }
        }
    }

    /// Returns the group identity, which is $1$.
    fn identity() -> Self {
        Gt(Fp12::ONE)
    }

    fn generator() -> Self {
        // pairing(&G1Affine::generator(), &G2Affine::generator())
        Gt(Fp12::new(
            Fp6::new(
                Fp2::new(
                    Fp::from_mont_unchecked([
                        0x1972_e433_a01f_85c5,
                        0x97d3_2b76_fd77_2538,
                        0xc8ce_546f_c96b_cdf9,
                        0xcef6_3e73_66d4_0614,
                        0xa611_3427_8184_3780,
                        0x13f3_448a_3fc6_d825,
                    ]),
                    Fp::from_mont_unchecked([
                        0xd263_31b0_2e9d_6995,
                        0x9d68_a482_f779_7e7d,
                        0x9c9b_2924_8d39_ea92,
                        0xf480_1ca2_e131_07aa,
                        0xa16c_0732_bdbc_b066,
                        0x083c_a4af_ba36_0478,
                    ]),
                ),
                Fp2::new(
                    Fp::from_mont_unchecked([
                        0x59e2_61db_0916_b641,
                        0x2716_b6f4_b23e_960d,
                        0xc8e5_5b10_a0bd_9c45,
                        0x0bdb_0bd9_9c4d_eda8,
                        0x8cf8_9ebf_57fd_aac5,
                        0x12d6_b792_9e77_7a5e,
                    ]),
                    Fp::from_mont_unchecked([
                        0x5fc8_5188_b0e1_5f35,
                        0x34a0_6e3a_8f09_6365,
                        0xdb31_26a6_e02a_d62c,
                        0xfc6f_5aa9_7d9a_990b,
                        0xa12f_55f5_eb89_c210,
                        0x1723_703a_926f_8889,
                    ]),
                ),
                Fp2::new(
                    Fp::from_mont_unchecked([
                        0x9358_8f29_7182_8778,
                        0x43f6_5b86_11ab_7585,
                        0x3183_aaf5_ec27_9fdf,
                        0xfa73_d7e1_8ac9_9df6,
                        0x64e1_76a6_a64c_99b0,
                        0x179f_a78c_5838_8f1f,
                    ]),
                    Fp::from_mont_unchecked([
                        0x672a_0a11_ca2a_ef12,
                        0x0d11_b9b5_2aa3_f16b,
                        0xa444_12d0_699d_056e,
                        0xc01d_0177_221a_5ba5,
                        0x66e0_cede_6c73_5529,
                        0x05f5_a71e_9fdd_c339,
                    ]),
                ),
            ),
            Fp6::new(
                Fp2::new(
                    Fp::from_mont_unchecked([
                        0xd30a_88a1_b062_c679,
                        0x5ac5_6a5d_35fc_8304,
                        0xd0c8_34a6_a81f_290d,
                        0xcd54_30c2_da37_07c7,
                        0xf0c2_7ff7_8050_0af0,
                        0x0924_5da6_e2d7_2eae,
                    ]),
                    Fp::from_mont_unchecked([
                        0x9f2e_0676_791b_5156,
                        0xe2d1_c823_4918_fe13,
                        0x4c9e_459f_3c56_1bf4,
                        0xa3e8_5e53_b9d3_e3c1,
                        0x820a_121e_21a7_0020,
                        0x15af_6183_41c5_9acc,
                    ]),
                ),
                Fp2::new(
                    Fp::from_mont_unchecked([
                        0x7c95_658c_2499_3ab1,
                        0x73eb_3872_1ca8_86b9,
                        0x5256_d749_4774_34bc,
                        0x8ba4_1902_ea50_4a8b,
                        0x04a3_d3f8_0c86_ce6d,
                        0x18a6_4a87_fb68_6eaa,
                    ]),
                    Fp::from_mont_unchecked([
                        0xbb83_e71b_b920_cf26,
                        0x2a52_77ac_92a7_3945,
                        0xfc0e_e59f_94f0_46a0,
                        0x7158_cdf3_7860_58f7,
                        0x7cc1_061b_82f9_45f6,
                        0x03f8_47aa_9fdb_e567,
                    ]),
                ),
                Fp2::new(
                    Fp::from_mont_unchecked([
                        0x8078_dba5_6134_e657,
                        0x1cd7_ec9a_4399_8a6e,
                        0xb1aa_599a_1a99_3766,
                        0xc9a0_f62f_0842_ee44,
                        0x8e15_9be3_b605_dffa,
                        0x0c86_ba0d_4af1_3fc2,
                    ]),
                    Fp::from_mont_unchecked([
                        0xe80f_f2a0_6a52_ffb1,
                        0x7694_ca48_721a_906c,
                        0x7583_183e_03b0_8514,
                        0xf567_afdd_40ce_e4e2,
                        0x9a6d_96d2_e526_a5fc,
                        0x197e_9f49_861f_2242,
                    ]),
                ),
            ),
        ))
    }

    fn is_identity(&self) -> Choice {
        self.0.ct_eq(&Self::identity().0)
    }

    #[must_use]
    fn double(&self) -> Self {
        Gt(self.0.square())
    }
}

#[cfg(test)]
impl Gt {
    fn is_in_subgroup(&self) -> bool {
        unsafe { blst_fp12_in_group(&(self.0).0) }
    }
}

#[cfg(test)]
mod tests {
    use group::{prime::PrimeCurveAffine, Curve};
    use pairing_lib::{Engine, MillerLoopResult, MultiMillerLoop};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;
    use crate::{pairing, Bls12, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective};

    #[test]
    fn test_gt_generator() {
        assert_eq!(
            Gt::generator(),
            pairing(&G1Affine::generator(), &G2Affine::generator()),
        );
    }

    #[test]
    fn test_gt_bilinearity() {
        use crate::Fq;

        let a = Fq::from_u64s_le(&[1, 2, 3, 4])
            .unwrap()
            .invert()
            .unwrap()
            .square();
        let b = Fq::from_u64s_le(&[5, 6, 7, 8])
            .unwrap()
            .invert()
            .unwrap()
            .square();
        let c = a * b;

        let g = G1Affine::from(G1Affine::generator() * a);
        let h = G2Affine::from(G2Affine::generator() * b);
        let p = pairing(&g, &h);

        assert_ne!(p, Gt::identity());
        assert_eq!(
            p,
            pairing(
                &G1Affine::from(G1Affine::generator() * c),
                &G2Affine::generator()
            ),
        );
        assert_eq!(
            p,
            pairing(&G1Affine::generator(), &G2Affine::generator()) * c
        );
    }

    #[test]
    fn test_gt_unitary() {
        let g = G1Affine::generator();
        let h = G2Affine::generator();
        let p = -pairing(&g, &h);
        let q = pairing(&g, &-h);
        let r = pairing(&-g, &h);

        assert_eq!(p, q);
        assert_eq!(q, r);
    }

    #[test]
    fn test_multi_miller_loop() {
        let a1 = G1Affine::generator();
        let b1 = G2Affine::generator();

        let a2 = G1Affine::from(
            G1Affine::generator()
                * Fq::from_u64s_le(&[1, 2, 3, 4])
                    .unwrap()
                    .invert()
                    .unwrap()
                    .square(),
        );
        let b2 = G2Affine::from(
            G2Affine::generator()
                * Fq::from_u64s_le(&[4, 2, 2, 4])
                    .unwrap()
                    .invert()
                    .unwrap()
                    .square(),
        );

        let a3 = G1Affine::identity();
        let b3 = G2Affine::from(
            G2Affine::generator()
                * Fq::from_u64s_le(&[9, 2, 2, 4])
                    .unwrap()
                    .invert()
                    .unwrap()
                    .square(),
        );

        let a4 = G1Affine::from(
            G1Affine::generator()
                * Fq::from_u64s_le(&[5, 5, 5, 5])
                    .unwrap()
                    .invert()
                    .unwrap()
                    .square(),
        );
        let b4 = G2Affine::identity();

        let a5 = G1Affine::from(
            G1Affine::generator()
                * Fq::from_u64s_le(&[323, 32, 3, 1])
                    .unwrap()
                    .invert()
                    .unwrap()
                    .square(),
        );
        let b5 = G2Affine::from(
            G2Affine::generator()
                * Fq::from_u64s_le(&[4, 2, 2, 9099])
                    .unwrap()
                    .invert()
                    .unwrap()
                    .square(),
        );

        let b1_prepared = G2Prepared::from(b1);
        let b2_prepared = G2Prepared::from(b2);
        let b3_prepared = G2Prepared::from(b3);
        let b4_prepared = G2Prepared::from(b4);
        let b5_prepared = G2Prepared::from(b5);

        let expected = Bls12::pairing(&a1, &b1)
            + Bls12::pairing(&a2, &b2)
            + Bls12::pairing(&a3, &b3)
            + Bls12::pairing(&a4, &b4)
            + Bls12::pairing(&a5, &b5);

        let test = <Bls12 as MultiMillerLoop>::multi_miller_loop(&[
            (&a1, &b1_prepared),
            (&a2, &b2_prepared),
            (&a3, &b3_prepared),
            (&a4, &b4_prepared),
            (&a5, &b5_prepared),
        ])
        .final_exponentiation();

        assert_eq!(expected, test);
    }

    #[test]
    fn gt_subgroup() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let p = G1Projective::random(&mut rng).to_affine();
        let q = G2Projective::random(&mut rng).to_affine();
        let a = crate::pairing(&p, &q);
        assert!(a.is_in_subgroup());
    }
}

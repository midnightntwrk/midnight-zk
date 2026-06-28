use core::{
    borrow::Borrow,
    iter::Sum,
    ops::{Add, Mul, Neg, Sub},
};
use std::ops::MulAssign;

use ff::PrimeField;
use group::{cofactor::CofactorCurveAffine, Group};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use crate::bn256::{
    curve::*, ext_field::quadratic::QuadSparseMul, fq::*, fq12::*, fq2::*,
    fq6::FROBENIUS_COEFF_FQ6_C1, fr::*, ExtField,
};

#[derive(Copy, Clone, Debug, Default)]
pub struct Gt(pub(crate) Fq12);

impl ConstantTimeEq for Gt {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for Gt {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Gt(Fq12::conditional_select(&a.0, &b.0, choice))
    }
}

impl Eq for Gt {}
impl PartialEq for Gt {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl Gt {
    /// Returns the group identity, which is $1$.
    pub fn identity() -> Gt {
        Gt(Fq12::one())
    }

    /// Doubles this group element.
    pub fn double(&self) -> Gt {
        use ff::Field;
        Gt(self.0.square())
    }
}

impl Neg for &Gt {
    type Output = Gt;

    #[inline]
    fn neg(self) -> Gt {
        // The element is unitary, so we just conjugate.
        let mut u = self.0;
        u.conjugate();
        Gt(u)
    }
}

impl Neg for Gt {
    type Output = Gt;

    #[inline]
    fn neg(self) -> Gt {
        -&self
    }
}

impl<'b> Add<&'b Gt> for &Gt {
    type Output = Gt;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: &'b Gt) -> Gt {
        Gt(self.0 * rhs.0)
    }
}

impl<'b> Sub<&'b Gt> for &Gt {
    type Output = Gt;

    #[inline]
    fn sub(self, rhs: &'b Gt) -> Gt {
        self + (-rhs)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<'b> Mul<&'b Fr> for &Gt {
    type Output = Gt;

    fn mul(self, other: &'b Fr) -> Self::Output {
        let mut acc = Gt::identity();

        for bit in other
            .to_repr()
            .as_ref()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(1)
        {
            acc = acc.double();
            acc = Gt::conditional_select(&acc, &(acc + self), bit);
        }

        acc
    }
}

crate::impl_binops_additive!(Gt, Gt);
crate::impl_binops_multiplicative!(Gt, Fr);

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
    type Scalar = Fr;

    fn random(rng: impl RngCore) -> Self {
        use ff::Field;
        Fq12::random(rng).final_exponentiation()
    }

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        unimplemented!()
    }

    fn is_identity(&self) -> Choice {
        self.ct_eq(&Self::identity())
    }

    fn double(&self) -> Self {
        self.double()
    }
}

#[derive(Clone, Debug)]
pub struct Bn256;

impl Engine for Bn256 {
    type Fr = Fr;
    type G1 = G1;
    type G1Affine = G1Affine;
    type G2 = G2;
    type G2Affine = G2Affine;
    type Gt = Gt;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        Bn256::multi_miller_loop(&[(p, q)]).final_exponentiation()
    }
}

impl MultiMillerLoop for Bn256 {
    type G2Prepared = G2Affine;
    type Result = Fq12;

    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        multi_miller_loop(terms)
    }
}

impl PairingCurveAffine for G1Affine {
    type Pair = G2Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        Bn256::pairing(self, other)
    }
}

impl PairingCurveAffine for G2Affine {
    type Pair = G1Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        Bn256::pairing(other, self)
    }
}

fn double(f: &mut Fq12, r: &mut G2, p: &G1Affine) {
    use ff::Field;
    let t0 = r.x.square();
    let t1 = r.y.square();
    let t2 = t1.square();
    let t3 = (t1 + r.x).square() - t0 - t2;
    let t3 = t3 + t3;
    let t4 = t0 + t0 + t0;
    let t6 = r.x + t4;
    let t5 = t4.square();
    let zsquared = r.z.square();
    r.x = t5 - t3 - t3;
    r.z = (r.z + r.y).square() - t1 - zsquared;
    r.y = (t3 - r.x) * t4;
    let t2 = t2 + t2;
    let t2 = t2 + t2;
    let t2 = t2 + t2;
    r.y -= t2;
    let t3 = t4 * zsquared;
    let t3 = t3 + t3;
    let t3 = -t3;
    let t6 = t6.square() - t0 - t5;
    let t1 = t1 + t1;
    let t1 = t1 + t1;
    let t6 = t6 - t1;
    let t0 = r.z * zsquared;
    let t0 = t0 + t0;

    ell(f, &(t0, t3, t6), p);
}

fn add(f: &mut Fq12, r: &mut G2, q: &G2Affine, p: &G1Affine) {
    use ff::Field;
    let zsquared = r.z.square();
    let ysquared = q.y.square();
    let t0 = zsquared * q.x;
    let t1 = ((q.y + r.z).square() - ysquared - zsquared) * zsquared;
    let t2 = t0 - r.x;
    let t3 = t2.square();
    let t4 = t3 + t3;
    let t4 = t4 + t4;
    let t5 = t4 * t2;
    let t6 = t1 - r.y - r.y;
    let t9 = t6 * q.x;
    let t7 = t4 * r.x;
    r.x = t6.square() - t5 - t7 - t7;
    r.z = (r.z + t2).square() - zsquared - t3;
    let t10 = q.y + r.z;
    let t8 = (t7 - r.x) * t6;
    let t0 = r.y * t5;
    let t0 = t0 + t0;
    r.y = t8 - t0;
    let t10 = t10.square() - ysquared;
    let ztsquared = r.z.square();
    let t10 = t10 - ztsquared;
    let t9 = t9 + t9 - t10;
    let t10 = r.z + r.z;
    let t6 = -t6;
    let t1 = t6 + t6;

    ell(f, &(t10, t1, t9), p);
}

impl MillerLoopResult for Fq12 {
    type Gt = Gt;

    fn final_exponentiation(&self) -> Self::Gt {
        fn exp_by_x(f: &mut Fq12) {
            let x = super::BN_X;
            let mut res = Fq12::one();
            for i in (0..64).rev() {
                res.cyclotomic_square();
                if ((x >> i) & 1) == 1 {
                    res.mul_assign(f);
                }
            }
            *f = res;
        }

        let r = *self;
        let mut f1 = *self;
        f1.conjugate();

        use ff::Field;
        Gt(r.invert()
            .map(|mut f2| {
                let mut r = f1;
                r.mul_assign(&f2);
                f2 = r;
                r.frobenius_map(2);
                r.mul_assign(&f2);

                let mut fp = r;
                fp.frobenius_map(1);

                let mut fp2 = r;
                fp2.frobenius_map(2);
                let mut fp3 = fp2;
                fp3.frobenius_map(1);

                let mut fu = r;
                exp_by_x(&mut fu);

                let mut fu2 = fu;
                exp_by_x(&mut fu2);

                let mut fu3 = fu2;
                exp_by_x(&mut fu3);

                let mut y3 = fu;
                y3.frobenius_map(1);

                let mut fu2p = fu2;
                fu2p.frobenius_map(1);

                let mut fu3p = fu3;
                fu3p.frobenius_map(1);

                let mut y2 = fu2;
                y2.frobenius_map(2);

                let mut y0 = fp;
                y0.mul_assign(&fp2);
                y0.mul_assign(&fp3);

                let mut y1 = r;
                y1.conjugate();

                let mut y5 = fu2;
                y5.conjugate();

                y3.conjugate();

                let mut y4 = fu;
                y4.mul_assign(&fu2p);
                y4.conjugate();

                let mut y6 = fu3;
                y6.mul_assign(&fu3p);
                y6.conjugate();

                y6.cyclotomic_square();
                y6.mul_assign(&y4);
                y6.mul_assign(&y5);

                let mut t1 = y3;
                t1.mul_assign(&y5);
                t1.mul_assign(&y6);

                y6.mul_assign(&y2);

                t1.cyclotomic_square();
                t1.mul_assign(&y6);
                t1.cyclotomic_square();

                let mut t0 = t1;
                t0.mul_assign(&y1);

                t1.mul_assign(&y0);

                t0.cyclotomic_square();
                t0.mul_assign(&t1);

                t0
            })
            .unwrap())
    }
}

pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Affine)]) -> Fq12 {
    let terms = terms
        .iter()
        .filter_map(|&(p, q)| {
            if bool::from(p.is_identity()) || bool::from(q.is_identity()) {
                None
            } else {
                Some((*p, *q))
            }
        })
        .collect::<Vec<_>>();

    let mut f = Fq12::one();
    let mut r = terms.iter().map(|(_, q)| q.to_curve()).collect::<Vec<_>>();

    for (i, x) in super::SIX_U_PLUS_2_NAF.iter().rev().skip(1).enumerate() {
        (i != 0).then(|| f.square_assign());

        for ((p, _), r) in terms.iter().zip(r.iter_mut()) {
            double(&mut f, r, p);
        }

        match x {
            &val @ (1 | -1) => {
                for ((p, q), r) in terms.iter().zip(r.iter_mut()) {
                    if val == 1 {
                        add(&mut f, r, q, p);
                    } else {
                        add(&mut f, r, &q.neg(), p);
                    }
                }
            }
            _ => continue,
        }
    }

    const XI_TO_Q_MINUS_1_OVER_2: Fq2 = Fq2 {
        c0: Fq([
            0xe4bbdd0c2936b629,
            0xbb30f162e133bacb,
            0x31a9d1b6f9645366,
            0x253570bea500f8dd,
        ]),
        c1: Fq([
            0xa1d77ce45ffe77c7,
            0x07affd117826d1db,
            0x6d16bd27bb7edc6b,
            0x2c87200285defecc,
        ]),
    };

    for ((p, q), r) in terms.iter().zip(r.iter_mut()) {
        let mut q1: G2Affine = *q;
        q1.x.conjugate();
        q1.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[1]);
        q1.y.conjugate();
        q1.y.mul_assign(&XI_TO_Q_MINUS_1_OVER_2);
        add(&mut f, r, &q1, p);
    }

    for ((p, q), r) in terms.iter().zip(r.iter_mut()) {
        let mut minusq2: G2Affine = *q;
        minusq2.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[2]);
        add(&mut f, r, &minusq2, p);
    }

    f
}

// Final steps of the line function on prepared coefficients
fn ell(f: &mut Fq12, coeffs: &(Fq2, Fq2, Fq2), p: &G1Affine) {
    let mut c0 = coeffs.0;
    let mut c1 = coeffs.1;
    c0.c0.mul_assign(&p.y);
    c0.c1.mul_assign(&p.y);
    c1.c0.mul_assign(&p.x);
    c1.c1.mul_assign(&p.x);
    Fq12::mul_by_034(f, &c0, &c1, &coeffs.2);
}

#[cfg(test)]
mod test {
    use super::super::Bn256;

    #[test]
    fn bn256_engine_tests() {
        crate::tests::engine::engine_tests::<Bn256>();
    }
}

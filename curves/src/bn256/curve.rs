use core::fmt::Debug;
use std::convert::TryInto;

use ff::{Field, PrimeField};
use group::{cofactor::CofactorGroup, prime::PrimeCurveAffine, Curve, Group, GroupEncoding};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{
    bn256::{Fq, Fq2, Fr},
    Coordinates, CurveAffine, CurveExt,
};

impl crate::serde::endian::EndianRepr for Fq2 {
    const ENDIAN: crate::serde::endian::Endian = Fq::ENDIAN;

    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn from_bytes(bytes: &[u8]) -> subtle::CtOption<Self> {
        Fq2::from_bytes(bytes[..Fq2::SIZE].try_into().unwrap())
    }
}

new_curve_impl!(
    (pub),
    G1,
    G1Affine,
    Fq,
    Fr,
    (G1_GENERATOR_X,G1_GENERATOR_Y),
    G1_A,
    G1_B,
    "bn256_g1",
    crate::serde::CompressedFlagConfig::TwoSpare,
    standard_sign
);

new_curve_impl!(
    (pub),
    G2,
    G2Affine,
    Fq2,
    Fr,
    (G2_GENERATOR_X, G2_GENERATOR_Y),
    G2_A,
    G2_B,
    "bn256_g2",
    crate::serde::CompressedFlagConfig::TwoSpare,
    standard_sign
);

const G1_GENERATOR_X: Fq = Fq::ONE;
const G1_GENERATOR_Y: Fq = Fq::from_raw([2, 0, 0, 0]);
const G1_A: Fq = Fq::ZERO;
const G1_B: Fq = Fq::from_raw([3, 0, 0, 0]);

const G2_A: Fq2 = Fq2 {
    c0: Fq::ZERO,
    c1: Fq::ZERO,
};

const G2_B: Fq2 = Fq2 {
    c0: Fq::from_raw([
        0x3267e6dc24a138e5,
        0xb5b4c5e559dbefa3,
        0x81be18991be06ac3,
        0x2b149d40ceb8aaae,
    ]),
    c1: Fq::from_raw([
        0xe4a2bd0685c315d2,
        0xa74fa084e52d1852,
        0xcd2cafadeed8fdf4,
        0x009713b03af0fed4,
    ]),
};

const G2_GENERATOR_X: Fq2 = Fq2 {
    c0: Fq::from_raw([
        0x46debd5cd992f6ed,
        0x674322d4f75edadd,
        0x426a00665e5c4479,
        0x1800deef121f1e76,
    ]),
    c1: Fq::from_raw([
        0x97e485b7aef312c2,
        0xf1aa493335a9e712,
        0x7260bfb731fb5d25,
        0x198e9393920d483a,
    ]),
};

const G2_GENERATOR_Y: Fq2 = Fq2 {
    c0: Fq::from_raw([
        0x4ce6cc0166fa7daa,
        0xe3d1e7690c43d37b,
        0x4aab71808dcb408f,
        0x12c85ea5db8c6deb,
    ]),

    c1: Fq::from_raw([
        0x55acdadcd122975b,
        0xbc4b313370b38ef3,
        0xec9e99ad690c3395,
        0x090689d0585ff075,
    ]),
};

impl group::cofactor::CofactorGroup for G1 {
    type Subgroup = G1;

    fn clear_cofactor(&self) -> Self {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, 1.into())
    }

    fn is_torsion_free(&self) -> Choice {
        1.into()
    }
}

impl CofactorGroup for G2 {
    type Subgroup = G2;

    fn clear_cofactor(&self) -> Self {
        fn exp_by_x(g2: &G2) -> G2 {
            let x = super::BN_X;
            let mut res = G2::identity();
            for i in (0..64).rev() {
                res = res.double();
                if ((x >> i) & 1) == 1 {
                    res += g2;
                }
            }
            res
        }

        fn psi(mut g2: G2) -> G2 {
            const U0: Fq = Fq::from_raw([
                0x99e39557176f553d,
                0xb78cc310c2c3330c,
                0x4c0bec3cf559b143,
                0x2fb347984f7911f7,
            ]);

            const U1: Fq = Fq::from_raw([
                0x1665d51c640fcba2,
                0x32ae2a1d0b7c9dce,
                0x4ba4cc8bd75a0794,
                0x16c9e55061ebae20,
            ]);
            let u = Fq2::new(U0, U1);

            const V0: Fq = Fq::from_raw([
                0xdc54014671a0135a,
                0xdbaae0eda9c95998,
                0xdc5ec698b6e2f9b9,
                0x063cf305489af5dc,
            ]);

            const V1: Fq = Fq::from_raw([
                0x82d37f632623b0e3,
                0x21807dc98fa25bd2,
                0x0704b5a7ec796f2b,
                0x07c03cbcac41049a,
            ]);
            let v = Fq2::new(V0, V1);

            g2.x.conjugate();
            g2.y.conjugate();
            g2.z.conjugate();

            g2.x *= u;
            g2.y *= v;

            g2
        }

        let u0 = exp_by_x(self);
        let u1 = psi(u0.double() + u0);
        let u2 = psi(psi(u0));
        let u3 = psi(psi(psi(*self)));

        u0 + u1 + u2 + u3
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        unimplemented!();
    }

    fn is_torsion_free(&self) -> Choice {
        // "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
        let e: [u8; 32] = [
            0x30, 0x64, 0x4e, 0x72, 0xe1, 0x31, 0xa0, 0x29, 0xb8, 0x50, 0x45, 0xb6, 0x81, 0x81,
            0x58, 0x5d, 0x28, 0x33, 0xe8, 0x48, 0x79, 0xb9, 0x70, 0x91, 0x43, 0xe1, 0xf5, 0x93,
            0xf0, 0x00, 0x00, 0x01,
        ];

        // self * GROUP_ORDER;
        let mut acc = G2::identity();
        for bit in e
            .iter()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(1)
        {
            acc = acc.double();
            acc = G2::conditional_select(&acc, &(acc + self), bit);
        }
        acc.is_identity()
    }
}

#[cfg(test)]
mod test {
    use group::UncompressedEncoding;

    use super::*;

    crate::curve_testing_suite!(G2, "clear_cofactor");
    crate::curve_testing_suite!(G1, G2);

    crate::curve_testing_suite!(
        G1,
        "constants",
        Fq::MODULUS,
        G1_A,
        G1_B,
        G1_GENERATOR_X,
        G1_GENERATOR_Y,
        Fr::MODULUS
    );

    crate::curve_testing_suite!(
        G2,
        "constants",
        Fq2::MODULUS,
        G2_A,
        G2_B,
        G2_GENERATOR_X,
        G2_GENERATOR_Y,
        Fr::MODULUS
    );

}

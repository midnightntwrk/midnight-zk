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

//! Elliptic curves used in-circuit.

use ff::PrimeField;
use group::{Curve, Group};
#[cfg(feature = "dev-curves")]
use midnight_curves::bn256;
use midnight_curves::{
    curve25519::Curve25519,
    secp256k1::{Secp256k1, Secp256k1Affine},
    CurveAffine, Fq as BlsScalar, JubjubAffine, JubjubExtended, JubjubSubgroup,
};

/// An elliptic curve whose points can be represented in terms of its base
/// field.
pub trait CircuitCurve: Curve + Default {
    /// Base field over which the EC is defined.
    type Base: PrimeField;

    /// Cryptographic group.
    type CryptographicGroup: Group<Scalar = Self::Scalar> + Into<Self>;

    /// Cofactor of the curve.
    const COFACTOR: u128 = 1;

    /// How many bits are needed to represent an element of the scalar field of
    /// the curve subgroup. This is the log2 rounded up of the curve order
    /// divided by the cofactor.
    const NUM_BITS_SUBGROUP: u32;

    /// Returns the coordinates.
    fn coordinates(&self) -> Option<(Self::Base, Self::Base)>;

    /// Constructs a point in the curve from its coordinates
    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self>;

    /// Checks that the point is part of the subgroup.
    fn into_subgroup(self) -> Self::CryptographicGroup;
}

/// A Weierstrass curve of the form `y^2 = x^3 + Ax + B`.
/// equipped with an efficient cubic endomorphism.
pub trait WeierstrassCurve: CircuitCurve {
    /// `A` parameter.
    const A: Self::Base;

    /// `B` parameter.
    const B: Self::Base;

    // Note:
    // There are 2 choices for each cubic root,
    // but they must agree!
    // SCALAR_ZETA * (x, y) = ( BASE_ZETA * x, y)
    //
    // It is recommended to get them directly from
    // ff::WithSmallOrderMulGroup<3> if available.

    /// Cubic root on the base field.
    const BASE_ZETA: Self::Base;

    /// Cubic root on the scalar field.
    const SCALAR_ZETA: Self::Scalar;
}

/// A twisted edwards curve of the form `A x^2 + y^2 = 1 + D x^2 y^2`.
pub trait EdwardsCurve: CircuitCurve {
    /// `A` parameter.
    const A: Self::Base;

    /// `D` parameter.
    const D: Self::Base;
}

impl CircuitCurve for JubjubExtended {
    type Base = BlsScalar;
    type CryptographicGroup = JubjubSubgroup;
    const COFACTOR: u128 = 8;
    const NUM_BITS_SUBGROUP: u32 = 252;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().get_u(), self.to_affine().get_v()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        // The only way to check that the coordinates are in the curve is via
        // the `from_bytes` interface
        // FIXME: change JubJub implementation to get a `frocm_coords_checked`
        // https://github.com/davidnevadoc/blstrs/issues/13c
        let mut bytes = y.to_bytes_le();
        let x_sign = x.to_bytes_le()[0] << 7;

        // Encode the sign of the u-coordinate in the most
        // significant bit.
        bytes[31] |= x_sign;

        let point = JubjubAffine::from_bytes(bytes).into_option().expect("Failed here");
        if point.get_v() == y {
            Some(point.into())
        } else {
            None
        }
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        <JubjubExtended as CofactorGroup>::into_subgroup(self)
            .expect("Point should be part of the subgroup")
    }
}

impl EdwardsCurve for JubjubExtended {
    const A: Self::Base = Self::Base::from_raw([
        0xffff_ffff_0000_0000,
        0x53bd_a402_fffe_5bfe,
        0x3339_d808_09a1_d805,
        0x73ed_a753_299d_7d48,
    ]);
    // `d = -(10240/10241)`
    const D: Self::Base = Self::Base::from_raw([
        0x0106_5fd6_d634_3eb1,
        0x292d_7f6d_3757_9d26,
        0xf5fd_9207_e6bd_7fd4,
        0x2a93_18e7_4bfa_2b48,
    ]);
}

// Implementation for Curve25519.
use midnight_curves::curve25519::Fp as Curve25519Base;

impl CircuitCurve for Curve25519 {
    type Base = Curve25519Base;
    type CryptographicGroup = Curve25519;
    const COFACTOR: u128 = 8;
    const NUM_BITS_SUBGROUP: u32 = 252;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        // Extract coordinates through compressed representation
        // CompressedEdwardsY format: bytes 0-31 contain y coordinate,
        // with bit 255 (high bit of byte 31) as x sign bit
        let compressed = self.0.compress();
        let bytes = compressed.to_bytes();

        // Extract y coordinate (clearing the sign bit)
        let mut y_bytes = bytes;
        y_bytes[31] &= 0x7f; // Clear high bit
        let y = Curve25519Base::from_bytes(&y_bytes).into_option()?;

        // Solve curve equation for x: -x^2 + y^2 = 1 + d*x^2*y^2
        // Rearranging: x^2 * (d*y^2 + 1) = y^2 - 1
        //              x^2 = (y^2 - 1) / (d*y^2 + 1)
        use ff::Field;

        // d = -(121665/121666) for Curve25519
        // In reduced form: d = 37095705934669439343138083508754565189542113879843219016388785533085940283555
        let d = Curve25519Base::from_raw([
            0x52036cee2b6ffe73,
            0x8cc740797779e898,
            0x0000000000000000,
            0x0000000000000000,
        ]);

        let y_squared = y.square();
        let numerator = y_squared - Curve25519Base::ONE;
        let denominator = d * y_squared + Curve25519Base::ONE;

        let x_squared = numerator * denominator.invert().into_option()?;
        let mut x = x_squared.sqrt().into_option()?;

        // Use sign bit to determine which root
        let x_sign = (bytes[31] >> 7) & 1;
        if (x.to_bytes()[0] & 1) != x_sign {
            x = -x;
        }

        Some((x, y))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        // Similar to JubjubExtended - encode as compressed bytes
        let mut bytes = y.to_bytes();
        let x_sign = x.to_bytes()[0] & 1;
        bytes[31] |= x_sign << 7;

        use group::GroupEncoding;
        Curve25519::from_bytes(&bytes).into_option()
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        // Multiply by cofactor to get into prime-order subgroup
        Curve25519(self.0.mul_by_cofactor())
    }
}

impl EdwardsCurve for Curve25519 {
    // A = -1 for Curve25519
    const A: Self::Base = Curve25519Base::from_raw([
        0xffffffffffffffec,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x7fffffffffffffff,
    ]);

    // D = -(121665/121666) for Curve25519
    const D: Self::Base = Curve25519Base::from_raw([
        0x52036cee2b6ffe73,
        0x8cc740797779e898,
        0x0000000000000000,
        0x0000000000000000,
    ]);
}

// Implementation for Secp256k1.
use midnight_curves::secp256k1::{Fp, Fq};
impl CircuitCurve for Secp256k1 {
    type Base = Fp;
    type CryptographicGroup = Secp256k1;

    const NUM_BITS_SUBGROUP: u32 = 256;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().x, self.to_affine().y))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <Secp256k1Affine as CurveAffine>::from_xy(x, y).into_option().map(|p| p.into())
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        self
    }
}

impl WeierstrassCurve for Secp256k1 {
    const A: Self::Base = Fp::from_raw([0, 0, 0, 0]);
    const B: Self::Base = Fp::from_raw([7, 0, 0, 0]);

    const BASE_ZETA: Self::Base = <Fp as ff::WithSmallOrderMulGroup<3>>::ZETA;
    const SCALAR_ZETA: Self::Scalar = <Fq as ff::WithSmallOrderMulGroup<3>>::ZETA;
}

// Implementation for Bls12-381.
use group::cofactor::CofactorGroup;
use midnight_curves::{Fp as BlsBase, G1Affine, G1Projective};

impl CircuitCurve for G1Projective {
    type Base = BlsBase;
    type CryptographicGroup = G1Projective;

    const NUM_BITS_SUBGROUP: u32 = 255;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().x(), self.to_affine().y()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <G1Affine as CurveAffine>::from_xy(x, y).into_option().map(|p| p.into())
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        self
    }
}

impl WeierstrassCurve for G1Projective {
    const A: Self::Base = midnight_curves::A;
    const B: Self::Base = midnight_curves::B;

    const BASE_ZETA: Self::Base = <BlsBase as ff::WithSmallOrderMulGroup<3>>::ZETA;
    const SCALAR_ZETA: Self::Scalar = <BlsScalar as ff::WithSmallOrderMulGroup<3>>::ZETA;
}

// Implementation for BN254.
#[cfg(feature = "dev-curves")]
impl CircuitCurve for bn256::G1 {
    type Base = bn256::Fq;
    type CryptographicGroup = bn256::G1;

    const NUM_BITS_SUBGROUP: u32 = 254;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().x, self.to_affine().y))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <bn256::G1Affine as CurveAffine>::from_xy(x, y).into_option().map(|p| p.into())
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        self
    }
}

#[cfg(feature = "dev-curves")]
impl WeierstrassCurve for bn256::G1 {
    const A: Self::Base = bn256::Fq::from_raw([0, 0, 0, 0]);
    const B: Self::Base = bn256::Fq::from_raw([3, 0, 0, 0]);

    const BASE_ZETA: Self::Base = <bn256::Fq as ff::WithSmallOrderMulGroup<3>>::ZETA;
    const SCALAR_ZETA: Self::Scalar = <bn256::Fr as ff::WithSmallOrderMulGroup<3>>::ZETA;
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;

    #[test]
    fn test_curve25519_circuit_curve() {
        // Test generator point coordinates extraction
        let gen = Curve25519::generator();
        let (x, y) = gen.coordinates().expect("Failed to extract coordinates");

        // Test from_xy reconstruction
        let reconstructed = Curve25519::from_xy(x, y).expect("Failed to reconstruct point");

        // Verify coordinates match
        let (x2, y2) = reconstructed.coordinates().expect("Failed to extract coordinates again");
        assert_eq!(x, x2);
        assert_eq!(y, y2);

        // Test identity point
        let identity = Curve25519::identity();
        let (ix, iy) = identity.coordinates().expect("Failed to extract identity coordinates");

        // For Edwards curves, identity is (0, 1)
        assert_eq!(ix, Curve25519Base::ZERO);
        assert_eq!(iy, Curve25519Base::ONE);

        // Test from_xy with identity coordinates
        let identity_reconstructed =
            Curve25519::from_xy(Curve25519Base::ZERO, Curve25519Base::ONE)
                .expect("Failed to reconstruct identity");
        assert_eq!(identity, identity_reconstructed);
    }

    #[test]
    fn test_curve25519_edwards_constants() {
        // Verify Edwards curve constants are set correctly
        // A = -1 for Curve25519
        assert_eq!(<Curve25519 as EdwardsCurve>::A, -Curve25519Base::ONE);

        // D = -(121665/121666) for Curve25519
        // Just verify it's non-zero
        assert!(<Curve25519 as EdwardsCurve>::D != Curve25519Base::ZERO);
    }

    #[test]
    fn test_curve25519_cofactor() {
        // Test into_subgroup multiplies by cofactor
        let gen = Curve25519::generator();
        let subgroup_point = gen.into_subgroup();

        // The subgroup point should be 8 times the generator
        let eight = Curve25519::generator()
            + Curve25519::generator()
            + Curve25519::generator()
            + Curve25519::generator()
            + Curve25519::generator()
            + Curve25519::generator()
            + Curve25519::generator()
            + Curve25519::generator();

        assert_eq!(subgroup_point, eight);
    }
}

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
use halo2curves::{
    bn256,
    secp256k1::{Secp256k1, Secp256k1Affine},
    CurveAffine,
};
use midnight_curves::{Fq as BlsScalar, JubjubAffine, JubjubExtended, JubjubSubgroup};

/// An elliptic curve whose points can be represented in terms of its base
/// field.
pub trait CircuitCurve: Curve + Default {
    /// Base field over which the EC is defined.
    type Base: PrimeField;

    /// Cryptographic group.
    type CryptographicGroup: Group<Scalar = Self::Scalar> + Into<Self>;

    /// Cofactor of the curve.
    const COFACTOR: u128 = 1;

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

        let point = JubjubAffine::from_bytes(bytes)
            .into_option()
            .expect("Failed here");
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

// Implementation for Secp256k1.
use halo2curves::secp256k1::{Fp, Fq};
impl CircuitCurve for Secp256k1 {
    type Base = Fp;
    type CryptographicGroup = Secp256k1;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().x, self.to_affine().y))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <Secp256k1Affine as CurveAffine>::from_xy(x, y)
            .into_option()
            .map(|p| p.into())
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

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().x(), self.to_affine().y()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <G1Affine as CurveAffine>::from_xy(x, y)
            .into_option()
            .map(|p| p.into())
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
impl CircuitCurve for bn256::G1 {
    type Base = bn256::Fq;
    type CryptographicGroup = bn256::G1;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().x, self.to_affine().y))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <bn256::G1Affine as CurveAffine>::from_xy(x, y)
            .into_option()
            .map(|p| p.into())
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        self
    }
}

impl WeierstrassCurve for bn256::G1 {
    const A: Self::Base = bn256::Fq::from_raw([0, 0, 0, 0]);
    const B: Self::Base = bn256::Fq::from_raw([3, 0, 0, 0]);

    const BASE_ZETA: Self::Base = <bn256::Fq as ff::WithSmallOrderMulGroup<3>>::ZETA;
    const SCALAR_ZETA: Self::Scalar = <bn256::Fr as ff::WithSmallOrderMulGroup<3>>::ZETA;
}

// Implementation for Vesta.
use halo2curves::pasta::{
    vesta::{Affine as VestaAffine, Point as Vesta},
    Fp as VestaScalar, Fq as VestaBase,
};

impl CircuitCurve for Vesta {
    type Base = VestaBase;
    type CryptographicGroup = Vesta;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        let coordinates = self.to_affine().coordinates().into_option()?;
        Some((*coordinates.x(), *coordinates.y()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        <VestaAffine as CurveAffine>::from_xy(x, y)
            .into_option()
            .map(|p| p.into())
    }

    fn into_subgroup(self) -> Self::CryptographicGroup {
        self
    }
}

impl WeierstrassCurve for Vesta {
    const A: Self::Base = VestaBase::from_raw([0, 0, 0, 0]);
    const B: Self::Base = VestaBase::from_raw([5, 0, 0, 0]);

    const BASE_ZETA: Self::Base = <VestaBase as ff::WithSmallOrderMulGroup<3>>::ZETA;
    const SCALAR_ZETA: Self::Scalar = <VestaScalar as ff::WithSmallOrderMulGroup<3>>::ZETA;
}

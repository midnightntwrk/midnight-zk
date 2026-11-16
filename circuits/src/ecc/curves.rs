// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

use ff::Field;
use group::{Curve, Group};
#[cfg(feature = "dev-curves")]
use midnight_curves::{CurveAffine, bn256};
use midnight_curves::{
    Fq as BlsScalar, JubjubAffine, JubjubExtended, JubjubSubgroup,
    curve25519::{CURVE_A as CURVE25519_A, CURVE_D as CURVE25519_D, Curve25519, Curve25519Affine},
};

use crate::CircuitField;

/// An elliptic curve whose points can be represented in terms of its base
/// field.
pub trait CircuitCurve: Curve + Default {
    /// Base field over which the EC is defined.
    type Base: CircuitField;

    /// Scalar field with CircuitField bound (same type as Group::Scalar).
    type ScalarField: CircuitField;

    /// Cryptographic group.
    type CryptographicGroup: Group<Scalar = Self::ScalarField> + Into<Self>;

    /// Cofactor of the curve.
    const COFACTOR: u128 = 1;

    /// How many bits are needed to represent an element of the scalar field of
    /// the curve subgroup. This is the log2 rounded up of the curve order
    /// divided by the cofactor.
    const NUM_BITS_SUBGROUP: u32;

    /// Returns the affine coordinates of the point, or `None` if the point
    /// has no valid affine representation (e.g. the Weierstrass identity).
    fn coordinates(&self) -> Option<(Self::Base, Self::Base)>;

    /// Constructs a point in the curve from its coordinates.
    /// Returns `None` if the coordinates do not satisfy the curve equation.
    ///
    /// NB: Edwards identity coordinates, (0, 1), satisfy the equation, whereas
    /// Weierstrass identity coordinates, typically (0, 0), do not.
    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self>;

    /// Checks that the point is part of the subgroup and returns the
    /// [Self::CryptographicGroup] type. Returns `None` if the check fails.
    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup>;

    /// Checks that the point is part of the subgroup and returns the
    /// [Self::CryptographicGroup] type.
    ///
    /// # Panics
    ///
    /// If the point is not part of the subgroup. Use
    /// [Self::try_into_subgroup] for a fallible version.
    fn into_subgroup(self) -> Self::CryptographicGroup {
        self.try_into_subgroup().expect("point must be in the prime-order subgroup")
    }
}

/// A Weierstrass curve of the form `y^2 = x^3 + Ax + B`.
pub trait WeierstrassCurve: CircuitCurve {
    /// `A` parameter.
    const A: Self::Base;

    /// `B` parameter.
    const B: Self::Base;

    /// Whether this curve supports the cubic endomorphism used by the GLV MSM
    /// optimization.
    fn has_cubic_endomorphism() -> bool {
        true
    }

    // Note:
    // There are 2 choices for each cubic root,
    // but they must agree!
    // scalar_zeta() * (x, y) = ( base_zeta() * x, y)

    /// Cubic root on the base field.
    fn base_zeta() -> Self::Base;

    /// Cubic root on the scalar field.
    fn scalar_zeta() -> Self::ScalarField;
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
    type ScalarField = <Self as Group>::Scalar;
    type CryptographicGroup = JubjubSubgroup;
    const COFACTOR: u128 = 8;
    const NUM_BITS_SUBGROUP: u32 = 252;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        Some((self.to_affine().get_u(), self.to_affine().get_v()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        // Check the twisted Edwards curve equation: A x² + y² = 1 + D x² y².
        let a = <Self as EdwardsCurve>::A;
        let d = <Self as EdwardsCurve>::D;
        let (x2, y2) = (x.square(), y.square());
        if a * x2 + y2 != Self::Base::ONE + d * x2 * y2 {
            return None;
        }
        Some(JubjubAffine::from_raw_unchecked(x, y).into())
    }

    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup> {
        <JubjubExtended as CofactorGroup>::into_subgroup(self).into_option()
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
use midnight_curves::curve25519::{Curve25519Subgroup, Fp as Curve25519Base};
impl CircuitCurve for Curve25519 {
    type Base = Curve25519Base;
    type ScalarField = <Self as Group>::Scalar;

    type CryptographicGroup = Curve25519Subgroup;
    const COFACTOR: u128 = 8;
    const NUM_BITS_SUBGROUP: u32 = 253;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        let affine = Curve25519Affine::from_edwards(self.0);
        Some((*affine.x(), *affine.y()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        let affine = Curve25519Affine::from_xy(x, y)?;
        Some(Curve25519::from(affine))
    }

    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup> {
        Curve25519Subgroup::from_edwards(self.0)
    }
}

impl EdwardsCurve for Curve25519 {
    const A: Self::Base = CURVE25519_A;
    const D: Self::Base = CURVE25519_D;
}

// Implementation for K256 (secp256k1 using k256 crate).
use midnight_curves::k256::{Fp as K256Fp, K256, K256Affine};

impl CircuitCurve for K256 {
    type Base = K256Fp;
    type ScalarField = <Self as Group>::Scalar;
    type CryptographicGroup = K256;

    const NUM_BITS_SUBGROUP: u32 = 256;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        if self.is_identity().into() {
            return None;
        }
        let affine = self.to_affine();
        Some((affine.x(), affine.y()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        K256Affine::from_xy(x, y).map(|p| p.into())
    }

    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup> {
        Some(self)
    }
}

impl WeierstrassCurve for K256 {
    const A: Self::Base = K256Fp::ZERO;
    const B: Self::Base = K256Fp::from_u64(7);

    fn base_zeta() -> Self::Base {
        K256::base_zeta()
    }

    fn scalar_zeta() -> Self::ScalarField {
        K256::scalar_zeta()
    }
}

// Implementation for P256 (secp256r1 / NIST P-256).
use midnight_curves::p256::{
    CURVE_A, CURVE_B, Fp as P256Fp, P256, affine_from_xy, affine_x, affine_y,
};

impl CircuitCurve for P256 {
    type Base = P256Fp;
    type ScalarField = <Self as Group>::Scalar;
    type CryptographicGroup = P256;

    const NUM_BITS_SUBGROUP: u32 = 256;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        if bool::from(self.is_identity()) {
            return Some((P256Fp::ZERO, P256Fp::ZERO));
        }
        let affine = self.to_affine();
        Some((affine_x(&affine), affine_y(&affine)))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        affine_from_xy(x, y).map(Into::into)
    }

    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup> {
        Some(self)
    }
}

impl WeierstrassCurve for P256 {
    const A: Self::Base = CURVE_A;
    const B: Self::Base = CURVE_B;

    fn has_cubic_endomorphism() -> bool {
        false
    }

    fn base_zeta() -> Self::Base {
        unimplemented!("P256 does not have a cubic endomorphism")
    }

    fn scalar_zeta() -> Self::ScalarField {
        unimplemented!("P256 does not have a cubic endomorphism")
    }
}

// Implementation for Bls12-381.
use group::cofactor::CofactorGroup;
use midnight_curves::{Fp as BlsBase, G1Affine, G1Projective};

impl CircuitCurve for G1Projective {
    type Base = BlsBase;
    type ScalarField = <Self as Group>::Scalar;
    type CryptographicGroup = G1Projective;

    // BLS12-381 G1 cofactor.
    const COFACTOR: u128 = 0x396c8c005555e1568c00aaab0000aaab;
    const NUM_BITS_SUBGROUP: u32 = 255;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        if self.is_identity().into() {
            return None;
        }
        let affine = self.to_affine();
        Some((affine.x(), affine.y()))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        // Check the (short) Weierstrass curve equation: y² = x³ + Ax + B
        let a = <Self as WeierstrassCurve>::A;
        let b = <Self as WeierstrassCurve>::B;
        if y.square() != x.square() * x + a * x + b {
            return None;
        }
        // The point is not required to be in the prime-order subgroup, so we
        // cannot use `CurveAffine::from_xy`, which rejects points outside of it.
        Some(G1Affine::from_xy_unchecked(x, y).into())
    }

    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup> {
        Some(self)
    }
}

impl WeierstrassCurve for G1Projective {
    const A: Self::Base = midnight_curves::A;
    const B: Self::Base = midnight_curves::B;

    fn base_zeta() -> Self::Base {
        <BlsBase as ff::WithSmallOrderMulGroup<3>>::ZETA
    }

    fn scalar_zeta() -> Self::ScalarField {
        <BlsScalar as ff::WithSmallOrderMulGroup<3>>::ZETA
    }
}

// Implementation for BN254.
#[cfg(feature = "dev-curves")]
impl CircuitCurve for bn256::G1 {
    type Base = bn256::Fq;
    type ScalarField = <Self as Group>::Scalar;
    type CryptographicGroup = bn256::G1;

    const NUM_BITS_SUBGROUP: u32 = 254;

    fn coordinates(&self) -> Option<(Self::Base, Self::Base)> {
        if self.is_identity().into() {
            return None;
        }
        let affine = self.to_affine();
        Some((affine.x, affine.y))
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> Option<Self> {
        // Check the (short) Weierstrass curve equation: y² = x³ + Ax + B
        // The underlying `CurveAffine::from_xy` handles the identity coordinates
        // without errors via a short-circuit check.
        let a = <Self as WeierstrassCurve>::A;
        let b = <Self as WeierstrassCurve>::B;
        if y.square() != x.square() * x + a * x + b {
            return None;
        }
        <bn256::G1Affine as CurveAffine>::from_xy(x, y).into_option().map(|p| p.into())
    }

    fn try_into_subgroup(self) -> Option<Self::CryptographicGroup> {
        Some(self)
    }
}

#[cfg(feature = "dev-curves")]
impl WeierstrassCurve for bn256::G1 {
    const A: Self::Base = bn256::Fq::from_raw([0, 0, 0, 0]);
    const B: Self::Base = bn256::Fq::from_raw([3, 0, 0, 0]);

    fn base_zeta() -> Self::Base {
        <bn256::Fq as ff::WithSmallOrderMulGroup<3>>::ZETA
    }
    fn scalar_zeta() -> Self::ScalarField {
        <bn256::Fr as ff::WithSmallOrderMulGroup<3>>::ZETA
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests that `coordinates` on the identity returns `Some` for Edwards
    /// curves (the identity has valid affine coordinates) and `None` for
    /// Weierstrass curves (the identity is the point at infinity).
    #[test]
    fn test_identity_coordinates() {
        fn check<C: CircuitCurve>(has_coordinates: bool) {
            assert_eq!(C::identity().coordinates().is_some(), has_coordinates);
        }

        // Edwards curves
        check::<JubjubExtended>(true);
        check::<Curve25519>(true);

        // Weierstrass curves
        check::<K256>(false);
        check::<G1Projective>(false);
        #[cfg(feature = "dev-curves")]
        check::<bn256::G1>(false);
    }

    /// Tests that `from_xy` rejects coordinates that do not satisfy the curve
    /// equation, and that accepted points have exactly the given coordinates.
    #[test]
    fn test_from_xy_checks_both_coordinates() {
        fn check<C: CircuitCurve>() {
            let two = C::Base::from(2);
            let mut p = C::generator();
            for _ in 0..10 {
                let (x, y) = p.coordinates().unwrap();
                assert_eq!(C::from_xy(x, y).unwrap().coordinates(), Some((x, y)));
                // Perturbations that preserve the parity of the coordinates.
                assert!(C::from_xy(x + two, y).is_none());
                assert!(C::from_xy(x, y + two).is_none());
                // (-x, y) is on Edwards curves and off Weierstrass ones; either
                // way it must not be mapped to a point with other coordinates.
                if let Some(q) = C::from_xy(-x, y) {
                    assert_eq!(q.coordinates(), Some((-x, y)));
                }
                p = p.double() + C::generator();
            }
        }

        check::<JubjubExtended>();
        check::<Curve25519>();
        check::<K256>();
        check::<P256>();
        check::<G1Projective>();
        #[cfg(feature = "dev-curves")]
        check::<bn256::G1>();
    }

    /// Tests that `from_xy` accepts points of BLS12-381 that satisfy the curve
    /// equation but lie outside the prime-order subgroup, preserving their
    /// coordinates.
    #[test]
    fn test_bls_from_xy_outside_subgroup() {
        // (0, 2) is a point of order 3.
        let (x, y) = (BlsBase::ZERO, BlsBase::from(2));
        let p = G1Projective::from_xy(x, y).expect("(0, 2) satisfies the curve equation");
        assert!(!bool::from(p.to_affine().is_torsion_free()));
        assert_eq!(p.coordinates(), Some((x, y)));
        assert!(bool::from((p.double() + p).is_identity()));

        // A point in the subgroup is still accepted.
        let (x, y) = G1Projective::generator().coordinates().unwrap();
        assert_eq!(G1Projective::from_xy(x, y), Some(G1Projective::generator()));
    }

    /// Tests that `from_xy` on the identity coordinates returns `Some` only
    /// when the coordinates satisfy the curve equation.
    ///
    /// Edwards identity coordinates, (0, 1), satisfy the equation.
    /// Weierstrass identity coordinates, typically (0, 0), do not.
    #[test]
    fn test_identity_from_xy() {
        fn check<C: CircuitCurve>(identity_on_curve: bool) {
            let (x, y) = C::identity().coordinates().unwrap_or((C::Base::ZERO, C::Base::ZERO));
            match C::from_xy(x, y) {
                Some(p) => assert!(identity_on_curve && bool::from(p.is_identity())),
                None => assert!(!identity_on_curve),
            }
        }

        // Edwards curves
        check::<JubjubExtended>(true);
        check::<Curve25519>(true);

        // Weierstrass curves
        check::<K256>(false);
        check::<G1Projective>(false);
        #[cfg(feature = "dev-curves")]
        check::<bn256::G1>(false);
    }
}

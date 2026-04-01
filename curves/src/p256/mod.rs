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

//! secp256r1 / NIST P-256 aliases and constants using the p256 crate.

use ff::PrimeField;
use p256::elliptic_curve::{
    point::AffineCoordinates,
    sec1::{FromEncodedPoint, ToEncodedPoint},
};
use primeorder::PrimeCurveParams;

/// secp256r1 base field element.
pub type Fp = p256::FieldElement;

/// secp256r1 scalar field.
pub type Fq = p256::Scalar;

/// secp256r1 projective curve point.
pub type P256 = p256::ProjectivePoint;

/// secp256r1 affine curve point.
pub type P256Affine = p256::AffinePoint;

/// Returns the affine x-coordinate as an `Fp` element.
pub fn affine_x(point: &P256Affine) -> Fp {
    Fp::from_repr(point.x()).expect("valid affine x coordinate")
}

/// Returns the affine y-coordinate as an `Fp` element.
pub fn affine_y(point: &P256Affine) -> Fp {
    let encoded = point.to_encoded_point(false);
    let y_bytes = *encoded.y().expect("uncompressed point has y coordinate");
    Fp::from_repr(y_bytes).expect("valid affine y coordinate")
}

/// Constructs an affine point from `x` and `y` field elements.
pub fn affine_from_xy(x: Fp, y: Fp) -> Option<P256Affine> {
    let encoded = p256::EncodedPoint::from_affine_coordinates(&x.to_repr(), &y.to_repr(), false);
    P256Affine::from_encoded_point(&encoded).into_option()
}

/// P-256 curve coefficient `a = -3`.
pub const CURVE_A: Fp = <p256::NistP256 as PrimeCurveParams>::EQUATION_A;

/// P-256 curve coefficient `b`.
///
/// `b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b`
pub const CURVE_B: Fp = <p256::NistP256 as PrimeCurveParams>::EQUATION_B;

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

//! Affine representation for Curve25519 points.

use curve25519_dalek::{edwards::CompressedEdwardsY, EdwardsPoint};
use ff::Field;
use group::GroupEncoding;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use super::{
    curve::{Curve25519, CURVE_A, CURVE_D},
    Fp,
};

/// Affine representation with cached EdwardsPoint for efficient conversion.
///
/// Stores both the affine coordinates (x, y) as `Fp` field elements and
/// a cached `EdwardsPoint`.
#[derive(Copy, Clone, Debug)]
pub struct Curve25519Affine {
    x: Fp,
    y: Fp,
    // Cached EdwardsPoint for cheap conversion. This is necessary because
    // the only entry point for EdwardsPoint is via CompressedEdwardsY::decompress()
    // which requires a sqrt and a field inversion.
    // The whole structure will be removed once the affine point API is publicly exposed.
    // [PR 819](https://github.com/dalek-cryptography/curve25519-dalek/pull/819)
    point: EdwardsPoint,
}

impl Curve25519Affine {
    /// Returns the x coordinate.
    pub fn x(&self) -> &Fp {
        &self.x
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> &Fp {
        &self.y
    }

    /// Returns the cached EdwardsPoint.
    pub fn to_edwards(&self) -> EdwardsPoint {
        self.point
    }

    /// Creates a new `Curve25519Affine` from an `EdwardsPoint`.
    pub fn from_edwards(point: EdwardsPoint) -> Option<Self> {
        let compressed = point.compress();
        let bytes = compressed.to_bytes();

        // Extract y (stored in bytes[0..31] with sign bit in bytes[31] bit 7).
        let mut y_bytes = bytes;
        let x_sign = (y_bytes[31] >> 7) & 1;
        y_bytes[31] &= 0x7f; // Clear sign bit.

        let y = Fp::from_bytes(&y_bytes).into_option()?;

        // Recover x from y using curve equation: -x^2 + y^2 = 1 + d*x^2*y^2
        // Rearranged: x^2 = (y^2 - 1) / (1 + d*y^2)
        let y2 = y.square();
        let u_num = y2 - Fp::ONE;
        let u_den = Fp::ONE + CURVE_D * y2;

        let mut x = Fp::sqrt(&(u_num * u_den.invert().into_option()?)).into_option()?;

        // Apply sign correction.
        if (x.to_bytes()[0] & 1) != x_sign {
            x = -x;
        }

        Some(Self { x, y, point })
    }

    /// Creates a new `Curve25519Affine` from x and y coordinates.
    ///
    /// Validates that the point is on the curve.
    pub fn from_xy(x: Fp, y: Fp) -> Option<Self> {
        // Validate that (x, y) is on the curve: a*x² + y² = 1 + d*x²*y²
        let x2 = x.square();
        let y2 = y.square();
        let lhs = CURVE_A * x2 + y2;
        let rhs = Fp::ONE + CURVE_D * x2 * y2;

        if lhs != rhs {
            return None;
        }

        // Encode as compressed bytes and decompress to get EdwardsPoint.
        let mut bytes = y.to_bytes();
        let x_sign = x.to_bytes()[0] & 1;
        bytes[31] |= x_sign << 7;

        let compressed = CompressedEdwardsY(bytes);
        let point = compressed.decompress()?;

        Some(Self { x, y, point })
    }
}

impl Default for Curve25519Affine {
    fn default() -> Self {
        Self {
            x: Fp::ZERO,
            y: Fp::ONE,
            point: EdwardsPoint::default(),
        }
    }
}

impl PartialEq for Curve25519Affine {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for Curve25519Affine {}

impl ConstantTimeEq for Curve25519Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y)
    }
}

impl ConditionallySelectable for Curve25519Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
            point: EdwardsPoint::conditional_select(&a.point, &b.point, choice),
        }
    }
}

impl From<Curve25519> for Curve25519Affine {
    fn from(point: Curve25519) -> Self {
        Curve25519Affine::from_edwards(point.0).expect("valid curve point")
    }
}

impl From<Curve25519Affine> for Curve25519 {
    fn from(affine: Curve25519Affine) -> Self {
        Curve25519(affine.point)
    }
}

impl GroupEncoding for Curve25519Affine {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> subtle::CtOption<Self> {
        let compressed = CompressedEdwardsY(*bytes);
        match compressed.decompress() {
            Some(point) => match Curve25519Affine::from_edwards(point) {
                Some(affine) => subtle::CtOption::new(affine, Choice::from(1u8)),
                None => subtle::CtOption::new(Curve25519Affine::default(), Choice::from(0u8)),
            },
            None => subtle::CtOption::new(Curve25519Affine::default(), Choice::from(0u8)),
        }
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> subtle::CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.point.compress().to_bytes()
    }
}

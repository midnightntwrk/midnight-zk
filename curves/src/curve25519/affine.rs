// Slightly adapted from https://github.com/dalek-cryptography/curve25519-dalek/blob/main/curve25519-dalek/src/edwards/affine.rs

use super::fp::Fp;
use super::{CompressedEdwardsY, EdwardsPoint};
use core::ops::Mul;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::Scalar;
use ff::Field;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

/// Affine Edwards point on untwisted curve.
#[derive(Copy, Clone, Debug)]
pub struct AffinePoint {
    pub(super) x: Fp,
    pub(super) y: Fp,
}

impl ConstantTimeEq for AffinePoint {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y)
    }
}

impl ConditionallySelectable for AffinePoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
        }
    }
}

impl Default for AffinePoint {
    fn default() -> AffinePoint {
        AffinePoint::identity()
    }
}

impl Identity for AffinePoint {
    fn identity() -> AffinePoint {
        AffinePoint {
            x: Fp::ZERO,
            y: Fp::ONE,
        }
    }
}

impl PartialEq for AffinePoint {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Eq for AffinePoint {}

impl AffinePoint {
    /// Convert to extended coordinates.
    pub fn to_edwards(self) -> EdwardsPoint {
        // Workaround access EdwardsPoint

        self.compress().decompress().expect("Valid EdwardsPoint")
        // EdwardsPoint {
        //     X: self.x,
        //     Y: self.y,
        //     Z: Fp::ONE,
        //     T: &self.x * &self.y,
        // }
    }

    /// Compress affine Edwards coordinates into `CompressedEdwardsY` format.
    #[inline]
    pub fn compress(self) -> CompressedEdwardsY {
        let mut s = self.y.to_bytes();
        s[31] ^= (self.x.to_bytes()[0] & 1) << 7;
        CompressedEdwardsY(s)
    }
}

impl Mul<AffinePoint> for Scalar {
    type Output = EdwardsPoint;

    #[inline]
    fn mul(self, rhs: AffinePoint) -> EdwardsPoint {
        self * &rhs
    }
}

impl Mul<&AffinePoint> for Scalar {
    type Output = EdwardsPoint;

    #[inline]
    fn mul(self, rhs: &AffinePoint) -> EdwardsPoint {
        rhs.to_edwards() * self
    }
}

#[cfg(test)]
mod tests {
    use super::{AffinePoint, EdwardsPoint, Identity};
    use curve25519_dalek::constants;

    #[test]
    fn identity_conversion() {
        assert_eq!(
            AffinePoint::identity().to_edwards(),
            EdwardsPoint::identity()
        );
    }

    #[test]
    fn generator_round_trip() {
        let basepoint = constants::ED25519_BASEPOINT_POINT;
        // Test compression/decompression round-trip
        let compressed = basepoint.compress();
        let decompressed = compressed.decompress().expect("valid point");
        assert_eq!(decompressed, basepoint);
    }
}

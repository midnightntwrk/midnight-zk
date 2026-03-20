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

//! secp256r1 / NIST P-256 implementation using the p256 crate.
//!
//! The p256 crate already exposes a suitable base-field type, so this module
//! re-exports it directly and keeps only a small helper for the Montgomery-form
//! curve constant.

mod curve;

pub use curve::{P256Affine, P256};

/// secp256r1 base field element.
pub type Fp = p256::FieldElement;

/// secp256r1 scalar field.
pub type Fq = p256::Scalar;

/// Creates a field element from raw Montgomery-form limbs (little-endian u64).
///
/// # Safety
///
/// The caller must ensure the limbs represent a valid Montgomery-form field
/// element. Correctness should be verified by round-trip tests.
const unsafe fn from_montgomery_limbs(limbs: [u64; 4]) -> Fp {
    unsafe { core::mem::transmute::<[u64; 4], p256::FieldElement>(limbs) }
}

/// P-256 curve coefficient `a = -3`.
pub const CURVE_A: Fp = Fp::from_u64(3).neg();

/// P-256 curve coefficient `b`.
///
/// `b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b`
///
/// Montgomery representation: `b * R mod p`.
///
/// # Safety
///
/// Uses [`from_montgomery_limbs`]; verified by
/// [`tests::test_curve_b_round_trip`].
pub const CURVE_B: Fp = unsafe {
    from_montgomery_limbs([
        0xd89c_df62_29c4_bddf,
        0xacf0_05cd_7884_3090,
        0xe5a2_20ab_f721_2ed6,
        0xdc30_061d_0487_4834,
    ])
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_curve_a_is_minus_three() {
        let expected = -Fp::from(3u64);
        assert_eq!(CURVE_A, expected);
    }

    #[test]
    fn test_curve_b_round_trip() {
        // The canonical (big-endian) byte encoding of b.
        let b_bytes: [u8; 32] = [
            0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7, 0xb3, 0xeb, 0xbd, 0x55, 0x76, 0x98,
            0x86, 0xbc, 0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53, 0xb0, 0xf6, 0x3b, 0xce, 0x3c, 0x3e,
            0x27, 0xd2, 0x60, 0x4b,
        ];
        use ff::PrimeField;
        let expected = Fp::from_repr(b_bytes.into()).unwrap();
        assert_eq!(CURVE_B, expected);
    }
}

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

//! Helper module for cpu ECDSA signatures over secp256k1 (k256).
use base64::DecodeError;
use ff::Field;
use group::{Curve, GroupEncoding};
use midnight_curves::k256::{Fp as K256Base, Fq as K256Scalar, K256Affine, K256};
use rand::RngCore;

use crate::CircuitField;

#[derive(Clone, Debug)]
/// ECDSA implemented over secp256k1 (k256).
pub struct Ecdsa;

/// ECDSA public key.
pub type PublicKey = K256;

/// ECDSA secret key.
pub type SecretKey = K256Scalar;

#[derive(Clone, Copy, Debug)]

/// ECDSA signature.
pub struct ECDSASig {
    // LE encoded r.
    r: [u8; 32],
    s: K256Scalar,
}

impl ECDSASig {
    /// Return `r` scalar as bytes.
    pub fn get_r(&self) -> [u8; 32] {
        self.r
    }

    /// Return `s` scalar.
    pub fn get_s(&self) -> K256Scalar {
        self.s
    }

    /// Create ECDSASig from a slice where:
    ///  - First 32 bytes represent BE-encoded r.
    ///  - Next 32 bytes represent BE-encoded s.
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 64);

        let mut r = [0u8; 32];
        r.copy_from_slice(&bytes[..32]);
        r.reverse();

        let s =
            K256Scalar::from_bytes_be(&bytes[32..]).expect("Valid secp256k1 scalar in signature");
        ECDSASig { r, s }
    }
}

impl Ecdsa {
    /// Generate keypair.
    pub fn keygen<R: RngCore>(rng: &mut R) -> (PublicKey, SecretKey) {
        let sk = K256Scalar::random(rng);
        let pk = K256::generator() * sk;
        (pk, sk)
    }

    /// Produce a signature for `msg_hash`.
    pub fn sign<R: RngCore>(sk: &SecretKey, msg_hash: &K256Scalar, rng: &mut R) -> ECDSASig {
        let k = K256Scalar::random(rng);
        let k_point: K256 = K256::generator() * k;

        let r_as_base = k_point.to_affine().x();
        let r = r_as_base.to_bytes_le();
        let r_as_scalar = K256Scalar::from_bytes_le(&r).unwrap();

        let s = k.invert().unwrap() * (msg_hash + r_as_scalar * sk);
        ECDSASig { r, s }
    }

    /// Verify a `signature` for `msg_hash` over key `pk`.
    pub fn verify(pk: &PublicKey, msg_hash: &K256Scalar, signature: &ECDSASig) -> bool {
        let g = K256::generator();
        let r_as_scalar = K256Scalar::from_bytes_le(&signature.r).unwrap();
        let r_as_base = K256Base::from_bytes_le(&signature.r).unwrap();

        let s_inv = signature.s.invert().unwrap();
        let k_point = g * (s_inv * msg_hash) + *pk * (s_inv * r_as_scalar);

        k_point.to_affine().x() == r_as_base
    }
}

// Note: Does this trait makes sense? If so, should it be moved somewhere else?
/// This represents an object that can be obtained from a base64 encoding.
pub trait FromBase64: Sized {
    /// Returns an element from its base64 encoding.
    fn from_base64(base64_bytes: &[u8]) -> Result<Self, DecodeError>;
}

impl FromBase64 for ECDSASig {
    /// Create ECDSASig from a JWT Base64 encoded blob of bytes.
    fn from_base64(base64_bytes: &[u8]) -> Result<Self, DecodeError> {
        let bytes = base64::decode_config(base64_bytes, base64::URL_SAFE_NO_PAD)?;
        Ok(ECDSASig::from_bytes_be(&bytes))
    }
}

impl FromBase64 for PublicKey {
    /// Input must be base64 encoding of the compressed point in BE.
    fn from_base64(base64_bytes: &[u8]) -> Result<Self, DecodeError> {
        let input_len = base64_bytes.len();

        match input_len {
            // Compressed format: standard SEC1 (0x02/0x03 prefix + 32 BE x-bytes).
            44 => {
                let bytes = base64::decode_config(base64_bytes, base64::STANDARD_NO_PAD)?;
                assert_eq!(bytes.len(), 33);
                let repr: [u8; 33] = bytes.try_into().expect("33 bytes");

                let ret = K256Affine::from_bytes(&repr.into())
                    .expect("Valid compressed secp256k1 point.");
                Ok(ret.into())
            }

            // Uncompressed format (JWK: two base64-encoded coordinates).
            86 => from_jwk(&base64_bytes[..43], &base64_bytes[43..]),
            _ => Err(DecodeError::InvalidLength),
        }
    }
}

/// Receives a public key in JWK format: (x, y) coordinates base64 encoded.
/// Returns the public key as a curve point.
fn from_jwk(x: &[u8], y: &[u8]) -> Result<PublicKey, DecodeError> {
    let x_bytes = base64::decode_config(x, base64::URL_SAFE)?;
    let y_bytes = base64::decode_config(y, base64::URL_SAFE)?;
    assert_eq!(x_bytes.len(), 32);
    assert_eq!(y_bytes.len(), 32);

    // JWK coordinates are in BE.
    let x_fp = K256Base::from_bytes_be(&x_bytes).expect("Valid x coordinate");
    let y_fp = K256Base::from_bytes_be(&y_bytes).expect("Valid y coordinate");

    let ret = K256Affine::from_xy(x_fp, y_fp).expect("Valid point on curve");
    Ok(ret.into())
}

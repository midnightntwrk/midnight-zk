//! Helper module for cpu ECDSA signatures over SECP256k1
use base64::DecodeError;
use ff::Field;
use group::{Curve, GroupEncoding};
use halo2curves::secp256k1::{
    Fp as secp256k1Base, Fq as secp256k1Scalar, Secp256k1, Secp256k1Affine,
};
use rand::RngCore;

#[derive(Clone, Debug)]
/// ECDSA implemented over SECP256k1
pub struct Ecdsa;

/// ECDSA public key
pub type PublicKey = Secp256k1;

/// ECDSA secret key
pub type SecretKey = secp256k1Scalar;

#[derive(Clone, Copy, Debug)]

/// ECDSA signature
pub struct ECDSASig {
    // LE encoded r.
    r: [u8; 32],
    s: secp256k1Scalar,
}

impl ECDSASig {
    /// Return `r` scalar as bytes
    pub fn get_r(&self) -> [u8; 32] {
        self.r
    }

    /// Return `s` scalar
    pub fn get_s(&self) -> secp256k1Scalar {
        self.s
    }

    /// Create ECDSASig from a slice where:
    ///  - First 32 bytes represent LE-encoded r.
    ///  - Next 32 bytes represent LE-encoded s.
    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 64);

        let r: [u8; 32] = bytes[..32].try_into().unwrap();
        let s_bytes: [u8; 32] = bytes[..32].try_into().unwrap();
        let s = secp256k1Scalar::from_bytes(&s_bytes).expect("Valid Secp256k1 scalar in signature");
        ECDSASig { r, s }
    }

    /// Create ECDSASig from a slice where:
    ///  - First 32 bytes represent BE-encoded r.
    ///  - Next 32 bytes represent BE-encoded s.
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 64);

        let mut r = [0u8; 32];
        r.copy_from_slice(&bytes[..32]);
        r.reverse();

        let mut s_bytes = [0u8; 32];
        s_bytes.copy_from_slice(&bytes[32..]);
        s_bytes.reverse();

        let s = secp256k1Scalar::from_bytes(&s_bytes).expect("Valid Secp256k1 scalar in signature");
        ECDSASig { r, s }
    }
}

impl Ecdsa {
    /// Generate keypair
    pub fn keygen<R: RngCore>(rng: &mut R) -> (PublicKey, SecretKey) {
        let sk = secp256k1Scalar::random(rng);
        let pk = Secp256k1::generator() * sk;
        (pk, sk)
    }

    /// Produce a signature for `msg_hash`
    pub fn sign<R: RngCore>(sk: &SecretKey, msg_hash: &secp256k1Scalar, rng: &mut R) -> ECDSASig {
        let k = secp256k1Scalar::random(rng);
        let k_point: Secp256k1 = Secp256k1::generator() * k;

        let r_as_base = k_point.to_affine().x;
        let r = r_as_base.to_bytes();
        let r_as_scalar = secp256k1Scalar::from_bytes(&r).unwrap();

        let s = k.invert().unwrap() * (msg_hash + r_as_scalar * sk);
        ECDSASig { r, s }
    }

    /// Verify a `signature` for `msg_hash` over key `pk`
    pub fn verify(pk: &PublicKey, msg_hash: &secp256k1Scalar, signature: &ECDSASig) -> bool {
        let gen = Secp256k1::generator();
        let r_as_scalar = secp256k1Scalar::from_bytes(&signature.r).unwrap();
        let r_as_base = secp256k1Base::from_bytes(&signature.r).unwrap();

        let s_inv = signature.s.invert().unwrap();
        let k_point = gen * (s_inv * msg_hash) + pk * (s_inv * r_as_scalar);

        k_point.to_affine().x == r_as_base
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
    fn from_base64(base64_bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut bytes = base64::decode_config(base64_bytes, base64::STANDARD_NO_PAD)?;
        assert_eq!(bytes.len(), 33);
        // Note:
        // Hack to adapt Secp256k1 spec format to halo2curves format.
        // We need to clear the identity flag, the second LSB of the first byte.
        // We do so by clearing all bits except the sign bit, the LSB.
        bytes[0] &= 0x01;
        bytes[1..].reverse();
        let repr = bytes.as_slice().into();

        let ret = Secp256k1Affine::from_bytes(&repr).expect("Valid compressed Secp256k1 point.");
        Ok(ret.into())
    }
}

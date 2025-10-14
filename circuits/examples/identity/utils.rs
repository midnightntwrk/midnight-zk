use std::{fs::OpenOptions, io::Read};

use halo2curves::secp256k1::{Fq as secp256k1Scalar, Secp256k1};
use midnight_circuits::testing_utils::ecdsa::{ECDSASig, Ecdsa, FromBase64};
use midnight_proofs::plonk::Error;
use sha2::Digest;

// Reads a credential of up to MAX bytes from the specified path.
pub(crate) fn read_credential<const MAX: usize>(path: &str) -> Result<Vec<u8>, Error> {
    let mut fd = OpenOptions::new().read(true).open(path)?;
    let mut buf = vec![0u8; MAX];
    let len = fd.read(buf.as_mut_slice())?;
    Ok(buf[..len - 1].into()) // -1 for the EOF
}

/// Splits a JWT blob in its 3 parts:
///  * header
///  * body
///  * signature
///
/// The signature is computed over payload := (header || body).
/// Returns the payload and the signature.
/// For reference: <https://auth0.com/docs/secure/tokens/json-web-tokens/json-web-token-structure>
pub(crate) fn split_blob(blob: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let mut parts = blob.split(|char| *char as char == '.');

    let header = parts.next().unwrap();
    let body = parts.next().unwrap();
    let signature = parts.next().unwrap();

    assert!(parts.next().is_none());

    let payload = [header, b".", body].concat();
    let signature = signature.to_vec();

    (payload, signature)
}

/// Verifies the signature of a credential (out of circuit).
/// The public key, message (or payload) and signature are expected in base64
/// encoding.
pub(crate) fn verify_credential_sig(pk_base64: &[u8], msg: &[u8], sig_base64: &[u8]) -> bool {
    let pk_affine = Secp256k1::from_base64(pk_base64).unwrap();
    let sig = ECDSASig::from_base64(sig_base64).unwrap();

    let mut msg_hash_bytes: [u8; 32] = sha2::Sha256::digest(msg).into();
    msg_hash_bytes.reverse(); // BE to LE
    let msg_scalar = secp256k1Scalar::from_bytes(&msg_hash_bytes).unwrap();

    Ecdsa::verify(&pk_affine, &msg_scalar, &sig)
}

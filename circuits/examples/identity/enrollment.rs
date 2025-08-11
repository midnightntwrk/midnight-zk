//! Example of enrollment proof on an Identus credential.
//! The enrollment proof verifies:
//!  - The ECDSA signature of the credential.
//!  - The Base64 decoding of the blob into JSON format.
//!  - The validity of the JSON structure.

use std::{fs::OpenOptions, io::Read};

use halo2curves::secp256k1::{Fq as secp256k1Scalar, Secp256k1};
use midnight_circuits::{
    compact_std_lib::{self, Relation, ShaTableSize, ZkStdLib, ZkStdLibArch},
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, Base64Instructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
        RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator},
    testing_utils::{
        ecdsa::{ECDSASig, Ecdsa, FromBase64, PublicKey},
        plonk_api::filecoin_srs,
    },
    types::{AssignedByte, AssignedForeignPoint, InnerValue, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;
use rand::rngs::OsRng;
use sha2::Digest;

type F = midnight_curves::Fq;

const CRED_PATH: &str = "./examples/identity/credentials/2k-credential";

// Public Key of the issuer, signer of the credential.
const PUB_KEY: &[u8] =
    b"_bDXlQJ636HHOvXSe-flG0f-OkkRu8Jusm93PB2GBjoykg753nsOiW1vhEpCnxxybkMdarJLXIUJIYw1K2emQI";

// Secret key of the credential holder.
const HOLDER_SK: SK = SK::from_raw([
    0x87c251f40ac6a55e,
    0xc82dbae785c00836,
    0x36f09fcb94100833,
    0xc4e05a8ec16835ce,
]);

const HEADER_LEN: usize = 38;
const PAYLOAD_LEN: usize = 2463;

// Issuer Public Key.
type PK = Secp256k1;
// Credential payload.
type Payload = [u8; PAYLOAD_LEN];
// Holder secret key.
type SK = secp256k1Scalar;

#[derive(Clone, Default)]
pub struct AtalaJsonECDSA;

impl Relation for AtalaJsonECDSA {
    type Instance = PK;
    type Witness = (Payload, ECDSASig, SK);

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        AssignedForeignPoint::<F, Secp256k1, MultiEmulationParams>::as_public_input(instance)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let b64_chip = std_lib.base64();

        // Assign the PK as public input.
        let pk = secp256k1_curve.assign_as_public_input(layouter, instance)?;

        let payload = witness.map(|(payload, _, _)| payload).transpose_array();
        let (sig, sk) = witness.map(|(_, sig, sk)| (sig, sk)).unzip();

        // Assign payload.
        let payload = std_lib.assign_many(layouter, &payload)?;

        // Verify credential signature.
        Self::verify_ecdsa(std_lib, layouter, pk, &payload, sig)?;

        // Decode Base64 JSON.
        let json =
            b64_chip.decode_base64(layouter, &payload[HEADER_LEN + 1..PAYLOAD_LEN], false)?;

        // TODO Constrain as committed instance

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: Some(ShaTableSize::Table11),
            secp256k1: true,
            bls12_381: false,
            base64: true,
            nr_pow2range_cols: 3,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(AtalaJsonECDSA)
    }
}

impl AtalaJsonECDSA {
    /// Verifies the secp256k1 ECDSA signature of the given message.
    fn verify_ecdsa(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        pk: AssignedForeignPoint<F, Secp256k1, MultiEmulationParams>,
        message: &[AssignedByte<F>],
        sig: Value<ECDSASig>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let secp256k1_scalar = std_lib.secp256k1_scalar();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        // Assign the message and hash it.
        let msg_hash: AssignedField<_, _, _> = {
            let hash_bytes = std_lib.sha256(layouter, message)?;
            secp256k1_scalar.assigned_from_be_bytes(layouter, &hash_bytes)?
        };

        // Assign the signature.
        let r_value = sig.map(|sig| sig.get_r());
        let r_le_bytes = std_lib.assign_many(layouter, &r_value.transpose_array())?;
        let s = secp256k1_scalar.assign(layouter, sig.map(|sig| sig.get_s()))?;

        let r_as_scalar = secp256k1_scalar.assigned_from_le_bytes(layouter, &r_le_bytes)?;
        let r_as_base = secp256k1_base.assigned_from_le_bytes(layouter, &r_le_bytes)?;

        // Verify the ECDSA signature: lhs.x =?= r, where
        // lhs := (msg_hash * s^-1) * G + (r * s^-1) * PK
        let r_over_s = secp256k1_scalar.div(layouter, &r_as_scalar, &s)?;
        let m_over_s = secp256k1_scalar.div(layouter, &msg_hash, &s)?;

        let gen = secp256k1_curve.assign_fixed(layouter, Secp256k1::generator())?;
        let lhs = secp256k1_curve.msm(layouter, &[m_over_s, r_over_s], &[gen, pk])?;
        let lhs_x = secp256k1_curve.x_coordinate(&lhs);

        secp256k1_base.assert_equal(layouter, &lhs_x, &r_as_base)
    }
}

// Reads a credential of up to MAX bytes from the specified path.
fn read_credential<const MAX: usize>(path: &str) -> Result<Vec<u8>, Error> {
    let mut fd = OpenOptions::new().read(true).open(path)?;
    let mut buf = vec![0u8; MAX];
    let len = fd.read(buf.as_mut_slice())?;
    Ok(buf[..len - 1].into()) // -1 for the EOF
}

fn main() {
    const K: u32 = 18;
    let srs = filecoin_srs(K);
    let credential_blob = read_credential::<4096>(CRED_PATH).expect("Path to credential file.");

    let relation = AtalaJsonECDSA;

    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    // Build the instance and witness to be proven.
    let instance = PublicKey::from_base64(PUB_KEY).expect("Base64 encoded PK");
    let witness = AtalaJsonECDSA::witness_from_blob(credential_blob.as_slice());
    let witness = (witness.0, witness.1, HOLDER_SK);

    let proof = compact_std_lib::prove::<AtalaJsonECDSA, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        compact_std_lib::verify::<AtalaJsonECDSA, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            &proof
        )
        .is_ok()
    )
}

// Helper functions for base64 encoded credentials.
// -----------------------------------------------
impl AtalaJsonECDSA {
    // Creates an AtalaJsonECDSA witness from:
    // 1. A JWT encoded Atala credential.
    // 2. The corresponding base64 encoded ECDSA public key.
    fn witness_from_blob(blob: &[u8]) -> (Payload, ECDSASig) {
        let (payload, signature_bytes) = split_blob(blob);

        assert!(verify_credential_sig(PUB_KEY, &payload, &signature_bytes));

        let signature = ECDSASig::from_base64(&signature_bytes).expect("Base64 encoded signature.");

        (
            payload.try_into().expect("Payload of length {PAYLOAD_LEN}"),
            signature,
        )
    }
}

/// Splits a JWT blob in its 3 parts:
///  * header
///  * body
///  * signature
///
/// The signature is computed over payload := (header || body).
/// Returns the payload and the signature.
/// For reference: <https://auth0.com/docs/secure/tokens/json-web-tokens/json-web-token-structure>
fn split_blob(blob: &[u8]) -> (Vec<u8>, Vec<u8>) {
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
fn verify_credential_sig(pk_base64: &[u8], msg: &[u8], sig_base64: &[u8]) -> bool {
    let pk_affine = Secp256k1::from_base64(pk_base64).unwrap();
    let sig = ECDSASig::from_base64(sig_base64).unwrap();

    let mut msg_hash_bytes: [u8; 32] = sha2::Sha256::digest(msg).into();
    msg_hash_bytes.reverse(); // BE to LE
    let msg_scalar = secp256k1Scalar::from_bytes(&msg_hash_bytes).unwrap();

    Ecdsa::verify(&pk_affine, &msg_scalar, &sig)
}

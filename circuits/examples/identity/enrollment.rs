//! Example of a proof of validity of an ECDSA signed credential.

use std::{io::Write, time::Instant};

use halo2curves::secp256k1::Secp256k1;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        public_input::CommittedInstanceInstructions, ArithInstructions, AssertionInstructions,
        AssignmentInstructions, Base64Instructions, DecompositionInstructions, EccInstructions,
        PublicInputInstructions,
    },
    testing_utils::{
        ecdsa::{ECDSASig, FromBase64, PublicKey},
        plonk_api::filecoin_srs,
    },
    types::{AssignedByte, AssignedForeignPoint, Instantiable},
};
use midnight_curves::G1Affine;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{commit_to_instances, Error},
    poly::kzg::KZGCommitmentScheme,
};
use rand::rngs::OsRng;
use utils::{read_credential, split_blob, verify_credential_sig};

#[path = "./utils.rs"]
mod utils;

type F = midnight_curves::Fq;

const CRED_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/identity/credentials/2k-credential"
);

// Public Key of the issuer, signer of the credential.
const PUB_KEY: &[u8] =
    b"_bDXlQJ636HHOvXSe-flG0f-OkkRu8Jusm93PB2GBjoykg753nsOiW1vhEpCnxxybkMdarJLXIUJIYw1K2emQI";

const HEADER_LEN: usize = 38;
const PAYLOAD_LEN: usize = 2463;

// Issuer Public Key.
type PK = Secp256k1;
// Credential payload.
type Payload = [u8; PAYLOAD_LEN];

/// This relation checks the validity of an Identus credential.
/// It receives as public inputs the public key of the credential signer and
/// the decoded JSON of the credential in committed form.
#[derive(Clone, Default)]
pub struct CredentialEnrollment;

impl Relation for CredentialEnrollment {
    type Instance = PK;
    type Witness = (Payload, ECDSASig);

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(AssignedForeignPoint::<F, Secp256k1, MultiEmulationParams>::as_public_input(instance))
    }

    fn format_committed_instances(witness: &Self::Witness) -> Vec<F> {
        let json_b64 = &witness.0[HEADER_LEN + 1..PAYLOAD_LEN];
        let json = base64::decode_config(json_b64, base64::STANDARD_NO_PAD)
            .expect("Valid base64 encoded JSON.");
        json.iter().map(|byte| F::from(*byte as u64)).collect()
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

        let (payload, sig) = witness.unzip();

        // Assign payload.
        let payload = std_lib.assign_many(layouter, &payload.transpose_array())?;

        // Verify credential signature.
        Self::verify_ecdsa(std_lib, layouter, pk, &payload, sig)?;

        // Decode Base64 JSON.
        let json_bytes =
            b64_chip.decode_base64(layouter, &payload[HEADER_LEN + 1..PAYLOAD_LEN], false)?;

        for byte in json_bytes.iter() {
            std_lib.constrain_as_committed_public_input(layouter, byte)?;
        }

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            sha512: false,
            secp256k1: true,
            bls12_381: false,
            base64: true,
            nr_pow2range_cols: 3,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(CredentialEnrollment)
    }
}

impl CredentialEnrollment {
    // Creates a witness from:
    // 1. A JWT encoded credential.
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

fn main() {
    const K: u32 = 17;
    let srs = filecoin_srs(K);
    let credential_blob = read_credential::<4096>(CRED_PATH).expect("Path to credential file.");

    let relation = CredentialEnrollment;

    let start = |msg: &str| -> Instant {
        print!("{msg}");
        let _ = std::io::stdout().flush();
        Instant::now()
    };

    let setup = start("Setting up the vk/pk");
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);
    println!("... done ({:?})", setup.elapsed());

    // Build the instance and witness to be proven.
    let wit = start("Computing instance and witnesses");
    let instance = PublicKey::from_base64(PUB_KEY).expect("Base64 encoded PK");
    let witness = {
        let w = CredentialEnrollment::witness_from_blob(credential_blob.as_slice());
        (w.0, w.1)
    };
    let committed_credential: G1Affine = {
        let instance = CredentialEnrollment::format_committed_instances(&witness);
        commit_to_instances::<_, KZGCommitmentScheme<_>>(&srs, vk.vk().get_domain(), &instance)
            .into()
    };
    println!("... done\n{:?}", wit.elapsed());

    let p = start("Proof generation");
    let proof = compact_std_lib::prove::<CredentialEnrollment, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");
    println!("... done\n{:?}", p.elapsed());

    let v = start("Proof verification");
    assert!(
        compact_std_lib::verify::<CredentialEnrollment, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            Some(committed_credential),
            &proof
        )
        .is_ok()
    );
    println!("... done\n{:?}", v.elapsed())
}

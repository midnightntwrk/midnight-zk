//! Example of verifying the validity of an ECDSA signed Atala identity JSON.

use blstrs::G1Affine;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use halo2curves::secp256k1::{Fq as secp256k1Scalar, Secp256k1};
use midnight_circuits::{
    compact_std_lib::{self, MidnightCircuit, Relation, ZkStdLib},
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
    },
    testing_utils::{
        ecdsa::{ECDSASig, Ecdsa, FromBase64},
        real_test_api::{check_vk, filecoin_srs},
    },
    types::{AssignedForeignPoint, Byte, Instantiable},
};
use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use sha2::Digest;

type F = blstrs::Scalar;

const _DATA: &str = r#"{
  "iss": "did:prism:aacafb5bdb3924b7731da155d611ba0d605fb37f72313cb7c996adf564f3bc31:CoQBCoEBEkIKDm15LWlzc3Vpbmcta2V5EAJKLgoJc2VjcDI1NmsxEiECmV5Y8sjADpg9wipCFCjfWrcBcHJgu83wj8OppnPRS9oSOwoHbWFzdGVyMBABSi4KCXNlY3AyNTZrMRIhAwyfObqSiUlOL_nyJoh9efoaE5xCsWfa37Ku3XRrP2tX",
  "sub": "did:prism:b3596c4defeb6ba2765ee58e64ad616a0e1165535ddc483cc4789cac01cd2384:CoABCn4SPwoLbXktYXV0aC1rZXkQBEouCglzZWNwMjU2azESIQPdU3R6CWuvulL3fXMFGmAGVvJNX8aIohzyLMoKeypt0hI7CgdtYXN0ZXIwEAFKLgoJc2VjcDI1NmsxEiEDg7g0XWjWob0dk2arGtDTNlkbak2gQZtgjcrroXDYIC4",
  "nbf": 1726835685,
  "exp": 1726839285,
  "vc": {
    "credentialSubject": {
      "familyName": "Wonderland",
      "givenName": "Alice",
      "national_id": "0123456789",
      "birthDate": "DDMMYYYY",
      "id": "did:prism:b3596c4defeb6ba2765ee58e64ad616a0e1165535ddc483cc4789cac01cd2384:CoABCn4SPwoLbXktYXV0aC1rZXkQBEouCglzZWNwMjU2azESIQPdU3R6CWuvulL3fXMFGmAGVvJNX8aIohzyLMoKeypt0hI7CgdtYXN0ZXIwEAFKLgoJc2VjcDI1NmsxEiEDg7g0XWjWob0dk2arGtDTNlkbak2gQZtgjcrroXDYIC4",
      "dateOfIssuance": "2020-11-13T20:20:39+00:00"
    },
    "issuer": {
      "id": "did:prism:aacafb5bdb3924b7731da155d611ba0d605fb37f72313cb7c996adf564f3bc31:CoQBCoEBEkIKDm15LWlzc3Vpbmcta2V5EAJKLgoJc2VjcDI1NmsxEiECmV5Y8sjADpg9wipCFCjfWrcBcHJgu83wj8OppnPRS9oSOwoHbWFzdGVyMBABSi4KCXNlY3AyNTZrMRIhAwyfObqSiUlOL_nyJoh9efoaE5xCsWfa37Ku3XRrP2tX",
      "type": "Profile"
    }
  }
}"#;

// This blob encodes the above data in another format.
const BLOB: &[u8] = b"eyJ0eXAiOiJKV1QiLCJhbGciOiJFUzI1NksifQ.eyJpc3MiOiJkaWQ6cHJpc206Y2M3YWVhMjM4Nzk0NWY0NjdkOTliY2ZjMTBlOGRmNDdmZWUzYzUwZDJiZjVlYTY4Y2QxM2Y0MGM1NWMxNzlmZTpDczhCQ3N3QkVrSUtEbTE1TFdsemMzVnBibWN0YTJWNUVBSktMZ29KYzJWamNESTFObXN4RWlFQ2MwQTJxLW40NDZYUHRqSHhZNWV6dElfTHA1UUd6VHllOXFhN2ZWdDVDOXdTT3dvSGJXRnpkR1Z5TUJBQlNpNEtDWE5sWTNBeU5UWnJNUkloQTRvMDRjdDBxOVBMY0FlRU9tQWk4cndMOS1MUm1jNFJ5SnZNMXN1LVRnUi1Ha2tLRG1GblpXNTBMV0poYzJVdGRYSnNFaEJNYVc1clpXUlNaWE52ZFhKalpWWXhHaVZvZEhSd09pOHZNVGt5TGpFMk9DNHdMakU1TXpvNE1EZ3dMMk5zYjNWa0xXRm5aVzUwIiwibmJmIjoxNzI3OTQ2NTg1LCJleHAiOjE3Mjc5NTAxODUsInZjIjp7ImNyZWRlbnRpYWxTdWJqZWN0Ijp7Im5hdGlvbmFsSWQiOiIwMTIzNDU2Nzg5IiwiZ2l2ZW5OYW1lIjoiQWxpY2UgICAgICAgICAgICAgICAiLCJmYW1pbHlOYW1lIjoiV29uZGVybGFuZCAgICAgICAgICAiLCJpZCI6ImRpZDpwcmlzbTplZTk2ZGJhNTFiMGJhYzdmNWJjYzkyMjVkZjQyOTFjMjQ0NmM5YjM1YThjMzIyMzExODM4MGM5YzEwNjRmMTkxOkNzd0JDc2tCRWo4S0MyMTVMV0YxZEdndGEyVjVFQVJLTGdvSmMyVmpjREkxTm1zeEVpRURBVWxKOXZpa0dYRXFZU3dlR2hDWUFjbDFzWWhrVXMwQjJEU0hhSzEtY1RvU093b0hiV0Z6ZEdWeU1CQUJTaTRLQ1hObFkzQXlOVFpyTVJJaEFuUUQ3MUczZnZ2akVDOEhYTHo0MEg5T0FEbzk5NFFrQmFxbEppcHZtLUZkR2trS0RtRm5aVzUwTFdKaGMyVXRkWEpzRWhCTWFXNXJaV1JTWlhOdmRYSmpaVll4R2lWb2RIUndPaTh2TVRreUxqRTJPQzR3TGpFNU16bzRNRGt3TDJOc2IzVmtMV0ZuWlc1MCIsImJpcnRoRGF0ZSI6IjIwMDAtMTAtMTkifSwidHlwZSI6WyJWZXJpZmlhYmxlQ3JlZGVudGlhbCJdLCJAY29udGV4dCI6WyJodHRwczpcL1wvd3d3LnczLm9yZ1wvMjAxOFwvY3JlZGVudGlhbHNcL3YxIl19fQ.LSXTl1w4oWm-Ucz-fLrUuSMGkH_br1gqvqUcp2Q3pFxRLEaIvMu56Y-Gwu8F26cXLr1PcnlpFg6XRTygYstTWQ";
const PUB_KEY: &[u8] = b"AnNANqvp+OOlz7Yx8WOXs7SPy6eUBs08nvamu31beQvc";

type PK = Secp256k1;
type Payload = [Byte; 1373];

#[derive(Clone, Default)]
struct AtalaJsonECDSA {
    // Public inputs:
    pk: Value<PK>,

    // Witnesses:
    payload: Value<Payload>,
    signature: Value<ECDSASig>,
}

impl Relation for AtalaJsonECDSA {
    type Instance = PK;

    type Witness = (Payload, ECDSASig);

    const K: u32 = 17;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        AssignedForeignPoint::<F, Secp256k1, MultiEmulationParams>::as_public_input(instance)
    }

    fn from_statement(instance: &Self::Instance, witness: &Self::Witness) -> Self {
        AtalaJsonECDSA {
            pk: Value::known(*instance),
            payload: Value::known(witness.0),
            signature: Value::known(witness.1),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let secp256k1_scalar = std_lib.secp256k1_scalar();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        // Assign the PK as public input.
        let pk = secp256k1_curve.assign_as_public_input(layouter, self.pk)?;

        // Assign the payload as a witness and hash it.
        let msg_hash: AssignedField<_, _, _> = {
            let payload = std_lib.assign_many(layouter, &self.payload.transpose_array())?;
            let hash_bytes = std_lib.sha256(layouter, &payload)?;
            secp256k1_scalar.assigned_from_be_bytes(layouter, &hash_bytes)?
        };

        // Assign the signature as a witness.
        let r_value = self.signature.map(|sig| sig.get_r().map(Byte));
        let r_le_bytes = std_lib.assign_many(layouter, &r_value.transpose_array())?;
        let s = secp256k1_scalar.assign(layouter, self.signature.map(|sig| sig.get_s()))?;

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
    let srs = filecoin_srs(AtalaJsonECDSA::K);

    let vk = compact_std_lib::setup_vk::<AtalaJsonECDSA>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<AtalaJsonECDSA>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<AtalaJsonECDSA>(&srs, &vk);

    // Build the instance and witness to be proven.
    let instance = Secp256k1::from_base64(PUB_KEY).expect("Base64 encoded PK");
    let witness = AtalaJsonECDSA::witness_from_blob(BLOB);

    let proof = compact_std_lib::prove::<AtalaJsonECDSA>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<AtalaJsonECDSA>(&srs, &vk, &instance, proof)
}

// Helper functions for base64 encoded credentials.
// -----------------------------------------------

impl AtalaJsonECDSA {
    // Creates an AtalaJsonECDSA witness from:
    // 1. A JWT encoded Atala credential.
    // 2. The corresponding base64 encoded ECDSA public key.
    fn witness_from_blob(blob: &[u8]) -> (Payload, ECDSASig) {
        let (payload_bytes, signature_bytes) = split_blob(blob);

        assert!(verify_credential_sig(
            PUB_KEY,
            &payload_bytes,
            &signature_bytes
        ));

        let payload = payload_bytes.into_iter().map(Byte).collect::<Vec<_>>();
        let signature = ECDSASig::from_base64(&signature_bytes).expect("Base64 encoded signature.");

        (payload.try_into().unwrap(), signature)
    }
}

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

fn verify_credential_sig(pk_base64: &[u8], msg: &[u8], sig_base64: &[u8]) -> bool {
    let pk_affine = Secp256k1::from_base64(pk_base64).unwrap();
    let sig = ECDSASig::from_base64(sig_base64).unwrap();

    let mut msg_hash_bytes: [u8; 32] = sha2::Sha256::digest(msg).into();
    msg_hash_bytes.reverse(); // BE to LE
    let msg_scalar = secp256k1Scalar::from_bytes(&msg_hash_bytes).unwrap();

    Ecdsa::verify(&pk_affine, &msg_scalar, &sig)
}

// Generate random key pair and a signature of DATA for the example.
fn _random() -> AtalaJsonECDSA {
    let mut rng = ChaChaRng::seed_from_u64(0x00c0ffee);
    let (pk, sk) = Ecdsa::keygen(&mut rng);

    let mut msg_hash_bytes: [u8; 32] = sha2::Sha256::digest(_DATA).into();
    msg_hash_bytes.reverse(); // BE to LE
    let msg_hash = secp256k1Scalar::from_bytes(&msg_hash_bytes).unwrap();

    let signature = Ecdsa::sign(&sk, &msg_hash, &mut rng);

    // Sanity check on the generated signature.
    assert!(Ecdsa::verify(&pk, &msg_hash, &signature));

    let payload = _DATA
        .as_bytes()
        .iter()
        .copied()
        .map(Byte)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    AtalaJsonECDSA {
        pk: Value::known(pk),
        payload: Value::known(payload),
        signature: Value::known(signature),
    }
}

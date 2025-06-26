//! Example of verifying the validity of an ECDSA signed Atala identity JSON.

use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use halo2curves::secp256k1::{Fq as secp256k1Scalar, Secp256k1};
use midnight_circuits::{
    compact_std_lib::{self, Relation, ShaTableSize, ZkStdLib, ZkStdLibArch},
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
        RangeCheckInstructions,
    },
    json::{DateFormat, Separator},
    testing_utils::{
        ecdsa::{ECDSASig, Ecdsa, FromBase64},
        plonk_api::filecoin_srs,
    },
    types::{AssignedByte, AssignedForeignPoint, Byte, InnerValue, Instantiable},
};
use num_bigint::BigUint;
use rand::rngs::OsRng;
use sha2::Digest;

type F = blstrs::Fq;

// This blob encodes a credential in JWT format.
const BLOB: &[u8] = b"eyJ0eXAiOiJKV1QiLCJhbGciOiJFUzI1NksifQ.eyJpc3MiOiJkaWQ6cHJpc206Y2M3YWVhMjM4Nzk0NWY0NjdkOTliY2ZjMTBlOGRmNDdmZWUzYzUwZDJiZjVlYTY4Y2QxM2Y0MGM1NWMxNzlmZTpDczhCQ3N3QkVrSUtEbTE1TFdsemMzVnBibWN0YTJWNUVBSktMZ29KYzJWamNESTFObXN4RWlFQ2MwQTJxLW40NDZYUHRqSHhZNWV6dElfTHA1UUd6VHllOXFhN2ZWdDVDOXdTT3dvSGJXRnpkR1Z5TUJBQlNpNEtDWE5sWTNBeU5UWnJNUkloQTRvMDRjdDBxOVBMY0FlRU9tQWk4cndMOS1MUm1jNFJ5SnZNMXN1LVRnUi1Ha2tLRG1GblpXNTBMV0poYzJVdGRYSnNFaEJNYVc1clpXUlNaWE52ZFhKalpWWXhHaVZvZEhSd09pOHZNVGt5TGpFMk9DNHdMakU1TXpvNE1EZ3dMMk5zYjNWa0xXRm5aVzUwIiwibmJmIjoxNzI3OTQ2NTg1LCJleHAiOjE3Mjc5NTAxODUsInZjIjp7ImNyZWRlbnRpYWxTdWJqZWN0Ijp7Im5hdGlvbmFsSWQiOiIwMTIzNDU2Nzg5IiwiZ2l2ZW5OYW1lIjoiQWxpY2UgICAgICAgICAgICAgICAiLCJmYW1pbHlOYW1lIjoiV29uZGVybGFuZCAgICAgICAgICAiLCJpZCI6ImRpZDpwcmlzbTplZTk2ZGJhNTFiMGJhYzdmNWJjYzkyMjVkZjQyOTFjMjQ0NmM5YjM1YThjMzIyMzExODM4MGM5YzEwNjRmMTkxOkNzd0JDc2tCRWo4S0MyMTVMV0YxZEdndGEyVjVFQVJLTGdvSmMyVmpjREkxTm1zeEVpRURBVWxKOXZpa0dYRXFZU3dlR2hDWUFjbDFzWWhrVXMwQjJEU0hhSzEtY1RvU093b0hiV0Z6ZEdWeU1CQUJTaTRLQ1hObFkzQXlOVFpyTVJJaEFuUUQ3MUczZnZ2akVDOEhYTHo0MEg5T0FEbzk5NFFrQmFxbEppcHZtLUZkR2trS0RtRm5aVzUwTFdKaGMyVXRkWEpzRWhCTWFXNXJaV1JTWlhOdmRYSmpaVll4R2lWb2RIUndPaTh2TVRreUxqRTJPQzR3TGpFNU16bzRNRGt3TDJOc2IzVmtMV0ZuWlc1MCIsImJpcnRoRGF0ZSI6IjIwMDAtMTAtMTkifSwidHlwZSI6WyJWZXJpZmlhYmxlQ3JlZGVudGlhbCJdLCJAY29udGV4dCI6WyJodHRwczpcL1wvd3d3LnczLm9yZ1wvMjAxOFwvY3JlZGVudGlhbHNcL3YxIl19fQ.LSXTl1w4oWm-Ucz-fLrUuSMGkH_br1gqvqUcp2Q3pFxRLEaIvMu56Y-Gwu8F26cXLr1PcnlpFg6XRTygYstTWQ";
const PUB_KEY: &[u8] = b"AnNANqvp+OOlz7Yx8WOXs7SPy6eUBs08nvamu31beQvc";

const PAYLOAD_LEN: usize = 1373;
// Note: Do these credentials always have the same header?
const HEADER_LEN: usize = 38;
type PK = Secp256k1;
type Payload = [Byte; PAYLOAD_LEN];

#[derive(Clone, Default)]
pub struct AtalaJsonECDSA;

impl Relation for AtalaJsonECDSA {
    type Instance = PK;
    type Witness = (Payload, ECDSASig);

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

        let payload = witness.map(|(payload, _)| payload).transpose_array();
        let sig = witness.map(|(_, sig)| sig);

        // Assign payload.
        let payload = std_lib.assign_many(layouter, &payload)?;

        // Verify credential signature.
        Self::verify_ecdsa(std_lib, layouter, pk, &payload, sig)?;

        // Decode Base64 JSON.
        let json = b64_chip.from_base64(layouter, &payload[HEADER_LEN + 1..PAYLOAD_LEN], false)?;

        // Check Name.
        let name = Self::get_property(std_lib, layouter, &json, b"givenName", 7)?;
        Self::assert_str_match(std_lib, layouter, &name[1..6], b"Alice")?;

        // Check birth date.
        let birthdate = Self::get_property(std_lib, layouter, &json, b"birthDate", 12)?;
        let limit = Date {
            day: 1,
            month: 1,
            year: 2004,
        };
        Self::assert_date_before(std_lib, layouter, &birthdate[1..11], limit)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: Some(ShaTableSize::Table11),
            secp256k1: true,
            bls12_381: false,
            base64: true,
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
        let r_value = sig.map(|sig| sig.get_r().map(Byte));
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

    /// Searches for "property": and returns the following `val_len` characters.
    fn get_property(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        body: &[AssignedByte<F>],
        property: &[u8],
        val_len: usize,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let parser = std_lib.parser();

        let property = [b"\"", property, b"\":"].concat();
        let p_len = property.len();
        let seq: Value<Vec<Byte>> = Value::from_iter(body.iter().map(|b| b.value()));
        let subseq: Vec<Byte> = property.into_iter().map(Byte).collect();

        let idx = seq.map(|seq| {
            let idx =
                find_subsequence(&seq, &subseq).expect("Property should appear in the credential.");
            F::from(idx as u64)
        });

        let idx = std_lib.assign(layouter, idx)?; // idx will be range-checked in `fetch_bytes`.

        let raw_propety = parser.fetch_bytes(layouter, body, &idx, p_len + val_len)?;
        Ok(raw_propety[p_len..].to_vec())
    }

    fn assert_str_match(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        str1: &[AssignedByte<F>],
        str2: &[u8],
    ) -> Result<(), Error> {
        assert_eq!(
            str1.len(),
            str2.len(),
            "Compared string lengths must match."
        );
        for (b1, b2) in str1.iter().zip(str2.iter()) {
            std_lib.assert_equal_to_fixed(layouter, b1, Byte(*b2))?
        }
        Ok(())
    }

    fn assert_date_before(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        date: &[AssignedByte<F>],
        limit_date: Date,
    ) -> Result<(), Error> {
        let format = (DateFormat::YYYYMMDD, Separator::Sep('-'));
        let date = std_lib.parser().date_to_int(layouter, date, format)?;
        std_lib.assert_lower_than_fixed(layouter, &date, &limit_date.into())
    }
}

struct Date {
    day: u8,
    month: u8,
    year: u16,
}

impl From<Date> for BigUint {
    fn from(value: Date) -> Self {
        (value.year as u64 * 10_000 + value.month as u64 * 100 + value.day as u64).into()
    }
}

// Returns the index of a subsequence inside a larger sequence, if it is
// present. This function is made generic so it works over native types and
// values.
fn find_subsequence<T>(seq: &[T], subseq: &[T]) -> Option<usize>
where
    for<'a> &'a [T]: PartialEq,
{
    seq.windows(subseq.len())
        .position(|window| window == subseq)
}

fn main() {
    const K: u32 = 17;
    let srs = filecoin_srs(K);

    let relation = AtalaJsonECDSA;
    let vk = compact_std_lib::setup_vk(&srs, &relation);

    let pk = compact_std_lib::setup_pk(&relation, &vk);

    // Build the instance and witness to be proven.
    let instance = Secp256k1::from_base64(PUB_KEY).expect("Base64 encoded PK");
    let witness = AtalaJsonECDSA::witness_from_blob(BLOB);

    let proof = compact_std_lib::prove(&srs, &pk, &relation, &instance, witness, OsRng)
        .expect("Proof generation should not fail");

    assert!(compact_std_lib::verify::<AtalaJsonECDSA>(
        &srs.verifier_params(),
        &vk,
        &instance,
        &proof
    )
    .is_ok())
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

fn verify_credential_sig(pk_base64: &[u8], msg: &[u8], sig_base64: &[u8]) -> bool {
    let pk_affine = Secp256k1::from_base64(pk_base64).unwrap();
    let sig = ECDSASig::from_base64(sig_base64).unwrap();

    let mut msg_hash_bytes: [u8; 32] = sha2::Sha256::digest(msg).into();
    msg_hash_bytes.reverse(); // BE to LE
    let msg_scalar = secp256k1Scalar::from_bytes(&msg_hash_bytes).unwrap();

    Ecdsa::verify(&pk_affine, &msg_scalar, &sig)
}

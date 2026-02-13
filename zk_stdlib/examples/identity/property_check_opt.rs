//! Optimized example of property proofs in a JSON credential.
//!
//! This is an alternative to `property_check.rs` that replaces the
//! automaton-based in-circuit parsing with
//! [`check_bytes`](midnight_circuits::parsing::ScannerChip::check_bytes)
//! substring verification. Much more efficient, but less general technique that
//! is not always applicable.
//!
//! # Trust assumption
//!
//! Unlike the automaton-based version, this circuit does **not** verify the
//! structural correctness of the credential (e.g. valid JSON, UTF-8 encoding).
//! It assumes the credential is well-formed and that field names are unique,
//! which is guaranteed by the issuer whose signature has been verified.
//! It also assumes there is no insignificant whitespace around `:` separators.

use std::time::Instant;

use base64::{decode_config, STANDARD_NO_PAD};
use midnight_circuits::{
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        public_input::CommittedInstanceInstructions, AssertionInstructions, AssignmentInstructions,
        Base64Instructions, DecompositionInstructions, EccInstructions, RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator},
    testing_utils::ecdsa::{ECDSASig, FromBase64},
    types::{AssignedByte, AssignedForeignPoint, AssignedNative},
};
use midnight_curves::{
    secp256k1::{Fq as secp256k1Scalar, Secp256k1},
    G1Affine,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{commit_to_instances, Error},
    poly::kzg::KZGCommitmentScheme,
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use num_bigint::BigUint;
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

// Secret key of the credential holder.
const HOLDER_SK: SK = SK::from_raw([
    0x87c251f40ac6a55e,
    0xc82dbae785c00836,
    0x36f09fcb94100833,
    0xc4e05a8ec16835ce,
]);

const HEADER_LEN: usize = 38;
const PAYLOAD_LEN: usize = 2463;

// Credential payload.
type Payload = [u8; PAYLOAD_LEN];
// Holder secret key.
type SK = secp256k1Scalar;

#[derive(Clone, Default)]
pub struct CredentialPropertyOpt;

const MAX_VALID_DATE: Date = Date {
    day: 1,
    month: 1,
    year: 2004,
};

const VALID_NAME: &[u8] = b"Alice";
const NAME_LEN: usize = VALID_NAME.len(); // TODO: this value should not be fixed.
const BIRTHDATE_LEN: usize = 10;
const COORD_LEN: usize = 43;

impl Relation for CredentialPropertyOpt {
    type Instance = ();
    type Witness = (Payload, SK);

    fn format_instance(_instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![])
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
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let b64_chip = std_lib.base64();

        let (payload, sk) = witness.unzip();

        // Decode Base64 JSON off-circuit (for finding snippet positions).
        let decoded: Value<Vec<u8>> = payload.map(|p| {
            let json_b64 = &p[HEADER_LEN + 1..PAYLOAD_LEN];
            decode_config(json_b64, STANDARD_NO_PAD).expect("Valid base64 encoded JSON.")
        });

        // Assign decoded JSON bytes.
        let json_len = (PAYLOAD_LEN - (HEADER_LEN + 1)) / 4 * 3;
        let json: Vec<AssignedByte<F>> = {
            let vals = decoded.clone().transpose_vec(json_len);
            std_lib.assign_many(layouter, vals.as_slice())?
        };

        // Constrain as committed instance (to link with enrollment proof).
        for byte in json.iter() {
            let byte_as_f: AssignedNative<_> = byte.into();
            std_lib.constrain_as_committed_public_input(layouter, &byte_as_f)?;
        }

        // Name check.
        let name = Self::get_property(std_lib, layouter, &json, &decoded, b"givenName", NAME_LEN)?;
        Self::assert_str_match(std_lib, layouter, &name, VALID_NAME)?;

        // Birthdate check.
        let birthdate = Self::get_property(
            std_lib,
            layouter,
            &json,
            &decoded,
            b"birthDate",
            BIRTHDATE_LEN,
        )?;
        Self::assert_date_before(std_lib, layouter, &birthdate, MAX_VALID_DATE)?;

        // Extract `x` field.
        let x = Self::get_property(std_lib, layouter, &json, &decoded, b"x", COORD_LEN)?;

        // Extract `y` field.
        let y = Self::get_property(std_lib, layouter, &json, &decoded, b"y", COORD_LEN)?;

        let x_val = b64_chip.decode_base64url(layouter, &x, false)?;
        let y_val = b64_chip.decode_base64url(layouter, &y, false)?;

        // Check knowledge of corresponding sk.
        let x_coord = secp256k1_curve
            .base_field_chip()
            .assigned_from_be_bytes(layouter, &x_val[..32])?;
        let y_coord = secp256k1_curve
            .base_field_chip()
            .assigned_from_be_bytes(layouter, &y_val[..32])?;

        let holder_pk = secp256k1_curve.point_from_coordinates(layouter, &x_coord, &y_coord)?;
        let holder_sk: AssignedField<_, secp256k1Scalar, MultiEmulationParams> =
            std_lib.secp256k1_scalar().assign(layouter, sk)?;

        let gen: AssignedForeignPoint<_, Secp256k1, MultiEmulationParams> =
            secp256k1_curve.assign_fixed(layouter, Secp256k1::generator())?;
        let must_be_pk = secp256k1_curve.msm(layouter, &[holder_sk], &[gen])?;
        secp256k1_curve.assert_equal(layouter, &holder_pk, &must_be_pk)?;

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            secp256k1: true,
            base64: true,
            automaton: true,
            nr_pow2range_cols: 3,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(CredentialPropertyOpt)
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

impl CredentialPropertyOpt {
    /// Verifies that a JSON field appears in the credential and extracts its
    /// value.
    ///
    /// Given a field name (e.g., `b"birthDate"`) and value length, this
    /// function builds the full prefix `"<field_name>":"` internally, then:
    /// 1. Finds the field in the decoded credential (off-circuit).
    /// 2. Assigns the prefix as fixed constants and the value as witness bytes.
    /// 3. Uses `check_bytes` to verify the full snippet (prefix + value +
    ///    closing `"`) is a substring of the credential.
    /// 4. Returns the extracted value bytes.
    fn get_property(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        cred: &[AssignedByte<F>],
        decoded: &Value<Vec<u8>>,
        field_name: &[u8],
        value_len: usize,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let field_prefix: Vec<u8> = [b"\"".as_slice(), field_name, b"\":\""].concat();
        let snippet_len = field_prefix.len() + value_len + 1; // +1 for closing quote.

        // Off-circuit: find the snippet position and extract the value.
        let (value_raw, idx_val): (Value<Vec<u8>>, Value<F>) = decoded
            .as_ref()
            .map(|d| {
                let pos = d
                    .windows(field_prefix.len())
                    .position(|w| w == field_prefix.as_slice())
                    .expect("Field prefix should appear in credential");
                assert!(
                    pos + snippet_len <= d.len(),
                    "Snippet exceeds credential length"
                );
                let value =
                    d[pos + field_prefix.len()..pos + field_prefix.len() + value_len].to_vec();
                (value, F::from(pos as u64))
            })
            .unzip();

        // Assign prefix as fixed constants.
        let prefix_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many_fixed(layouter, &field_prefix)?;

        // Assign value from witness.
        let value_data = value_raw.transpose_vec(value_len);
        let value_bytes: Vec<AssignedByte<F>> =
            std_lib.assign_many(layouter, value_data.as_slice())?;

        // Assign closing quote as fixed.
        let closing_quote: AssignedByte<F> = std_lib.assign_fixed(layouter, b'"')?;

        // Build full snippet: prefix || value || closing quote.
        let snippet_bytes: Vec<AssignedByte<F>> = prefix_bytes
            .into_iter()
            .chain(value_bytes.iter().cloned())
            .chain(std::iter::once(closing_quote))
            .collect();
        assert_eq!(snippet_bytes.len(), snippet_len);

        let idx: AssignedNative<F> = std_lib.assign(layouter, idx_val)?;
        std_lib.scanner(false).check_bytes(layouter, cred, &idx, &snippet_bytes)?;

        Ok(value_bytes)
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
            std_lib.assert_equal_to_fixed(layouter, b1, *b2)?
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

    // Creates a CredentialPropertyOpt witness from:
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
}

fn main() {
    const K: u32 = 15;
    let srs = filecoin_srs(K);
    let credential_blob = read_credential::<4096>(CRED_PATH).expect("Path to credential file.");

    let relation = CredentialPropertyOpt;

    let start = |msg: &str| -> Instant {
        println!("{msg}");
        Instant::now()
    };

    let setup = start("Setting up the vk/pk");
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    println!("... done ({:?})", setup.elapsed());

    // Build the instance and witness to be proven.
    let wit = start("Computing instance and witnesses");
    let witness = CredentialPropertyOpt::witness_from_blob(credential_blob.as_slice());
    let witness = (witness.0, HOLDER_SK);

    let committed_credential: G1Affine = {
        let instance = CredentialPropertyOpt::format_committed_instances(&witness);
        commit_to_instances::<_, KZGCommitmentScheme<_>>(&srs, vk.vk().get_domain(), &instance)
            .into()
    };
    println!("... done ({:?})", wit.elapsed());

    let p = start("Proof generation");
    let proof = midnight_zk_stdlib::prove::<CredentialPropertyOpt, blake2b_simd::State>(
        &srs,
        &pk,
        &relation,
        &(),
        witness,
        OsRng,
    )
    .expect("Proof generation should not fail");
    println!("... done ({:?})", p.elapsed());

    let v = start("Proof verification");
    assert!(
        midnight_zk_stdlib::verify::<CredentialPropertyOpt, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &(),
            Some(committed_credential),
            &proof
        )
        .is_ok()
    );
    println!("... done ({:?})", v.elapsed())
}

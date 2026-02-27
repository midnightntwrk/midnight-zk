//! Example of property proofs in a JSON credential. Is parsed with an
//! automaton-based technique.
//!
//! NB: The automaton-based technique is a bit overkill for this kind of
//! credential that have a lot of structure. Typically, instead of parsing the
//! full credential structure, one could simply scan the input to search for the
//! field names ("givenName", "birthDate"...). This is actually what is done in
//! `property_check_opt.rs`, which is much more efficient. The present example
//! should rather be seen as an illustration of the use of the automaton chip,
//! useful in cases of less structured credentials, without keywords (e.g.,
//! ASN.1 encodings).

use std::time::Instant;

use base64::{decode_config, STANDARD_NO_PAD};
use midnight_circuits::{
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        public_input::CommittedInstanceInstructions, AssertionInstructions, AssignmentInstructions,
        Base64Instructions, ControlFlowInstructions, DecompositionInstructions, EccInstructions,
        EqualityInstructions, RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator, StdLibParser},
    testing_utils::ecdsa::{ECDSASig, FromBase64},
    types::{AssignedByte, AssignedForeignPoint, AssignedNative},
    CircuitField,
};
use midnight_curves::{
    k256::{Fq as K256Scalar, K256},
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

// Secret key of the credential holder (big-endian bytes).
const HOLDER_SK_BYTES: [u8; 32] = [
    0xc4, 0xe0, 0x5a, 0x8e, 0xc1, 0x68, 0x35, 0xce, 0x36, 0xf0, 0x9f, 0xcb, 0x94, 0x10, 0x08, 0x33,
    0xc8, 0x2d, 0xba, 0xe7, 0x85, 0xc0, 0x08, 0x36, 0x87, 0xc2, 0x51, 0xf4, 0x0a, 0xc6, 0xa5, 0x5e,
];

const HEADER_LEN: usize = 38;
const PAYLOAD_LEN: usize = 2463;

// Credential payload.
type Payload = [u8; PAYLOAD_LEN];
// Holder secret key.
type SK = K256Scalar;

#[derive(Clone, Default)]
pub struct CredentialProperty;

const MAX_VALID_DATE: Date = Date {
    day: 1,
    month: 1,
    year: 2004,
};

const VALID_NAME: &[u8] = b"Alice";
const NAME_LEN: usize = VALID_NAME.len(); // TODO: this value should not be fixed.
const BIRTHDATE_LEN: usize = 10;
const COORD_LEN: usize = 43;

impl Relation for CredentialProperty {
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
        let scanner_chip = std_lib.scanner();

        let (json, sk) = witness.unzip();

        // Assign decoded Base64 JSON
        let json: Vec<AssignedByte<_>> = {
            let len = (PAYLOAD_LEN - (HEADER_LEN + 1)) / 4 * 3;
            let vals = json
                .map(|json| {
                    let json_b64 = &json[HEADER_LEN + 1..PAYLOAD_LEN];
                    decode_config(json_b64, STANDARD_NO_PAD).expect("Valid base64 encoded JSON.")
                })
                .transpose_vec(len);
            std_lib.assign_many(layouter, vals.as_slice())?
        };

        // Constrains as committed instance (to link with enrollment proof).
        for byte in json.iter() {
            let byte_as_f: AssignedNative<_> = byte.into();
            std_lib.constrain_as_committed_public_input(layouter, &byte_as_f)?;
        }

        let parsed_json = scanner_chip.parse(layouter, StdLibParser::Jwt.into(), &json)?;

        // Check Name.
        let name = Self::get_property(std_lib, layouter, &json, &parsed_json, 3, NAME_LEN)?;
        Self::assert_str_match(std_lib, layouter, &name, VALID_NAME)?;

        // Check birth date.
        let birthdate =
            Self::get_property(std_lib, layouter, &json, &parsed_json, 4, BIRTHDATE_LEN)?;
        Self::assert_date_before(std_lib, layouter, &birthdate, MAX_VALID_DATE)?;

        // Get holder public key.
        let x = Self::get_property(std_lib, layouter, &json, &parsed_json, 5, COORD_LEN)?;
        let y = Self::get_property(std_lib, layouter, &json, &parsed_json, 6, COORD_LEN)?;
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
        let holder_sk: AssignedField<_, K256Scalar, MultiEmulationParams> =
            std_lib.secp256k1_scalar().assign(layouter, sk)?;

        let gen: AssignedForeignPoint<_, K256, MultiEmulationParams> =
            secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let must_be_pk = secp256k1_curve.msm(layouter, &[holder_sk], &[gen])?;
        secp256k1_curve.assert_equal(layouter, &holder_pk, &must_be_pk)?;

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
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
        Ok(CredentialProperty)
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

impl CredentialProperty {
    /// Searches for the first position in `parsed_body` marked with `marker`,
    /// and returns the following `val_len` bytes from `body`.
    fn get_property(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        body: &[AssignedByte<F>],
        parsed_body: &[AssignedNative<F>],
        marker: usize,
        val_len: usize,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let marker_f = F::from(marker as u64);

        // In-circuit scan: find the first position of `marker` in `parsed_body`.
        // Iterating in reverse so that the final overwrite is the first occurrence of
        // the marker.
        let mut idx: AssignedNative<F> = std_lib.assign_fixed(layouter, F::from(0u64))?;
        for (i, m) in parsed_body.iter().enumerate().rev() {
            let is_match = std_lib.is_equal_to_fixed(layouter, m, marker_f)?;
            let i_val: AssignedNative<F> = std_lib.assign_fixed(layouter, F::from(i as u64))?;
            idx = std_lib.select(layouter, &is_match, &i_val, &idx)?;
        }

        std_lib.parser().fetch_bytes(layouter, body, &idx, val_len)
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
    // Creates an CredentialProperty witness from:
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
    const K: u32 = 16;
    let srs = filecoin_srs(K);
    let credential_blob = read_credential::<4096>(CRED_PATH).expect("Path to credential file.");

    let relation = CredentialProperty;

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
    let witness = CredentialProperty::witness_from_blob(credential_blob.as_slice());
    let holder_sk = K256Scalar::from_bytes_be(&HOLDER_SK_BYTES).expect("Valid scalar");
    let witness = (witness.0, holder_sk);

    let committed_credential: G1Affine = {
        let instance = CredentialProperty::format_committed_instances(&witness);
        commit_to_instances::<_, KZGCommitmentScheme<_>>(&srs, vk.vk().get_domain(), &instance)
            .into()
    };
    println!("... done ({:?})", wit.elapsed());

    let p = start("Proof generation");
    let proof = midnight_zk_stdlib::prove::<CredentialProperty, blake2b_simd::State>(
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
        midnight_zk_stdlib::verify::<CredentialProperty, blake2b_simd::State>(
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

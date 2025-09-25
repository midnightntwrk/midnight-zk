//! Example of verifying the validity of an ECDSA signed Atala identity JSON.
//!
//! This is an experimental improvement of `json_verification.rs` which includes
//! the automaton chip to parse credentials.

use std::time::Instant;

use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    instructions::{
        AssertionInstructions, AssignmentInstructions, Base64Instructions, RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator, StdLibParser},
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedByte, AssignedNative},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

// This blob encodes a credential in JWT format.
const BLOB: &[u8] = b"eyJ0eXAiOiJKV1QiLCJhbGciOiJFUzI1NksifQ.eyJpc3MiOiJkaWQ6cHJpc206OTU0ZTU5ZWE0YzIxMmY0YjRiZTg2ODhiZDNmZTYzZGQ3MDc5ZDIxOGVmNjI4MjIwNWE3MDEzMWY4N2YyODg3YyIsInN1YiI6ImRpZDpwcmlzbTo3M2JiNTE2ZmU4OGJlZWM1YjNiOGQyODNlYWVjNTk2NGQxYzEzY2Q1NGVmOGYxNzg0MjE3ZjRmZTQyNjg4NjI2OkN0UUJDdEVCRWtnS0ZHMTVMV0YxZEdndGEyVjVMVzFwWkc1cFoyaDBFQVJLTGdvSmMyVmpjREkxTm1zeEVpRUNTMGtqM3lkU2VGODZMVTlCcEh1Vm50TUZOOFNDS2NIeWNpMXRYRmJSVzhNU093b0hiV0Z6ZEdWeU1CQUJTaTRLQ1hObFkzQXlOVFpyTVJJaEFpbVdEZ2dORHN3QUlKV0tiZXhrZkR4VjBQRWE1OHRjVmNTMWRrMnBoa0RqR2tnS0RtRm5aVzUwTFdKaGMyVXRkWEpzRWhCTWFXNXJaV1JTWlhOdmRYSmpaVll4R2lSb2RIUndPaTh2TVRreUxqRTJPQzR4TGpnMk9qZ3pNREF2WTJ4dmRXUXRZV2RsYm5RIiwibmJmIjoxNzQwNDgyMTc1LCJleHAiOjE3NDA0ODU3NzUsInZjIjp7ImNyZWRlbnRpYWxTY2hlbWEiOlt7ImlkIjoiaHR0cDpcL1wvMTkyLjE2OC4xLjg2Ojg0MDBcL2Nsb3VkLWFnZW50XC9zY2hlbWEtcmVnaXN0cnlcL3NjaGVtYXNcLzJmY2ZlZWFlLTk1MzItMzg2OS1hZDg5LWNkZjUwNjBjM2EzYyIsInR5cGUiOiJDcmVkZW50aWFsU2NoZW1hMjAyMiJ9XSwiY3JlZGVudGlhbFN1YmplY3QiOnsibmF0aW9uYWxJZCI6IjEyMzQ1IiwiZmFtaWx5TmFtZSI6IldvbmRlcmxhbmQiLCJnaXZlbk5hbWUiOiJBbGljZSIsInB1YmxpY0tleUp3ayI6eyJrdHkiOiJFQyIsImNydiI6InNlY3AyNTZrMSIsIngiOiJTMGtqM3lkU2VGODZMVTlCcEh1Vm50TUZOOFNDS2NIeWNpMXRYRmJSVzhNIiwieSI6ImR1eDhoLVFjSUEzYVpHOUNTUElsdER3VnZPa2Ywa2ZKUkpMSDdLMUtTbFEifSwiaWQiOiJkaWQ6cHJpc206NzNiYjUxNmZlODhiZWVjNWIzYjhkMjgzZWFlYzU5NjRkMWMxM2NkNTRlZjhmMTc4NDIxN2Y0ZmU0MjY4ODYyNjpDdFFCQ3RFQkVrZ0tGRzE1TFdGMWRHZ3RhMlY1TFcxcFpHNXBaMmgwRUFSS0xnb0pjMlZqY0RJMU5tc3hFaUVDUzBrajN5ZFNlRjg2TFU5QnBIdVZudE1GTjhTQ0tjSHljaTF0WEZiUlc4TVNPd29IYldGemRHVnlNQkFCU2k0S0NYTmxZM0F5TlRack1SSWhBaW1XRGdnTkRzd0FJSldLYmV4a2ZEeFYwUEVhNTh0Y1ZjUzFkazJwaGtEakdrZ0tEbUZuWlc1MExXSmhjMlV0ZFhKc0VoQk1hVzVyWldSU1pYTnZkWEpqWlZZeEdpUm9kSFJ3T2k4dk1Ua3lMakUyT0M0eExqZzJPamd6TURBdlkyeHZkV1F0WVdkbGJuUSIsImJpcnRoRGF0ZSI6IjIwMDAtMTEtMTMifSwidHlwZSI6WyJWZXJpZmlhYmxlQ3JlZGVudGlhbCJdLCJAY29udGV4dCI6WyJodHRwczpcL1wvd3d3LnczLm9yZ1wvMjAxOFwvY3JlZGVudGlhbHNcL3YxIl0sImlzc3VlciI6eyJpZCI6ImRpZDpwcmlzbTo5NTRlNTllYTRjMjEyZjRiNGJlODY4OGJkM2ZlNjNkZDcwNzlkMjE4ZWY2MjgyMjA1YTcwMTMxZjg3ZjI4ODdjIiwidHlwZSI6IlByb2ZpbGUifSwiY3JlZGVudGlhbFN0YXR1cyI6eyJzdGF0dXNQdXJwb3NlIjoiUmV2b2NhdGlvbiIsInN0YXR1c0xpc3RJbmRleCI6MywiaWQiOiJodHRwOlwvXC8xOTIuMTY4LjEuODY6ODQwMFwvY2xvdWQtYWdlbnRcL2NyZWRlbnRpYWwtc3RhdHVzXC8yMDU0ZTJlYS1mMTkxLTQ2NDAtODZkZC02ZGRlNmIyZjc3ZjcjMyIsInR5cGUiOiJTdGF0dXNMaXN0MjAyMUVudHJ5Iiwic3RhdHVzTGlzdENyZWRlbnRpYWwiOiJodHRwOlwvXC8xOTIuMTY4LjEuODY6ODQwMFwvY2xvdWQtYWdlbnRcL2NyZWRlbnRpYWwtc3RhdHVzXC8yMDU0ZTJlYS1mMTkxLTQ2NDAtODZkZC02ZGRlNmIyZjc3ZjcifX19.WT3rH0dikzIy00nauqXJHep1xY9ToezY2i0HJJS-5LU2ykBDYv3xzzeruckIRjDmuO7XAco5S9n4KjQp_ivbpg";

// The credential in question. Just keeping it for reference.
const _INPUT: &str = r#"{
    \"iss\":\"did:prism:954e59ea4c212f4b4be8688bd3fe63dd7079d218ef6282205a70131f87f2887c\",
    \"sub\":\"did:prism:73bb516fe88beec5b3b8d283eaec5964d1c13cd54ef8f1784217f4fe42688626:CtQBCtEBEkgKFG15LWF1dGgta2V5LW1pZG5pZ2h0EARKLgoJc2VjcDI1NmsxEiECS0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8MSOwoHbWFzdGVyMBABSi4KCXNlY3AyNTZrMRIhAimWDggNDswAIJWKbexkfDxV0PEa58tcVcS1dk2phkDjGkgKDmFnZW50LWJhc2UtdXJsEhBMaW5rZWRSZXNvdXJjZVYxGiRodHRwOi8vMTkyLjE2OC4xLjg2OjgzMDAvY2xvdWQtYWdlbnQ\",
    \"nbf\":1740482175,
    \"exp\":1740485775,
    \"vc\":{
       \"credentialSchema\":[
          {
             \"id\":\"http:\/\/192.168.1.86:8400\/cloud-agent\/schema-registry\/schemas\/2fcfeeae-9532-3869-ad89-cdf5060c3a3c\",
             \"type\":\"CredentialSchema2022\"
          }
       ],
       \"credentialSubject\":{
          \"nationalId\":\"12345\",
          \"familyName\":\"Wonderland\",
          \"givenName\":\"Alice\",
          \"publicKeyJwk\":{
             \"kty\":\"EC\",
             \"crv\":\"secp256k1\",
             \"x\":\"S0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8M\",
             \"y\":\"dux8h-QcIA3aZG9CSPIltDwVvOkf0kfJRJLH7K1KSlQ\"
          },
          \"id\":\"did:prism:73bb516fe88beec5b3b8d283eaec5964d1c13cd54ef8f1784217f4fe42688626:CtQBCtEBEkgKFG15LWF1dGgta2V5LW1pZG5pZ2h0EARKLgoJc2VjcDI1NmsxEiECS0kj3ydSeF86LU9BpHuVntMFN8SCKcHyci1tXFbRW8MSOwoHbWFzdGVyMBABSi4KCXNlY3AyNTZrMRIhAimWDggNDswAIJWKbexkfDxV0PEa58tcVcS1dk2phkDjGkgKDmFnZW50LWJhc2UtdXJsEhBMaW5rZWRSZXNvdXJjZVYxGiRodHRwOi8vMTkyLjE2OC4xLjg2OjgzMDAvY2xvdWQtYWdlbnQ\",
          \"birthDate\":\"2000-11-13\"
       },
       \"type\":[
          \"VerifiableCredential\"
       ],
       \"@context\":[
          \"https:\/\/www.w3.org\/2018\/credentials\/v1\"
       ],
       \"issuer\":{
          \"id\":\"did:prism:954e59ea4c212f4b4be8688bd3fe63dd7079d218ef6282205a70131f87f2887c\",
          \"type\":\"Profile\"
       },
       \"credentialStatus\":{
          \"statusPurpose\":\"Revocation\",
          \"statusListIndex\":3,
          \"id\":\"http:\/\/192.168.1.86:8400\/cloud-agent\/credential-status\/2054e2ea-f191-4640-86dd-6dde6b2f77f7#3\",
          \"type\":\"StatusList2021Entry\",
          \"statusListCredential\":\"http:\/\/192.168.1.86:8400\/cloud-agent\/credential-status\/2054e2ea-f191-4640-86dd-6dde6b2f77f7\"
       }
    }
}"#;

const _INPUT_LEN: usize = _INPUT.len();

const PAYLOAD_LEN: usize = 2424; // 2463 if we include the header.

// Credential payload.
type Payload = [u8; PAYLOAD_LEN];

#[derive(Clone, Default)]
pub struct AtalaJsonECDSA;

const MAX_VALID_DATE: Date = Date {
    day: 1,
    month: 1,
    year: 2004,
};
const VALID_NAME: &[u8] = b"Alice";
const NAME_LEN: usize = VALID_NAME.len(); // TODO: this value should not be fixed.
const BIRTHDATE_LEN: usize = 10;
const COORD_LEN: usize = 43;

impl Relation for AtalaJsonECDSA {
    type Instance = ();
    type Witness = Payload;

    fn format_instance(_instance: &Self::Instance) -> Vec<F> {
        vec![]
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let b64_chip = std_lib.base64();
        let automaton_chip = std_lib.automaton();

        // Assign payload.
        let payload = std_lib.assign_many(layouter, &witness.transpose_array())?;

        // Decode Base64 JSON.
        let json = b64_chip.decode_base64(layouter, &payload[..PAYLOAD_LEN], false)?;
        let parsed_json = automaton_chip.parse(layouter, &StdLibParser::Jwt, &json)?;

        // Check Name.
        let name = Self::get_property(std_lib, layouter, &json, &parsed_json, 3, NAME_LEN)?;
        Self::assert_str_match(std_lib, layouter, &name, VALID_NAME)?;

        // Check birth date.
        let birthdate =
            Self::get_property(std_lib, layouter, &json, &parsed_json, 4, BIRTHDATE_LEN)?;
        Self::assert_date_before(std_lib, layouter, &birthdate, MAX_VALID_DATE)?;

        // Gets points x and y. Not used here, but still adding them for performance
        // measurement.
        // Get holder public key.
        let x = Self::get_property(std_lib, layouter, &json, &parsed_json, 5, COORD_LEN)?;
        let y = Self::get_property(std_lib, layouter, &json, &parsed_json, 6, COORD_LEN)?;
        let _x_val = b64_chip.decode_base64url(layouter, &x, false)?;
        let _y_val = b64_chip.decode_base64url(layouter, &y, false)?;

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            secp256k1: true,
            bls12_381: false,
            base64: true,
            nr_pow2range_cols: 3,
            automaton: true,
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
    /// Searches for "property": and returns the following `val_len` characters.
    fn get_property(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        body: &[AssignedByte<F>],
        parsed_body: &[AssignedNative<F>],
        marker: usize,
        val_len: usize,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let parser = std_lib.parser();
        let parsed_seq: Value<Vec<F>> =
            Value::from_iter(parsed_body.iter().map(|b| b.value().copied()));
        let idx = parsed_seq.map(|parsed_seq| {
            let idx = parsed_seq
                .iter()
                .position(|&m| m == F::from(marker as u64))
                .expect("Property should appear in the credential.");
            F::from(idx as u64)
        });

        let idx = std_lib.assign(layouter, idx)?; // idx will be range-checked in `fetch_bytes`.
        parser.fetch_bytes(layouter, body, &idx, val_len)
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

fn main() {
    const K: u32 = 14;
    let srs = filecoin_srs(K);

    let relation = AtalaJsonECDSA;

    let start = |msg: &str| -> Instant {
        println!("{msg}");
        Instant::now()
    };

    let setup = start("Setting up the vk/pk");
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);
    println!("... done ({:?})", setup.elapsed());

    // Build the instance and witness to be proven.
    let wit = start("Computing instance and witnesses");
    let witness = AtalaJsonECDSA::witness_from_blob(BLOB);
    println!("... done ({:?})", wit.elapsed());

    let p = start("Proof generation");
    let proof = compact_std_lib::prove::<AtalaJsonECDSA, blake2b_simd::State>(
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
        compact_std_lib::verify::<AtalaJsonECDSA, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &(),
            None,
            &proof,
        )
        .is_ok()
    );
    println!("... done ({:?})", v.elapsed())
}

// Helper functions for base64 encoded credentials.
// -----------------------------------------------
impl AtalaJsonECDSA {
    // Creates an AtalaJsonECDSA witness from:
    // 1. A JWT encoded Atala credential.
    // 2. The corresponding base64 encoded ECDSA public key.
    fn witness_from_blob(blob: &[u8]) -> Payload {
        let mut parts = blob.split(|char| *char as char == '.');

        let _header = parts.next().unwrap();
        let body = parts.next().unwrap();
        let _signature = parts.next().unwrap();

        assert!(parts.next().is_none());
        body.try_into().unwrap_or_else(|_| {
            panic!(
                "Payload of incorrect length {}, instead of expected {}",
                body.len(),
                PAYLOAD_LEN
            )
        })
    }
}

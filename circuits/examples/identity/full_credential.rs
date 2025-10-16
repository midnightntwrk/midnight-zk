//! Full example of a proof of validity and attributed in a ECDSA signed
//! credential.

use std::{io::Write, time::Instant};

use halo2curves::secp256k1::{Fq as secp256k1Scalar, Secp256k1};
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, Base64Instructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
        RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator},
    testing_utils::{
        ecdsa::{ECDSASig, FromBase64, PublicKey},
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
use utils::{read_credential, split_blob, verify_credential_sig};

#[path = "./utils.rs"]
mod utils;
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
pub struct FullCredential;

impl Relation for FullCredential {
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
        Self::assert_date_before(std_lib, layouter, &birthdate[1..11], limit)?;

        // Get holder public key.
        let holder_key = Self::get_property(std_lib, layouter, &json, b"publicKeyJwk", 220)?;
        let x = Self::get_property(std_lib, layouter, &holder_key, b"x", 45)?;
        let y = Self::get_property(std_lib, layouter, &holder_key, b"y", 45)?;
        let x_val = b64_chip.decode_base64url(layouter, &x[1..44], false)?;
        let y_val = b64_chip.decode_base64url(layouter, &y[1..44], false)?;

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
        Ok(FullCredential)
    }
}

impl FullCredential {
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
        let seq: Value<Vec<u8>> = Value::from_iter(body.iter().map(|b| b.value()));

        let idx = seq.map(|seq| {
            let idx = find_subsequence(&seq, &property)
                .expect("Property should appear in the credential.");
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

// Returns the index of a subsequence inside a larger sequence, if it is
// present. This function is made generic so it works over native types and
// values.
fn find_subsequence<T>(seq: &[T], subseq: &[T]) -> Option<usize>
where
    for<'a> &'a [T]: PartialEq,
{
    seq.windows(subseq.len()).position(|window| window == subseq)
}

fn main() {
    const K: u32 = 17;
    let srs = filecoin_srs(K);
    let credential_blob = read_credential::<4096>(CRED_PATH).expect("Path to credential file.");

    let relation = FullCredential;

    let start = |msg: &str| -> Instant {
        print!("{msg}");
        let _ = std::io::stdout().flush();
        Instant::now()
    };

    let setup = start("Setting up the vk/pk");
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);
    println!("... done\n{:?}", setup.elapsed());

    // Build the instance and witness to be proven.
    let wit = start("Computing instance and witnesses");
    let instance = PublicKey::from_base64(PUB_KEY).expect("Base64 encoded PK");
    let witness = FullCredential::witness_from_blob(credential_blob.as_slice());
    let witness = (witness.0, witness.1, HOLDER_SK);
    println!("... done ({:?})", wit.elapsed());

    let p = start("Proof generation");
    let proof = compact_std_lib::prove::<FullCredential, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail.");
    println!("... done\n{:?}", p.elapsed());

    let v = start("Proof verification");
    assert!(
        compact_std_lib::verify::<FullCredential, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    );
    println!("... done\n{:?}", v.elapsed())
}

impl FullCredential {
    // Creates an witness from:
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

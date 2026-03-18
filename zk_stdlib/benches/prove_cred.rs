//! Criterion benchmark for full_credential proving (k=17) with optional MSM timing.
//!
//! Run with MSM timing enabled:
//! ```sh
//! MSM_TIMING=1 cargo bench -p midnight-zk-stdlib --bench prove_cred
//! ```

#[macro_use]
extern crate criterion;

use std::cell::RefCell;
use std::fs::OpenOptions;
use std::io::Read;
use std::time::Duration;

use criterion::Criterion;
use midnight_circuits::{
    field::foreign::{params::MultiEmulationParams, AssignedField},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, Base64Instructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
        RangeCheckInstructions,
    },
    parsing::{DateFormat, Separator},
    testing_utils::ecdsa::{ECDSASig, Ecdsa, FromBase64, PublicKey},
    types::{AssignedByte, AssignedForeignPoint, InnerValue, Instantiable},
    CircuitField,
};
use midnight_curves::k256::{Fq as K256Scalar, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::msm::{msm_timing_reset, msm_timing_snapshot, msm_timing_wall_clock},
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use num_bigint::BigUint;
use rand::rngs::OsRng;
use sha2::Digest;

type F = midnight_curves::Fq;

const CRED_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/identity/credentials/2k-credential"
);

const PUB_KEY: &[u8] =
    b"_bDXlQJ636HHOvXSe-flG0f-OkkRu8Jusm93PB2GBjoykg753nsOiW1vhEpCnxxybkMdarJLXIUJIYw1K2emQI";

const HOLDER_SK_BYTES: [u8; 32] = [
    0xc4, 0xe0, 0x5a, 0x8e, 0xc1, 0x68, 0x35, 0xce, 0x36, 0xf0, 0x9f, 0xcb, 0x94, 0x10, 0x08,
    0x33, 0xc8, 0x2d, 0xba, 0xe7, 0x85, 0xc0, 0x08, 0x36, 0x87, 0xc2, 0x51, 0xf4, 0x0a, 0xc6,
    0xa5, 0x5e,
];

const HEADER_LEN: usize = 38;
const PAYLOAD_LEN: usize = 2463;

type PK = K256;
type Payload = [u8; PAYLOAD_LEN];
type SK = K256Scalar;

// --- FullCredential (from zk_stdlib/examples/identity/full_credential.rs) ---

#[derive(Clone, Default)]
pub struct FullCredential;

impl Relation for FullCredential {
    type Instance = PK;
    type Witness = (Payload, ECDSASig, SK);

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(AssignedForeignPoint::<F, K256, MultiEmulationParams>::as_public_input(instance))
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

        let pk = secp256k1_curve.assign_as_public_input(layouter, instance)?;

        let payload = witness.map(|(payload, _, _)| payload).transpose_array();
        let (sig, sk) = witness.map(|(_, sig, sk)| (sig, sk)).unzip();

        let payload = std_lib.assign_many(layouter, &payload)?;

        FullCredential::verify_ecdsa(std_lib, layouter, pk, &payload, sig)?;

        let json =
            b64_chip.decode_base64(layouter, &payload[HEADER_LEN + 1..PAYLOAD_LEN], false)?;

        let name = FullCredential::get_property(std_lib, layouter, &json, b"givenName", 7)?;
        FullCredential::assert_str_match(std_lib, layouter, &name[1..6], b"Alice")?;

        let birthdate =
            FullCredential::get_property(std_lib, layouter, &json, b"birthDate", 12)?;
        let limit = Date {
            day: 1,
            month: 1,
            year: 2004,
        };
        FullCredential::assert_date_before(std_lib, layouter, &birthdate[1..11], limit)?;

        let holder_key =
            FullCredential::get_property(std_lib, layouter, &json, b"publicKeyJwk", 220)?;
        let x = FullCredential::get_property(std_lib, layouter, &holder_key, b"x", 45)?;
        let y = FullCredential::get_property(std_lib, layouter, &holder_key, b"y", 45)?;
        let x_val = b64_chip.decode_base64url(layouter, &x[1..44], false)?;
        let y_val = b64_chip.decode_base64url(layouter, &y[1..44], false)?;

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
            nr_pow2range_cols: 3,
            ..ZkStdLibArch::default()
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
    fn verify_ecdsa(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        pk: AssignedForeignPoint<F, K256, MultiEmulationParams>,
        message: &[AssignedByte<F>],
        sig: Value<ECDSASig>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let secp256k1_scalar = std_lib.secp256k1_scalar();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        let msg_hash: AssignedField<_, _, _> = {
            let hash_bytes = std_lib.sha2_256(layouter, message)?;
            secp256k1_scalar.assigned_from_be_bytes(layouter, &hash_bytes)?
        };

        let r_value = sig.map(|sig| sig.get_r());
        let r_le_bytes = std_lib.assign_many(layouter, &r_value.transpose_array())?;
        let s = secp256k1_scalar.assign(layouter, sig.map(|sig| sig.get_s()))?;

        let r_as_scalar = secp256k1_scalar.assigned_from_le_bytes(layouter, &r_le_bytes)?;
        let r_as_base = secp256k1_base.assigned_from_le_bytes(layouter, &r_le_bytes)?;

        let r_over_s = secp256k1_scalar.div(layouter, &r_as_scalar, &s)?;
        let m_over_s = secp256k1_scalar.div(layouter, &msg_hash, &s)?;

        let gen = secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let lhs = secp256k1_curve.msm(layouter, &[m_over_s, r_over_s], &[gen, pk])?;
        let lhs_x = secp256k1_curve.x_coordinate(&lhs);

        secp256k1_base.assert_equal(layouter, &lhs_x, &r_as_base)
    }

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

        let idx = std_lib.assign(layouter, idx)?;

        let raw_property = parser.fetch_bytes(layouter, body, &idx, p_len + val_len)?;
        Ok(raw_property[p_len..].to_vec())
    }

    fn assert_str_match(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        str1: &[AssignedByte<F>],
        str2: &[u8],
    ) -> Result<(), Error> {
        assert_eq!(str1.len(), str2.len(), "Compared string lengths must match.");
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

fn find_subsequence<T>(seq: &[T], subseq: &[T]) -> Option<usize>
where
    for<'a> &'a [T]: PartialEq,
{
    seq.windows(subseq.len()).position(|window| window == subseq)
}

// --- Credential utilities (from zk_stdlib/examples/identity/utils.rs) ---

fn read_credential<const MAX: usize>(path: &str) -> Result<Vec<u8>, Error> {
    let mut fd = OpenOptions::new().read(true).open(path)?;
    let mut buf = vec![0u8; MAX];
    let len = fd.read(buf.as_mut_slice())?;
    Ok(buf[..len - 1].into())
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
    let pk_affine = K256::from_base64(pk_base64).unwrap();
    let sig = ECDSASig::from_base64(sig_base64).unwrap();

    let msg_hash_bytes: [u8; 32] = sha2::Sha256::digest(msg).into();
    let msg_scalar = K256Scalar::from_bytes_be(&msg_hash_bytes).unwrap();

    Ecdsa::verify(&pk_affine, &msg_scalar, &sig)
}

fn witness_from_blob(blob: &[u8]) -> (Payload, ECDSASig) {
    let (payload, signature_bytes) = split_blob(blob);

    assert!(verify_credential_sig(PUB_KEY, &payload, &signature_bytes));

    let signature = ECDSASig::from_base64(&signature_bytes).expect("Base64 encoded signature.");

    (
        payload.try_into().expect("Payload of length PAYLOAD_LEN"),
        signature,
    )
}

// --- Benchmark ---

struct MsmStats {
    wall_ms: f64,
    msm_total_ms: f64,
    msm_calls: usize,
}

fn bench_prove(c: &mut Criterion) {
    let relation = FullCredential;
    let srs = srs_for_test(&relation, Some(17));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let credential_blob = read_credential::<4096>(CRED_PATH).expect("Path to credential file.");
    let instance = PublicKey::from_base64(PUB_KEY).expect("Base64 encoded PK");
    let (payload, signature) = witness_from_blob(credential_blob.as_slice());
    let holder_sk = K256Scalar::from_bytes_be(&HOLDER_SK_BYTES).expect("Valid scalar");
    let witness = (payload, signature, holder_sk);

    let stats: RefCell<Vec<MsmStats>> = RefCell::new(Vec::new());

    let mut group = c.benchmark_group("prove");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(10));

    group.bench_function("cred_full_k17", |b| {
        b.iter_custom(|iters| {
            msm_timing_reset();
            let start = std::time::Instant::now();
            for _ in 0..iters {
                midnight_zk_stdlib::prove::<FullCredential, blake2b_simd::State>(
                    &srs, &pk, &relation, &instance, witness.clone(), OsRng,
                )
                .expect("proof generation failed");
            }
            let elapsed = start.elapsed();

            let entries = msm_timing_snapshot();
            if !entries.is_empty() {
                let total_msm = msm_timing_wall_clock(&entries);
                stats.borrow_mut().push(MsmStats {
                    wall_ms: elapsed.as_secs_f64() * 1000.0 / iters as f64,
                    msm_total_ms: total_msm.as_secs_f64() * 1000.0 / iters as f64,
                    msm_calls: entries.len() / iters as usize,
                });
            }

            elapsed
        });
    });

    group.finish();

    let stats = stats.borrow();
    if !stats.is_empty() {
        let avg_wall = stats.iter().map(|s| s.wall_ms).sum::<f64>() / stats.len() as f64;
        let avg_msm = stats.iter().map(|s| s.msm_total_ms).sum::<f64>() / stats.len() as f64;
        let msm_calls = stats.last().unwrap().msm_calls;
        eprintln!();
        eprintln!("--- MSM Timing (avg over {} samples) ---", stats.len());
        eprintln!("  Wall:      {avg_wall:.1} ms");
        eprintln!(
            "  MSM total: {avg_msm:.1} ms ({:.1}%)",
            avg_msm / avg_wall * 100.0
        );
        eprintln!("  MSM calls: {msm_calls}");
        eprintln!(
            "  MSM avg:   {:.2} ms/call",
            avg_msm / msm_calls as f64
        );
    }
}

criterion_group!(benches, bench_prove);
criterion_main!(benches);

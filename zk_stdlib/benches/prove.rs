//! Criterion benchmark for bitcoin_sig proving with optional MSM timing.
//!
//! Run with MSM timing enabled:
//! ```sh
//! MSM_TIMING=1 cargo bench -p midnight-zk-stdlib --bench prove
//! ```

#[macro_use]
extern crate criterion;

use std::cell::RefCell;
use std::time::Duration;

use criterion::Criterion;
use group::GroupEncoding;
use midnight_circuits::{
    field::foreign::params::MultiEmulationParams,
    instructions::{
        AssertionInstructions, AssignmentInstructions, DecompositionInstructions, EccInstructions,
        PublicInputInstructions, ZeroInstructions,
    },
    types::{AssignedByte, AssignedForeignPoint, Instantiable},
    CircuitField,
};
use midnight_curves::k256::{Fp as K256Base, Fq as K256Scalar, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::msm::{msm_timing_reset, msm_timing_snapshot, msm_timing_wall_clock},
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;
use sha2::Digest;

type F = midnight_curves::Fq;
type Message = [u8; 32];
type PK = K256;
type Signature = (K256Base, K256Scalar);

// SHA256("BIP0340/challenge") tag used in Bitcoin Schnorr signatures.
const TAG_PREIMAGE: [u8; 17] = [
    0x42, 0x49, 0x50, 0x30, 0x33, 0x34, 0x30, 0x2f, 0x63, 0x68, 0x61, 0x6c, 0x6c, 0x65, 0x6e,
    0x67, 0x65,
];

#[derive(Clone, Default)]
struct BitcoinSigExample;

impl Relation for BitcoinSigExample {
    type Instance = (PK, Message);
    type Witness = Signature;

    fn format_instance((pk, msg_bytes): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            AssignedForeignPoint::<F, K256, MultiEmulationParams>::as_public_input(pk),
            msg_bytes
                .iter()
                .flat_map(AssignedByte::<F>::as_public_input)
                .collect::<Vec<_>>(),
        ]
        .into_iter()
        .flatten()
        .collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let secp256k1_scalar = std_lib.secp256k1_scalar();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        // Assign the PK as public input.
        let pk = secp256k1_curve.assign_as_public_input(layouter, instance.map(|(pk, _)| pk))?;

        // Assign the message bytes and constrain as public input.
        let msg_bytes = std_lib.assign_many(
            layouter,
            &instance.map(|(_, msg_bytes)| msg_bytes).transpose_array(),
        )?;
        msg_bytes
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))?;

        // Assign the signature as a witness.
        let (rx_val, s_val) = witness.unzip();
        let rx = secp256k1_base.assign(layouter, rx_val)?;
        let s = secp256k1_scalar.assign(layouter, s_val)?;

        // Assign the (fixed) SHA tag.
        let tag_value: [u8; 32] = sha2::Sha256::digest(TAG_PREIMAGE).into();
        let tag = std_lib.assign_many_fixed(layouter, &tag_value)?;

        let rx_bytes = secp256k1_base.assigned_to_be_bytes(layouter, &rx, None)?;
        let pk_x = secp256k1_curve.x_coordinate(&pk);
        let pk_x_bytes = secp256k1_base.assigned_to_be_bytes(layouter, &pk_x, None)?;

        // Prepare the SHA input: (tag || tag || rx || pk_x || msg).
        let sha_input = (tag.clone().into_iter())
            .chain(tag)
            .chain(rx_bytes.clone())
            .chain(pk_x_bytes)
            .chain(msg_bytes)
            .collect::<Vec<_>>();

        let mut sha_output = std_lib.sha2_256(layouter, &sha_input)?;

        // Bitcoin represents scalars in big-endian.
        sha_output.reverse();

        let sha_output_bits = sha_output
            .into_iter()
            .map(|byte| std_lib.assigned_to_le_bits(layouter, &byte.into(), Some(8), true))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let gen = secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let s_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &s, None, true)?;
        let neg_pk = secp256k1_curve.negate(layouter, &pk)?;

        let r_point =
            secp256k1_curve.msm_by_le_bits(layouter, &[s_bits, sha_output_bits], &[gen, neg_pk])?;

        // Check the correctness of R.
        secp256k1_curve.assert_non_zero(layouter, &r_point)?;

        let y = secp256k1_curve.y_coordinate(&r_point);
        let y_sign = secp256k1_base.sgn0(layouter, &y)?;
        std_lib.assert_false(layouter, &y_sign)?;

        let r_point_x = secp256k1_curve.x_coordinate(&r_point);
        secp256k1_base.assert_equal(layouter, &r_point_x, &rx)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            secp256k1: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(BitcoinSigExample)
    }
}

fn parse_bitcoin_point(x_coord: &[u8; 32]) -> K256 {
    let mut sec1_compressed = [0u8; 33];
    sec1_compressed[0] = 0x02;
    sec1_compressed[1..].copy_from_slice(x_coord);
    K256::from_bytes(&sec1_compressed.into()).expect("Point parsing failed")
}

struct MsmStats {
    wall_ms: f64,
    msm_total_ms: f64,
    msm_calls: usize,
}

fn bench_prove(c: &mut Criterion) {
    let relation = BitcoinSigExample;
    let srs = srs_for_test(&relation, Some(15));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let msg_bytes: [u8; 32] = [
        27, 214, 156, 7, 93, 215, 183, 140, 79, 32, 166, 152, 178, 42, 63, 185, 215, 70, 21, 37,
        195, 152, 39, 214, 170, 247, 161, 98, 139, 224, 162, 131,
    ];
    let pk_bytes: [u8; 32] = [
        179, 21, 213, 119, 148, 98, 81, 244, 98, 197, 69, 237, 108, 48, 37, 32, 206, 5, 247,
        157, 67, 110, 22, 104, 179, 49, 214, 89, 58, 147, 58, 98,
    ];
    let sig_bytes: [u8; 64] = [
        130, 202, 167, 37, 68, 100, 97, 250, 64, 31, 112, 100, 84, 155, 189, 94, 44, 183, 164,
        69, 191, 116, 182, 25, 49, 201, 43, 66, 204, 112, 124, 32, 49, 8, 60, 245, 140, 215, 44,
        157, 221, 20, 191, 69, 227, 251, 112, 89, 42, 136, 159, 147, 148, 126, 60, 47, 139, 187,
        129, 58, 59, 239, 164, 80,
    ];

    let instance = (parse_bitcoin_point(&pk_bytes), msg_bytes);
    let witness = (
        K256Base::from_bytes_be(&sig_bytes[..32]).expect("Secp base"),
        K256Scalar::from_bytes_be(&sig_bytes[32..]).expect("Secp scalar"),
    );

    let stats: RefCell<Vec<MsmStats>> = RefCell::new(Vec::new());

    let mut group = c.benchmark_group("prove");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(10));

    group.bench_function("bitcoin_sig", |b| {
        b.iter_custom(|iters| {
            msm_timing_reset();
            let start = std::time::Instant::now();
            for _ in 0..iters {
                midnight_zk_stdlib::prove::<BitcoinSigExample, blake2b_simd::State>(
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

    // Print MSM timing summary when MSM_TIMING=1 is set.
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

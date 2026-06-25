//! Criterion-driven sweep of prove/verify time and proof size over
//! `T_MAX_LOG` for the SHA-256 preimage circuit at K=13. Each benchmark
//! samples the full prove or verify pipeline (Criterion handles warmup,
//! statistical noise reduction, and 95 % CIs).
//!
//! Run:
//! ```
//! cargo bench -p midnight-zk-stdlib --bench fflonk_sha_preimage
//! ```
//!
//! For per-phase substep timings, see the standalone `Instant`-driven
//! example added alongside this file (intentionally outside Criterion —
//! marker timings are too short for Criterion's statistical machinery).

#![allow(clippy::all)]

#[path = "../examples/exposing_types.rs"]
mod exposing_types;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use exposing_types::sha_preimage::ShaPreImageCircuit;
use group::prime::PrimeCurveAffine;
use midnight_curves::{Bls12, Fq as Scalar, G1Affine};
use midnight_proofs::{
    circuit::Value,
    plonk::{create_proof, keygen_pk, keygen_vk_with_k, prepare, ProvingKey, VerifyingKey},
    poly::{
        commitment::{Guard, Params, PolynomialCommitmentScheme},
        fflonk::{FflonkBundle, FflonkCommitment, FflonkScheme, FflonkVerificationGuard},
        kzg::params::ParamsKZG,
        PolynomialLabel,
    },
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{MidnightCircuit, Relation};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

const K: u32 = 13;

/// Build an SRS large enough for `FflonkScheme<Bls12, T_MAX_LOG>` at K=13.
/// Uses `unsafe_setup` (random SRS) — sufficient for timing comparison.
fn build_srs<const T_MAX_LOG: u32>(cs_degree: usize) -> ParamsKZG<Bls12> {
    let blowup = <FflonkScheme<Bls12, T_MAX_LOG> as PolynomialCommitmentScheme<Scalar>>::srs_monomial_blowup(
        cs_degree,
    );
    if blowup <= 1 {
        return ParamsKZG::unsafe_setup(K, OsRng);
    }
    let extended_k = K + (blowup as f64).log2().ceil() as u32;
    let mut srs: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(extended_k, OsRng);
    srs.downsize_lagrange(K);
    srs
}

/// One sweep setup — builds SRS, VK, PK once. The witness/instance is
/// regenerated per Criterion iteration in the `prove` bench (deterministic
/// per (T, iter)) so we can run a fresh transcript each time.
struct Setup<const T_MAX_LOG: u32> {
    srs: ParamsKZG<Bls12>,
    vk: VerifyingKey<Scalar, FflonkScheme<Bls12, T_MAX_LOG>>,
    pk: ProvingKey<Scalar, FflonkScheme<Bls12, T_MAX_LOG>>,
}

fn setup<const T_MAX_LOG: u32>() -> Setup<T_MAX_LOG> {
    let relation = ShaPreImageCircuit;
    let cs_degree = midnight_zk_stdlib::cs_degree(relation.used_chips());
    let srs = build_srs::<T_MAX_LOG>(cs_degree);
    let circuit = MidnightCircuit::from_relation(&relation, Some(K));
    let vk: VerifyingKey<Scalar, FflonkScheme<Bls12, T_MAX_LOG>> =
        keygen_vk_with_k(&srs, &circuit, K).expect("keygen_vk");
    let pk: ProvingKey<Scalar, FflonkScheme<Bls12, T_MAX_LOG>> =
        keygen_pk(vk.clone(), &circuit).expect("keygen_pk");
    Setup { srs, vk, pk }
}

/// Build one fresh witness + matching instance + proof. Used both as a
/// per-iteration prover input and as a one-shot to seed the verifier
/// benchmark.
fn prove<const T_MAX_LOG: u32>(setup: &Setup<T_MAX_LOG>, seed: u64) -> ([u8; 32], Vec<u8>) {
    let relation = ShaPreImageCircuit;
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
    let instance: [u8; 32] = sha2::Sha256::digest(witness).into();
    let pi_flat = <ShaPreImageCircuit as Relation>::format_instance(&instance).unwrap();
    let com_inst = <ShaPreImageCircuit as Relation>::format_committed_instances(&witness);
    let circuit = MidnightCircuit::new(
        &relation,
        Value::known(instance),
        Value::known(witness),
        Some(K),
    );
    let mut transcript: CircuitTranscript<blake2b_simd::State> = CircuitTranscript::init();
    create_proof::<Scalar, FflonkScheme<Bls12, T_MAX_LOG>, _, _>(
        &setup.srs,
        &setup.pk,
        &circuit,
        1,
        &[com_inst.as_slice(), &pi_flat],
        &mut transcript,
        OsRng,
    )
    .expect("create_proof");
    (instance, transcript.finalize())
}

/// Verifier inner loop — split out so Criterion can time just it.
fn verify<const T_MAX_LOG: u32>(
    setup: &Setup<T_MAX_LOG>,
    instance: &[u8; 32],
    proof: &[u8],
) {
    let pi_flat = <ShaPreImageCircuit as Relation>::format_instance(instance).unwrap();
    let mut transcript: CircuitTranscript<blake2b_simd::State> =
        CircuitTranscript::init_from_bytes(proof);
    let committed_pi: G1Affine = G1Affine::identity();
    let committed_pi_com: FflonkCommitment<Bls12, T_MAX_LOG> =
        FflonkCommitment(vec![FflonkBundle::Bundle(
            committed_pi.into(),
            vec![PolynomialLabel::CommittedInstance(0)],
        )]);
    let guard: FflonkVerificationGuard<Bls12, T_MAX_LOG> = prepare::<
        Scalar,
        FflonkScheme<Bls12, T_MAX_LOG>,
        _,
    >(
        &setup.vk,
        &[committed_pi_com],
        &[&pi_flat],
        &mut transcript,
    )
    .expect("prepare");
    let verifier_params = setup.srs.verifier_params();
    assert!(
        <FflonkVerificationGuard<Bls12, T_MAX_LOG> as Guard<
            Scalar,
            FflonkScheme<Bls12, T_MAX_LOG>,
        >>::verify(guard, &verifier_params)
        .is_ok(),
    );
}

macro_rules! bench_t {
    ($c:ident, $t:expr) => {{
        const T: u32 = $t;
        let setup = setup::<T>();
        let proof_size = {
            let (_instance, p) = prove::<T>(&setup, 0xdead_0000 | T as u64);
            p.len()
        };
        eprintln!(
            "[T_MAX_LOG={}] SRS|g|=2^{}, proof = {} B",
            T,
            (setup.srs.g_monomial_size() as f64).log2().round() as u32,
            proof_size,
        );

        let mut g = $c.benchmark_group(format!("fflonk_sha_preimage_T{}", T));
        // SHA-256 K=13 is slow; small sample sizes still give stable means.
        g.sample_size(10);
        g.measurement_time(Duration::from_secs(45));
        g.warm_up_time(Duration::from_secs(5));

        g.bench_with_input(BenchmarkId::new("prove", T), &(), |b, _| {
            let mut counter: u64 = 0;
            b.iter_with_large_drop(|| {
                counter = counter.wrapping_add(1);
                prove::<T>(&setup, 0xc0fe_0000 | counter)
            });
        });

        // One representative proof seeded outside the bench loop so the
        // verifier runs on a stable input.
        let (instance, proof) = prove::<T>(&setup, 0xbeef_0000 | T as u64);
        g.bench_with_input(BenchmarkId::new("verify", T), &(), |b, _| {
            b.iter(|| verify::<T>(&setup, &instance, &proof));
        });

        g.finish();
    }};
}

fn bench(c: &mut Criterion) {
    bench_t!(c, 0);
    bench_t!(c, 1);
    bench_t!(c, 2);
    bench_t!(c, 3);
    bench_t!(c, 4);
    bench_t!(c, 5);
}

criterion_group!(benches, bench);
criterion_main!(benches);

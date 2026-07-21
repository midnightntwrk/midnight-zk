//! Compares the two ways of verifying a batch of proofs, swept over the number
//! of CPU cores made available to rayon (1..=all logical cores). Three costs
//! are measured on a fixed batch of `NB_PROOFS` proofs:
//!
//! - `u` — `batch_verify(.., identify_failures = false)` on an **all-valid**
//!   batch: the accept path. One parallel `prepare` per proof, folded into a
//!   single pairing check. This is what consensus verification pays.
//! - `v` — **individual** verification (in parallel) localizing the failures:
//!   one `verify` per proof, error-count independent. This is the naive
//!   alternative strategy.
//! - `w` — `batch_verify(.., identify_failures = true)` on a batch with **one
//!   invalid** proof: the batch recovery path. Pays `u`, then, since the batch
//!   check failed, reuses the already-prepared guards for a parallel singleton
//!   search to pinpoint the culprit. This is *not* `u + v`: the search reuses
//!   the `prepare` work, so on a single failure `w` is typically well below `u
//!   + v` (and can even beat `v`).
//!
//! `u`, `v`, `w` all solve the same problem when the batch is bad ("which
//! proofs failed?"), except `u` is the 0-failure baseline. The interesting
//! quantities are the gap `u <-> v` (what batching saves on the happy path) and
//! `v <-> w` (how the batch recovery path compares to plain individual
//! verification).
//!
//! The number of cores dominates: verifying 1000 independent proofs is
//! embarrassingly parallel, so each measurement is run inside a rayon pool
//! pinned to exactly `c` threads (`ThreadPoolBuilder::num_threads(c)` +
//! `pool.install`); every internal `par_iter` then picks up that pool.
//!
//! Rust reports the core count via `std::thread::available_parallelism()`.
//!
//! Run from the crate directory `zk_stdlib` (the SRS loads via the relative
//! path `./examples/assets`). CSV goes to stdout (import into Numbers to plot
//! the three curves against the core count), the human-readable table to
//! stderr:
//!
//! ```text
//! cargo bench --bench batch_verify_cores > cores.csv
//! ```
//!
//! Tunable via env vars (all optional): `NB_PROOFS`, `SAMPLES`, `MAX_CORES`.

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

use ff::Field;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::params::ParamsVerifierKZG,
};
use midnight_zk_stdlib::{
    utils::plonk_api::srs_for_test, MidnightVK, Relation, ZkStdLib, ZkStdLibArch,
};
use rand::rngs::OsRng;
use rayon::{
    iter::{IntoParallelIterator, ParallelIterator},
    ThreadPoolBuilder,
};

type F = midnight_curves::Fq;
type H = blake2b_simd::State;

// Defaults; each can be overridden by an env var of the same name.
const NB_PROOFS: usize = 1000;
const SAMPLES: usize = 20;
const WARMUP: Duration = Duration::from_millis(1500);

// --- Relation under test (swap this block to sweep another circuit) ----------

#[derive(Clone, Default)]
struct PoseidonBench;

impl Relation for PoseidonBench {
    type Instance = F;
    type Witness = [F; 3];
    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonBench)
    }
}

fn random_instance() -> (F, [F; 3]) {
    let witness: [F; 3] = core::array::from_fn(|_| F::random(OsRng));
    let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);
    (instance, witness)
}

/// `individual` strategy: verify each proof on its own (in parallel), returning
/// the ascending failing indices. Uses the ambient rayon pool, so its core
/// count matches `batch_verify` (whose per-proof `prepare` also runs under
/// rayon).
fn locate_individual(
    params: &ParamsVerifierKZG<midnight_curves::Bls12>,
    vks: &[MidnightVK],
    instances: &[F],
    proofs: &[Vec<u8>],
) -> Vec<usize> {
    let mut failures: Vec<usize> = (0..proofs.len())
        .into_par_iter()
        .filter(|&i| {
            midnight_zk_stdlib::verify::<PoseidonBench, H>(
                params,
                &vks[i],
                &instances[i],
                None,
                &proofs[i],
            )
            .is_err()
        })
        .collect();
    failures.sort_unstable();
    failures
}

// --- Measurement (criterion-style noise control, minus the criterion crate) --

struct Stats {
    /// Median wall time in ms — the headline, robust central tendency.
    median: f64,
    /// Standard deviation in ms — a proxy for the measurement noise.
    std: f64,
}

impl Stats {
    /// Compact `median±sd` cell for the human-readable table.
    fn cell(&self) -> String {
        format!("{:.2}±{:.2}", self.median, self.std)
    }
}

/// Warms up for `WARMUP` (at least one run, discarded), then times `SAMPLES`
/// runs and reports median / min / std. `f`'s output must be consumed with
/// `black_box` by the caller so the work is not optimized away.
fn measure(samples: usize, mut f: impl FnMut()) -> Stats {
    let start = Instant::now();
    loop {
        f();
        if start.elapsed() >= WARMUP {
            break;
        }
    }

    let mut ms: Vec<f64> = Vec::with_capacity(samples);
    for _ in 0..samples {
        let t = Instant::now();
        f();
        ms.push(t.elapsed().as_secs_f64() * 1e3);
    }
    ms.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let n = ms.len();
    let median = if n.is_multiple_of(2) {
        (ms[n / 2 - 1] + ms[n / 2]) / 2.0
    } else {
        ms[n / 2]
    };
    let mean = ms.iter().sum::<f64>() / n as f64;
    let std = (ms.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / n as f64).sqrt();

    Stats { median, std }
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// Joins one CSV row. With `eu` set, uses European conventions so Numbers on a
/// comma-decimal locale imports the numbers as numbers, not text: `;` as the
/// field separator and `,` as the decimal mark. Otherwise the plain `,`-and-`.`
/// form. Fields must contain no separator characters of their own.
fn csv_row(fields: &[String], eu: bool) -> String {
    if eu {
        fields.iter().map(|f| f.replace('.', ",")).collect::<Vec<_>>().join(";")
    } else {
        fields.join(",")
    }
}

fn main() {
    let nb_proofs = env_usize("NB_PROOFS", NB_PROOFS);
    let samples = env_usize("SAMPLES", SAMPLES);
    let max_cores = env_usize(
        "MAX_CORES",
        std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1),
    );
    // European CSV (`;` separator, `,` decimals) for direct import into Numbers
    // on a comma-decimal locale: `EU_CSV=1`.
    let eu = std::env::var("EU_CSV").map(|v| !v.is_empty() && v != "0").unwrap_or(false);

    let relation = PoseidonBench;
    let srs = srs_for_test(&relation, Some(6));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let params = srs.verifier_params();

    eprintln!("generating {nb_proofs} proofs (one-time setup, all cores)...");
    let generated: Vec<(F, Vec<u8>)> = (0..nb_proofs)
        .into_par_iter()
        .map(|_| {
            let (instance, witness) = random_instance();
            let proof = midnight_zk_stdlib::prove::<PoseidonBench, H>(
                &srs, &pk, &relation, &instance, witness, OsRng,
            )
            .expect("proof generation failed");
            (instance, proof)
        })
        .collect();

    let instances: Vec<F> = generated.iter().map(|(i, _)| *i).collect();
    let proofs: Vec<Vec<u8>> = generated.iter().map(|(_, p)| p.clone()).collect();
    let vks: Vec<MidnightVK> = (0..nb_proofs).map(|_| vk.clone()).collect();

    let clean_pis: Vec<Vec<F>> =
        instances.iter().map(|i| PoseidonBench::format_instance(i).unwrap()).collect();

    // Inject exactly one invalid proof by pairing a valid proof with a wrong
    // (but same-length) public input: `prepare` still succeeds, only the opening
    // check fails. Corrupt the instance and its formatted PI consistently, so
    // the individual and batch strategies see the same single failure.
    let bad_idx = nb_proofs / 2;
    let mut bad_instances = instances.clone();
    bad_instances[bad_idx] += F::ONE;
    let mut bad_pis = clean_pis.clone();
    bad_pis[bad_idx] = PoseidonBench::format_instance(&bad_instances[bad_idx]).unwrap();

    eprintln!(
        "batch of {nb_proofs} proofs, 1 invalid at index {bad_idx}; \
         sweeping cores 1..={max_cores}, {samples} samples/measurement\n"
    );

    let header = [
        "cores",
        "u_batch_ms",
        "v_individual_ms",
        "w_recovery_ms",
        "batch_speedup_pct",
        "recovery_vs_individual_pct",
    ]
    .map(String::from);
    println!("{}", csv_row(&header, eu));
    eprintln!(
        "{:>5}  {:>16}  {:>16}  {:>16}  {:>9}  {:>9}",
        "cores", "u batch (ms)", "v indiv (ms)", "w recover (ms)", "u<->v", "v<->w"
    );

    for c in 1..=max_cores {
        let pool = ThreadPoolBuilder::new().num_threads(c).build().unwrap();

        let (u, v, w) = pool.install(|| {
            // Correctness: all three strategies must agree before we time them.
            assert!(
                midnight_zk_stdlib::batch_verify::<H>(&params, &vks, &clean_pis, &proofs, false)
                    .is_ok(),
                "clean batch must accept"
            );
            assert_eq!(
                locate_individual(&params, &vks, &bad_instances, &proofs),
                vec![bad_idx],
                "individual must localize the single failure"
            );
            match midnight_zk_stdlib::batch_verify::<H>(&params, &vks, &bad_pis, &proofs, true) {
                Err(Error::BatchOpening(f)) => {
                    assert_eq!(f, vec![bad_idx], "batch recovery must localize the failure")
                }
                other => panic!("expected BatchOpening, got {other:?}"),
            }

            let u = measure(samples, || {
                black_box(
                    midnight_zk_stdlib::batch_verify::<H>(
                        &params, &vks, &clean_pis, &proofs, false,
                    )
                    .is_ok(),
                );
            });
            let v = measure(samples, || {
                black_box(locate_individual(&params, &vks, &bad_instances, &proofs));
            });
            let w = measure(samples, || {
                black_box(
                    midnight_zk_stdlib::batch_verify::<H>(&params, &vks, &bad_pis, &proofs, true)
                        .is_err(),
                );
            });
            (u, v, w)
        });

        // Positive => batch accept is that % faster than individual.
        let batch_speedup = (v.median - u.median) / v.median * 100.0;
        // Positive => batch recovery is that % slower than individual;
        // negative => recovery is actually faster (it reuses the `prepare`).
        let recovery_gap = (w.median - v.median) / v.median * 100.0;

        let row = [
            format!("{c}"),
            format!("{:.3}", u.median),
            format!("{:.3}", v.median),
            format!("{:.3}", w.median),
            format!("{:.2}", batch_speedup),
            format!("{:.2}", recovery_gap),
        ];
        println!("{}", csv_row(&row, eu));
        eprintln!(
            "{c:>5}  {:>16}  {:>16}  {:>16}  {:>+8.1}%  {:>+8.1}%",
            u.cell(),
            v.cell(),
            w.cell(),
            batch_speedup,
            recovery_gap
        );
    }
}

//! Sweeps the number of invalid proofs in a batch and times the three
//! failure-recovery strategies, emitting a CSV so the curves can be plotted.
//!
//! Strategies (all return the same failing-index set):
//! - `individual`: verify each proof on its own with `verify`, in parallel with
//!   rayon so the baseline gets the same core count as the batch path (whose
//!   `prepare` step is also parallelised). Error-count independent, so measured
//!   once and repeated across every CSV row.
//! - `reuse-prepare` (`BatchStrategy::ReusePrepare`): prepare once, localize by
//!   binary search that re-evaluates each subset's combined MSM.
//! - `reuse-prepare+msm` (`BatchStrategy::ReusePrepareMsm`): also collapse each
//!   proof's MSM to a point up front, so search nodes only recombine points.
//!
//! Invalid proofs are injected by pairing a valid proof with a wrong (but
//! same-length) public input: `prepare` succeeds, only the opening check fails.
//!
//! Run from the crate directory `zk_stdlib` (the SRS loads via the relative
//! path `./examples/assets`); CSV goes to stdout, progress to stderr:
//!
//! ```text
//! cargo bench --bench batch_recovery_sweep > sweep.csv
//! ```
//!
//! The sweep is dense where the curve bends and coarse where it is flat.

use std::{hint::black_box, time::Instant};

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
    utils::plonk_api::srs_for_test, BatchStrategy, MidnightVK, Relation, ZkStdLib, ZkStdLibArch,
};
use rand::{rngs::OsRng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

type F = midnight_curves::Fq;
type H = blake2b_simd::State;

const NB_PROOFS: usize = 1000;
const REPS: usize = 3;
const SEED: u64 = 0xB47C;

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

/// `individual`: verify each proof on its own (in parallel), returning the
/// failing indices. Parallelised to match the batch path, whose per-proof
/// `prepare` also runs under rayon — otherwise the baseline would be handicapped
/// by running serially against a multi-threaded competitor.
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

/// `reuse-prepare*`: guard-sharing binary search under the given strategy.
fn locate_batch(
    params: &ParamsVerifierKZG<midnight_curves::Bls12>,
    vks: &[MidnightVK],
    pis: &[Vec<F>],
    proofs: &[Vec<u8>],
    strategy: BatchStrategy,
) -> Vec<usize> {
    match midnight_zk_stdlib::batch_verify_with_strategy::<H>(params, vks, pis, proofs, strategy) {
        Ok(()) => Vec::new(),
        Err(Error::BatchOpening(f)) => f,
        Err(e) => panic!("unexpected error: {e:?}"),
    }
}

/// Corrupts `k` distinct (seeded) public inputs; returns the poisoned `pis` and
/// the sorted corrupted indices.
fn poison(base_pis: &[Vec<F>], k: usize, seed: u64) -> (Vec<Vec<F>>, Vec<usize>) {
    let mut pis = base_pis.to_vec();
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut set = std::collections::BTreeSet::new();
    while set.len() < k {
        set.insert(rng.next_u32() as usize % pis.len());
    }
    let bad: Vec<usize> = set.into_iter().collect();
    for &i in &bad {
        pis[i] = vec![pis[i][0] + F::ONE];
    }
    (pis, bad)
}

/// Runs `f` `REPS` times, returning the minimum wall time (ms) and the last
/// result (the minimum is the least noise-perturbed estimate).
fn bench_min<T>(mut f: impl FnMut() -> T) -> (f64, T) {
    let mut best = f64::INFINITY;
    let mut last = None;
    for _ in 0..REPS {
        let t = Instant::now();
        let r = f();
        let ms = t.elapsed().as_secs_f64() * 1e3;
        best = best.min(ms);
        last = Some(r);
    }
    (best, last.unwrap())
}

/// Sweep points: every integer 0..=10, then every 10 to 100, then every 50 to
/// `NB_PROOFS`.
fn sweep_points() -> Vec<usize> {
    let mut ks: Vec<usize> = (0..=10).collect();
    ks.extend((20..100).step_by(10));
    ks.extend((100..=NB_PROOFS).step_by(50));
    ks
}

fn main() {
    let relation = PoseidonBench;
    let srs = srs_for_test(&relation, Some(6));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let params = srs.verifier_params();

    eprintln!("generating {NB_PROOFS} proofs (one-time setup)...");
    let mut instances = Vec::with_capacity(NB_PROOFS);
    let mut proofs = Vec::with_capacity(NB_PROOFS);
    for _ in 0..NB_PROOFS {
        let (instance, witness) = random_instance();
        let proof = midnight_zk_stdlib::prove::<PoseidonBench, H>(
            &srs, &pk, &relation, &instance, witness, OsRng,
        )
        .expect("proof generation failed");
        instances.push(instance);
        proofs.push(proof);
    }

    let vks: Vec<_> = (0..NB_PROOFS).map(|_| vk.clone()).collect();
    let clean_pis: Vec<Vec<F>> =
        instances.iter().map(|i| PoseidonBench::format_instance(i).unwrap()).collect();

    // `individual` is independent of the number of failures: measure it once.
    let (individual_ms, _) = bench_min(|| locate_individual(&params, &vks, &instances, &proofs));
    eprintln!("individual (constant reference): {individual_ms:.1} ms");

    println!("k,individual_ms,reuse_prepare_ms,reuse_prepare_msm_ms");
    for k in sweep_points() {
        let (pis, bad) = poison(&clean_pis, k, SEED.wrapping_add(k as u64));

        let (prep_ms, prep_res) =
            bench_min(|| locate_batch(&params, &vks, &pis, &proofs, BatchStrategy::ReusePrepare));
        let (msm_ms, msm_res) = bench_min(|| {
            locate_batch(&params, &vks, &pis, &proofs, BatchStrategy::ReusePrepareMsm)
        });

        // Sanity: both strategies recovered exactly the injected failure set.
        assert_eq!(prep_res, bad, "reuse-prepare disagrees at k={k}");
        assert_eq!(msm_res, bad, "reuse-prepare+msm disagrees at k={k}");
        black_box(&prep_res);
        black_box(&msm_res);

        println!("{k},{individual_ms:.3},{prep_ms:.3},{msm_ms:.3}");
        eprintln!("k={k:>4}: prepare={prep_ms:7.1} ms   prepare+msm={msm_ms:7.1} ms");
    }
}

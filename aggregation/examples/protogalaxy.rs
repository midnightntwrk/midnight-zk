//! One-shot Protogalaxy folding of `k` instances vs `k` standard proofs.
//!
//! Port of accordion's `protogalaxy` example onto the scalar-e
//! running-accumulator API (`midnight_proofs::plonk::protogalaxy`). Accordion
//! folded the `k` instances with one k-ary fold (vector E) and proved the
//! folded trace; here the `k` instances are committed (partial proofs),
//! the first one initialises the accumulator, the other `k − 1` are folded
//! 2-to-1 one after the other, and one decider proof closes the accumulator.
//! The verifier reads the `k` instances, replays `init` and the `k − 1` folds
//! natively and checks the decider proof.
//!
//! DO NOT add this example to the CI as it is slow.
//!
//! ```text
//! cargo run --release --features truncated-challenges --example protogalaxy             # widths 2..64
//! cargo run --release --features truncated-challenges --example protogalaxy -- 4        # one width
//! PG_REPS=3 cargo run --release --features truncated-challenges --example protogalaxy -- 4
//! PG_PLONK=1 cargo run --release --features truncated-challenges --example protogalaxy -- 4  # + k proofs
//! PG_PLONK_ONLY=8 cargo run --release --features truncated-challenges --example protogalaxy  # 8 proofs, no fold
//! PG_PCS=kzg ...   # plain KZG instead of the branch default (fflonk)
//! ```
//!
//! Uses `ParamsKZG::unsafe_setup` (benchmark only, not a trusted setup).

#[path = "circuits/sha_multi.rs"]
mod sha_multi;

use std::{
    env,
    time::{Duration, Instant},
};

use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_curves::Bls12;
use midnight_proofs::{
    circuit::Value,
    plonk::{
        ProvingKey, create_proof, keygen_pk, keygen_vk_with_k, prepare,
        protogalaxy::{
            Accumulator, ProverAccumulator, commit_instance, folding_degree, prove_relaxed_trace,
            read_instance, verify_relaxed_trace,
        },
    },
    poly::{
        commitment::{Guard, PolynomialCommitmentScheme},
        kzg::{KZGCommitmentScheme, params::ParamsKZG},
    },
    transcript::{CircuitTranscript, Hashable, Transcript},
};
use midnight_zk_stdlib::{
    DefaultPCS, MidnightCircuit, MidnightPCS, Relation, cost_model, optimal_k,
};
use rand::rngs::OsRng;
use sha_multi::{N_SHA, ShaMultiCircuit};

type F = midnight_curves::Fq;
type H = PoseidonState<F>;
type T = CircuitTranscript<H>;
type Pair = ([u8; 32], [u8; 24]);

/// Folding widths run when no width is given on the command line.
const DEFAULT_WIDTHS: [usize; 6] = [2, 4, 8, 16, 32, 64];

fn env_usize(key: &str, default: usize) -> usize {
    env::var(key).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// Public inputs of an instance: empty committed-instance column, then the PI.
fn public_inputs(instance: &[u8; 32]) -> Vec<Vec<F>> {
    vec![vec![], ShaMultiCircuit::format_instance(instance).unwrap()]
}

fn slices(pi: &[Vec<F>]) -> Vec<&[F]> {
    pi.iter().map(Vec::as_slice).collect()
}

fn circuit<'a>(
    relation: &'a ShaMultiCircuit,
    k: u32,
    pair: &Pair,
) -> MidnightCircuit<'a, ShaMultiCircuit> {
    MidnightCircuit::new(
        relation,
        Value::known(pair.0),
        Value::known(pair.1),
        Some(k),
    )
}

fn mean(ts: &[Duration]) -> Duration {
    ts.iter().sum::<Duration>() / ts.len().max(1) as u32
}

struct Bench<'a, CS: PolynomialCommitmentScheme<F>> {
    relation: &'a ShaMultiCircuit,
    k: u32,
    params: ParamsKZG<Bls12>,
    pk: ProvingKey<F, CS>,
}

impl<CS> Bench<'_, CS>
where
    CS: MidnightPCS,
    CS::Commitment: Hashable<H>,
{
    /// `k` independent `create_proof`s, then their verification.
    fn plonk(&self, pairs: &[Pair]) {
        let n = pairs.len();
        let pis: Vec<_> = pairs.iter().map(|p| public_inputs(&p.0)).collect();

        let t = Instant::now();
        let proofs: Vec<Vec<u8>> = pairs
            .iter()
            .zip(&pis)
            .map(|(pair, pi)| {
                let mut transcript = T::init();
                let c = circuit(self.relation, self.k, pair);
                create_proof(
                    &self.params,
                    &self.pk,
                    &c,
                    0,
                    &slices(pi),
                    &mut transcript,
                    OsRng,
                )
                .expect("PLONK prove failed");
                transcript.finalize()
            })
            .collect();
        let prove = t.elapsed();
        let size: usize = proofs.iter().map(Vec::len).sum();
        eprintln!(
            "[PLONK {n}× prove]                    {prove:>8.2?}   per proof {:>8.2?}   proof size: {size} B",
            prove / n as u32
        );

        let t = Instant::now();
        let vp = CS::get_verifier_params(&self.params);
        for (pi, proof) in pis.iter().zip(&proofs) {
            let mut transcript = T::init_from_bytes(proof);
            prepare(self.pk.get_vk(), &[], &slices(pi), &mut transcript)
                .expect("PLONK verify failed")
                .verify(&vp)
                .expect("PLONK PCS check failed");
        }
        eprintln!(
            "[PLONK {n}× verify]                   {:>8.2?}",
            t.elapsed()
        );
    }

    /// One-shot folding of `pairs`: commit all, init + `k − 1` folds, decider;
    /// then the verifier side.
    fn fold(&self, pairs: &[Pair]) {
        let pis: Vec<_> = pairs.iter().map(|p| public_inputs(&p.0)).collect();
        let pk = &self.pk;

        // ── Prover: commit phases of every instance (partial proofs).
        let t_all = Instant::now();
        let mut commit_times = vec![];
        let mut partial_proofs = vec![];
        let mut fresh = vec![];
        for (pair, pi) in pairs.iter().zip(&pis) {
            let t = Instant::now();
            let mut transcript = T::init();
            let c = circuit(self.relation, self.k, pair);
            fresh.push(
                commit_instance(&self.params, pk, &c, &slices(pi), &mut transcript, OsRng)
                    .expect("commit_instance failed"),
            );
            partial_proofs.push(transcript.finalize());
            commit_times.push(t.elapsed());
        }
        let commit_total: Duration = commit_times.iter().sum();

        // ── Prover: init with the first instance, fold the others 2-to-1.
        let t = Instant::now();
        let mut fresh = fresh.into_iter();
        let mut acc = ProverAccumulator::init(pk, fresh.next().unwrap(), &mut T::init())
            .expect("init failed");
        let init_time = t.elapsed();
        let mut fold_times = vec![];
        let mut folding_proofs = vec![];
        for instance in fresh {
            let t = Instant::now();
            let mut transcript = T::init();
            acc = acc.fold(pk, instance, None, &mut transcript).expect("fold failed");
            folding_proofs.push(transcript.finalize());
            fold_times.push(t.elapsed());
        }
        let fold_total: Duration = fold_times.iter().sum();

        // ── Prover: decider proof of the final accumulator.
        let t = Instant::now();
        let acc_public = acc.accumulator().clone();
        let mut transcript = T::init();
        prove_relaxed_trace(&self.params, pk, acc, &mut transcript).expect("decider failed");
        let decider_proof = transcript.finalize();
        let decider_time = t.elapsed();
        let total = t_all.elapsed();

        let len = |ps: &[Vec<u8>]| ps.iter().map(Vec::len).sum::<usize>();
        let (partial, folding) = (len(&partial_proofs), len(&folding_proofs));
        eprintln!(
            "[commit ×{}]                         {commit_total:>8.2?}   per instance {:>8.2?}",
            pairs.len(),
            mean(&commit_times)
        );
        eprintln!("[init]                               {init_time:>8.2?}");
        eprintln!(
            "[fold ×{}]                           {fold_total:>8.2?}   per fold {:>8.2?}   {fold_times:.2?}",
            fold_times.len(),
            mean(&fold_times)
        );
        eprintln!("[decider prove]                      {decider_time:>8.2?}");
        eprintln!(
            "[protogalaxy] ONE-SHOT TOTAL          {total:>8.2?}   proof size: {} B \
             (partial {partial} + folding {folding} + decider {})",
            partial + folding + decider_proof.len(),
            decider_proof.len()
        );

        // ── Verifier: read the instances, init + folds, decider.
        let vk = pk.get_vk();
        let t = Instant::now();
        let mut instances = pis.iter().zip(&partial_proofs).map(|(pi, proof)| {
            read_instance(vk, &slices(pi), &mut T::init_from_bytes(proof)).expect("read failed")
        });
        let mut acc_v = Accumulator::init(vk, instances.next().unwrap(), &mut T::init()).unwrap();
        for (instance, proof) in instances.zip(&folding_proofs) {
            acc_v = acc_v
                .fold(vk, &instance, None, &mut T::init_from_bytes(proof))
                .expect("verifier fold failed");
        }
        let fold_verify = t.elapsed();
        assert!(
            acc_v == acc_public,
            "prover and verifier accumulators differ"
        );

        let t = Instant::now();
        let guard = verify_relaxed_trace(vk, &acc_v, &mut T::init_from_bytes(&decider_proof))
            .expect("decider verification failed");
        let decider_verify = t.elapsed();
        let t = Instant::now();
        guard
            .verify(&CS::get_verifier_params(&self.params))
            .expect("decider PCS check failed");
        let pcs_verify = t.elapsed();
        eprintln!(
            "[protogalaxy] verify                 {:>8.2?}   (read + init + folds {fold_verify:.2?}, \
             decider {decider_verify:.2?}, PCS {pcs_verify:.2?})",
            fold_verify + decider_verify + pcs_verify
        );
        eprintln!(
            "Protogalaxy folding succeeded for {} instances.",
            pairs.len()
        );
    }
}

fn run<CS>(relation: &ShaMultiCircuit, k: u32, widths: &[usize], reps: usize)
where
    CS: MidnightPCS,
    CS::Commitment: Hashable<H>,
{
    let t = Instant::now();
    let params = ParamsKZG::<Bls12>::unsafe_setup(CS::srs_k(k), OsRng);
    let c = MidnightCircuit::from_relation(relation, Some(k));
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &c, k).expect("keygen_vk failed");
    let pk = keygen_pk(vk, &c).expect("keygen_pk failed");
    println!(
        "Setup completed in {:.2?} (PCS {}, d_total {})",
        t.elapsed(),
        std::any::type_name::<CS>(),
        folding_degree(pk.get_vk().cs())
    );
    let bench = Bench {
        relation,
        k,
        params,
        pk,
    };

    let plonk_only = env_usize("PG_PLONK_ONLY", 0);
    if plonk_only > 0 {
        eprintln!("\n══════════ standard PLONK: {plonk_only} independent proofs ══════════");
        let pairs: Vec<_> = (0..plonk_only).map(|_| sha_multi::random_instance()).collect();
        return bench.plonk(&pairs);
    }

    for &w in widths {
        eprintln!("\n══════════ NB_FOLDED = {w} ══════════");
        for rep in 0..reps {
            eprintln!("---------- run {} of {reps} ----------", rep + 1);
            let pairs: Vec<_> = (0..w).map(|_| sha_multi::random_instance()).collect();
            if env::var("PG_PLONK").is_ok() {
                bench.plonk(&pairs);
            }
            bench.fold(&pairs);
        }
    }
}

fn main() {
    let relation = ShaMultiCircuit;
    let widths: Vec<usize> = match env::args().nth(1) {
        Some(a) => vec![a.parse().expect("width must be an integer ≥ 1")],
        None => DEFAULT_WIDTHS.to_vec(),
    };
    let reps = env_usize("PG_REPS", 1).max(1);

    let k = optimal_k(&relation);
    let model = cost_model(&relation, Some(k), false);
    println!(
        "Circuit: {N_SHA}× SHA-256 per instance, K={k} ({} rows, {} used), cs degree {}\n\
         advice cols {}, fixed cols {}, lookups {}, trashcans {}, permutations {}",
        1usize << k,
        model.rows,
        model.max_deg,
        model.advice_columns,
        model.fixed_columns,
        model.lookups,
        model.trashcans,
        model.permutations,
    );

    match env::var("PG_PCS").as_deref() {
        Ok("kzg") => run::<KZGCommitmentScheme<Bls12>>(&relation, k, &widths, reps),
        _ => run::<DefaultPCS>(&relation, k, &widths, reps),
    }
}

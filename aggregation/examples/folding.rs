//! Protogalaxy folding of plonk instances, with a final decider proof.
//!
//! Several instances of a circuit (knowledge of a Poseidon preimage, one
//! random preimage per instance) are folded into a running accumulator:
//! - each *fresh instance* is the commit phases of a plonk proof
//!   ([`commit_instance`]); its transcript is its partial proof;
//! - the accumulator starts from the first instance; each *round* folds one or
//!   more fresh instances into it and writes its folding proof to a transcript;
//! - the verifier reads the instances from the partial proofs, replays the
//!   rounds from the folding proofs, and must obtain the prover's accumulators.
//!
//! Finally, the prover proves that the final accumulator satisfies its relaxed
//! relation (the decider proof), which the verifier checks against its own
//! accumulator.
//!
//! The one-shot mode instead folds a batch of fresh instances and proves the
//! result in a single proof, with `prove_one_shot` and `verify_one_shot`.
//!
//! Run with `cd aggregation && cargo run --release --example folding`.

use std::time::Instant;

use ff::Field;
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{AssignmentInstructions, PublicInputInstructions, hash::HashCPU},
};
use midnight_curves::Bls12;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        Error, ProvingKey, keygen_pk, keygen_vk_with_k,
        protogalaxy::{
            Accumulator, FoldingInstance, ProverAccumulator, ProverInstance, commit_instance,
            prove_one_shot, prove_relaxed_trace, read_instance, verify_one_shot,
            verify_relaxed_trace,
        },
    },
    poly::{
        commitment::{Guard, PolynomialCommitmentScheme},
        kzg::params::ParamsKZG,
    },
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{
    DefaultPCS, MidnightCircuit, MidnightPCS, Relation, ZkStdLib, ZkStdLibArch, cost_model,
    optimal_k,
    utils::plonk_api::{SrsSource, load_srs},
};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;
type T = CircuitTranscript<PoseidonState<F>>;

/// Log2 of the smallest Midnight SRS in `examples/assets`, downsized to the
/// circuit.
const SMALLEST_SRS_K: u32 = 17;

/// Fresh instances per step: the first initialises, the others are folding
/// rounds.
const STEPS: [usize; 4] = [1, 3, 1, 1];

/// Knowledge of three field elements whose Poseidon hash is the public input.
#[derive(Clone)]
struct PoseidonPreimage;

impl Relation for PoseidonPreimage {
    type Instance = F;
    type Witness = [F; 3];
    type Error = Error;

    fn format_instance(digest: &F) -> Result<Vec<F>, Error> {
        Ok(vec![*digest])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _digest: Value<F>,
        preimage: Value<[F; 3]>,
    ) -> Result<(), Error> {
        let message = std_lib.assign_many(layouter, &preimage.transpose_array())?;
        let digest = std_lib.poseidon(layouter, &message)?;
        std_lib.constrain_as_public_input(layouter, &digest)
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
        Ok(PoseidonPreimage)
    }
}

/// Number of fresh instances folded in the one-shot mode.
const ONE_SHOT_K: usize = 4;

/// What the verifier gets for a fresh instance.
struct Published {
    public_inputs: Vec<F>,
    partial_proof: Vec<u8>,
}

/// Instance columns: an empty committed-instance column, then the public
/// inputs.
fn columns(public_inputs: &[F]) -> [&[F]; 2] {
    [&[], public_inputs]
}

/// A circuit for a random preimage, with its public inputs.
fn random_instance(k: u32) -> (MidnightCircuit<'static, PoseidonPreimage>, Vec<F>) {
    let preimage: [F; 3] = std::array::from_fn(|_| F::random(OsRng));
    let digest = <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage);
    let public_inputs = PoseidonPreimage::format_instance(&digest).unwrap();
    let circuit = MidnightCircuit::new(
        &PoseidonPreimage,
        Value::known(digest),
        Value::known(preimage),
        Some(k),
    );
    (circuit, public_inputs)
}

/// Commits a fresh instance for a random preimage.
fn commit<'a>(
    params: &ParamsKZG<Bls12>,
    pk: &'a ProvingKey<F, DefaultPCS>,
    k: u32,
) -> (ProverInstance<'a, F, DefaultPCS>, Published) {
    let (circuit, public_inputs) = random_instance(k);
    let mut transcript = T::init();
    let instance = commit_instance(
        params,
        pk,
        &circuit,
        &columns(&public_inputs),
        &mut transcript,
        OsRng,
    )
    .expect("commit_instance failed");
    let partial_proof = transcript.finalize();
    let published = Published {
        public_inputs,
        partial_proof,
    };
    (instance, published)
}

fn main() {
    let k = optimal_k(&PoseidonPreimage);
    let rows = cost_model(&PoseidonPreimage, Some(k), false).rows;
    println!("Poseidon preimage circuit: k = {k}, {rows} rows used");

    let mut srs = load_srs::<DefaultPCS>(SrsSource::Midnight, SMALLEST_SRS_K);
    srs.downsize(DefaultPCS::srs_k(k));
    let circuit = MidnightCircuit::from_relation(&PoseidonPreimage, Some(k));
    let vk = keygen_vk_with_k::<_, DefaultPCS, _>(&srs, &circuit, k).expect("keygen_vk failed");
    let pk = keygen_pk(vk, &circuit).expect("keygen_pk failed");

    // Fresh instances, grouped by step.
    let (mut provers, mut published): (Vec<Vec<_>>, Vec<Vec<_>>) =
        STEPS.iter().map(|&n| (0..n).map(|_| commit(&srs, &pk, k)).unzip()).unzip();

    // Prover: initialise with the first instance, then one fold per round.
    let first = provers.remove(0).remove(0);
    let mut prover = ProverAccumulator::init(&pk, first, &mut T::init()).expect("init failed");
    let mut accumulators = vec![prover.accumulator().clone()];
    let mut rounds = vec![];
    for fresh in provers {
        let (n, start) = (fresh.len(), Instant::now());
        let mut transcript = T::init();
        prover = prover.fold(&pk, fresh, None, &mut transcript).expect("fold failed");
        rounds.push((n, transcript.finalize(), start.elapsed()));
        accumulators.push(prover.accumulator().clone());
    }
    assert!(prover.is_satisfied(&pk), "unsatisfied accumulator");

    // Verifier: read the instances from their partial proofs, replay the rounds.
    let vk = pk.get_vk();
    let read = |group: &[Published]| -> Vec<FoldingInstance<F, DefaultPCS>> {
        group
            .iter()
            .map(|p| {
                let mut transcript = T::init_from_bytes(&p.partial_proof);
                read_instance(vk, &columns(&p.public_inputs), &mut transcript)
                    .expect("read_instance failed")
            })
            .collect()
    };
    let first = read(&published.remove(0)).remove(0);
    let mut verifier = Accumulator::init(vk, first, &mut T::init()).expect("init failed");
    assert!(verifier == accumulators[0], "init: accumulators differ");
    for (round, ((n, proof, prover_time), group)) in (1..).zip(rounds.iter().zip(&published)) {
        let start = Instant::now();
        let mut transcript = T::init_from_bytes(proof);
        verifier = verifier
            .fold(vk, &read(group), None, &mut transcript)
            .expect("verifier fold failed");
        let verifier_time = start.elapsed();
        assert!(
            verifier == accumulators[round],
            "round {round}: accumulators differ"
        );
        println!(
            "round {round}: folded {n} instance(s), folding proof {} B, prover {prover_time:.2?}, \
             verifier {verifier_time:.2?}",
            proof.len()
        );
    }

    // Decider: the final accumulator satisfies its relaxed relation.
    let start = Instant::now();
    let mut transcript = T::init();
    prove_relaxed_trace(&srs, &pk, prover, &mut transcript).expect("decider prover failed");
    let decider = transcript.finalize();
    let prover_time = start.elapsed();
    let start = Instant::now();
    verify_relaxed_trace(vk, &verifier, &mut T::init_from_bytes(&decider))
        .expect("decider verifier failed")
        .verify(&DefaultPCS::get_verifier_params(&srs))
        .expect("decider proof rejected");
    let verifier_time = start.elapsed();
    println!(
        "decider: proof {} B, prover {prover_time:.2?}, verifier {verifier_time:.2?}",
        decider.len()
    );

    // One-shot: fold fresh instances and prove the result in a single proof.
    let (circuits, public_inputs): (Vec<_>, Vec<_>) =
        (0..ONE_SHOT_K).map(|_| random_instance(k)).unzip();
    let columns: Vec<_> = public_inputs.iter().map(|pi| columns(pi)).collect();
    let instances: Vec<Vec<&[F]>> = columns.iter().map(|c| c.to_vec()).collect();
    let instances: Vec<&[&[F]]> = instances.iter().map(Vec::as_slice).collect();
    let start = Instant::now();
    let mut transcript = T::init();
    prove_one_shot(&srs, &pk, &circuits, &instances, &mut transcript, OsRng)
        .expect("one-shot prover failed");
    let proof = transcript.finalize();
    let prover_time = start.elapsed();
    let start = Instant::now();
    verify_one_shot(vk, &instances, &mut T::init_from_bytes(&proof))
        .expect("one-shot verifier failed")
        .verify(&DefaultPCS::get_verifier_params(&srs))
        .expect("one-shot proof rejected");
    let verifier_time = start.elapsed();
    println!(
        "one-shot: folded {ONE_SHOT_K} instances, proof {} B, prover {prover_time:.2?}, \
         verifier {verifier_time:.2?}",
        proof.len()
    );
}

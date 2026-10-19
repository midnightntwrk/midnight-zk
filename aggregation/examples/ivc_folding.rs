//! Incrementally Verifiable Computation with Protogalaxy folding.
//!
//! Same transition as the `ivc` example (a Poseidon chain), but the step
//! circuit verifies a Protogalaxy fold instead of a proof: each step folds the
//! previous step's instance and only commits to its own witness, so no proof
//! is produced per step. A single decider proof is produced at the end, for
//! the final accumulator. The step circuit uses fflonk over KZG with
//! `T_MAX = 16`, so the SRS must have `2^(K + 4)` points.
//!
//! Run with `cd aggregation && cargo run --release --example ivc_folding`.
//!
//! DO NOT add this example to the CI as it is slow.

#[path = "circuits/poseidon_chain.rs"]
mod poseidon_chain;

use std::time::Instant;

use midnight_aggregation::{
    ivc::IvcState,
    ivc_folding::{self, FoldingIvcProver, FoldingPCS},
};
use midnight_zk_stdlib::utils::plonk_api::{SrsSource, load_srs};
use poseidon_chain::PoseidonChain;

fn main() {
    // Circuit size parameter (log2 of rows). It must fit the folding step circuit.
    const K: u32 = 15;

    const N: usize = 1; // Number of Poseidon iterations per IVC step.
    const STEPS: usize = 5; // Number of IVC steps to run.

    type T = PoseidonChain<N>;

    let srs = load_srs::<FoldingPCS>(SrsSource::Midnight, K);

    let start = Instant::now();
    let (keys, verifier) = ivc_folding::setup::<T>(srs, K, ());
    println!("Setup completed in {:.2?}", start.elapsed());

    let mut prover = FoldingIvcProver::new(&keys);
    for i in 0..STEPS {
        let start = Instant::now();
        prover.prove_step(()).unwrap();
        println!("Step {i}: prove {:.2?}", start.elapsed());
    }

    let start = Instant::now();
    let (instance, proof) = prover.finalize().unwrap();
    println!("Finalize (decider): {:.2?}", start.elapsed());

    let start = Instant::now();
    verifier.verify(&instance, &proof).unwrap();
    println!("Final verify: {:.2?}", start.elapsed());

    let proof_size =
        proof.partial_proof.len() + proof.folding_proof.len() + proof.decider_proof.len();
    println!(
        "Proof size: {proof_size} bytes (partial {}, folding {}, decider {}), accumulator {} bytes",
        proof.partial_proof.len(),
        proof.folding_proof.len(),
        proof.decider_proof.len(),
        instance.accumulator_size()
    );

    println!(
        "IVC completed: {STEPS} steps from\n genesis {:?}\n      to {:?}",
        T::genesis(&()),
        instance.state()
    );
}

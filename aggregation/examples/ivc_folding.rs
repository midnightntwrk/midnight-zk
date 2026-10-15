//! Incrementally Verifiable Computation with Protogalaxy folding.
//!
//! Same transition as the `ivc` example (Poseidon chain), but the step circuit
//! runs the folding verifier: each step folds the previous step's instance
//! natively and only commits to its own witness (no proof per step); the
//! final verifier folds the last instance and checks one decider proof.
//!
//! Negative check: `TAMPER_STEP=<i>` makes step `i` claim a wrong next state
//! (two transitions instead of one); the final verification must then fail.
//!
//! DO NOT add this example to the CI as it is slow.

#[path = "circuits/poseidon_chain.rs"]
mod poseidon_chain;

use std::time::Instant;

use midnight_aggregation::{
    ivc::{IvcState, IvcTransition},
    ivc_folding::{self, FoldingIvcCircuit, FoldingIvcProver},
};
use midnight_zk_stdlib::{
    DefaultPCS,
    utils::plonk_api::{SrsSource, load_srs},
};
use poseidon_chain::PoseidonChain;

fn main() {
    // Circuit size parameter (log2 of rows); fflonk needs an SRS of
    // 2^(K + LOG2_T_MAX) points.
    const K: u32 = 16;

    const N: usize = 1; // Number of Poseidon iteration per IVC step.
    const STEPS: usize = 10; // Number of IVC steps to run.

    type T = PoseidonChain<N>;

    let tamper_step: Option<usize> = std::env::var("TAMPER_STEP")
        .ok()
        .map(|s| s.parse().expect("TAMPER_STEP: step index"));

    let model = midnight_zk_stdlib::cost_model(&FoldingIvcCircuit::<T>::new(K, ()), Some(K), false);
    println!(
        "Step circuit: k = {}, rows = {}, table rows = {}",
        model.k, model.rows, model.table_rows
    );

    let srs = load_srs::<DefaultPCS>(SrsSource::Midnight, K);

    let start = Instant::now();
    let (keys, verifier) = ivc_folding::setup::<T>(srs, K, ());
    println!("Setup completed in {:.2?}", start.elapsed());

    let mut prover = FoldingIvcProver::new(&keys);
    for i in 0..STEPS {
        let start = Instant::now();
        let timings = if tamper_step == Some(i) {
            let skipped = T::transition(&(), &T::transition(&(), prover.state(), ()), ());
            prover.prove_step_claiming((), skipped).unwrap()
        } else {
            prover.prove_step(()).unwrap()
        };
        println!(
            "Step {i}: total {:.2?} (native fold {:.2?}, synthesis + commit {:.2?})",
            start.elapsed(),
            timings.fold,
            timings.commit
        );
    }

    let (instance, proof, timings) = prover.finalize().unwrap();
    println!(
        "Finalize: last fold {:.2?}, decider prove {:.2?}",
        timings.fold, timings.decider
    );
    println!(
        "Sizes (bytes): accumulator {}, last partial proof {}, last folding proof {}, decider proof {}",
        instance.accumulator_size(),
        proof.partial_proof.len(),
        proof.folding_proof.len(),
        proof.decider_proof.len()
    );

    let start = Instant::now();
    let result = verifier.verify(&instance, &proof);
    println!("Final verify: {:.2?}, {result:?}", start.elapsed());

    match (tamper_step, result) {
        (None, Ok(())) => println!(
            "IVC completed: {STEPS} steps from\n genesis {:?}\n      to {:?}",
            T::genesis(&()),
            instance.state()
        ),
        (None, Err(e)) => panic!("honest folding IVC rejected: {e}"),
        (Some(i), Err(_)) => println!("Tampered step {i}: rejected as expected"),
        (Some(i), Ok(())) => panic!("tampered step {i} accepted"),
    }
}

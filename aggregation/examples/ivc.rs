//! Incrementally Verifiable Computation (IVC) using the aggregation API.
//!
//! This example demonstrates how to use the [`Ivc`] API with a transition
//! function that iteratively hashes a value using Poseidon.
//!
//! DO NOT add this example to the CI as it is slow.

#[path = "circuits/poseidon_chain.rs"]
mod poseidon_chain;

use std::time::Instant;

use midnight_aggregation::ivc::{self, IvcState};
use midnight_zk_stdlib::{
    DefaultPCS,
    utils::plonk_api::{SrsSource, load_srs},
};
use poseidon_chain::PoseidonChain;

fn main() {
    // Circuit size parameter (log2 of rows). Must be large enough to fit the
    // IVC circuit; ideally the minimum possible value. If too small, the error
    // message will hint at a valid (but not necessarily optimal) value, e.g.
    // `keygen_vk should not fail: SrsError(14, 19)` means K = 19 works, but a
    // smaller K might too. Binary-search to find it.
    const K: u32 = 18;

    const N: usize = 1_000; // Number of Poseidon iteration per IVC step.
    const STEPS: usize = 3; // Number of IVC steps to run.

    let srs = load_srs::<DefaultPCS>(SrsSource::Midnight, K);

    let start = Instant::now();
    let (mut prover, verifier) = ivc::setup::<PoseidonChain<N>>(srs, K, ());
    println!("IVC setup completed in {:.2?}", start.elapsed());

    for i in 0..STEPS {
        let start = Instant::now();
        let proof = prover.prove_step(()).unwrap();
        let prove_time = start.elapsed();

        let instance = prover.instance();

        let start = Instant::now();
        verifier.verify(&instance, &proof).unwrap();
        let verify_time = start.elapsed();

        println!("Step {i}: prove {prove_time:.2?}, verify {verify_time:.2?}");
    }

    println!(
        "IVC completed: {STEPS} steps from\n genesis {:?}\n      to {:?}",
        PoseidonChain::<N>::genesis(&()),
        prover.instance().state()
    );
}

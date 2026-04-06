//! Multi-circuit proof aggregation via IVC.
//!
//! This example demonstrates on-the-fly aggregation of proofs from different
//! inner circuits (SHA-256 preimage and Poseidon preimage) using the
//! [`multi_circuit_aggregator`](midnight_aggregation::multi_circuit_aggregator)
//! module.
//!
//! The IVC aggregator is set up once with a shared SRS and architecture.
//! Inner circuits can then be introduced, proved and folded in at any point,
//! without the aggregator knowing about them in advance.
//!
//! The requirements for an inner circuit to be aggregatable are:
//! - It must use the [`ZkStdLibArch`] chosen at IVC setup time.
//! - It must encode its statement as a single formatted public input.
//! - It must be padded to the common circuit size `K`.
//!
//! The single-public-input restriction is not a real limitation: any circuit
//! can hash its statement into a single field element. On the other hand, the
//! shared-`K` constraint can be removed by extending the verifier gadget to
//! accept dynamic domain parameters.
//!
//! DO NOT add this example to the CI as it is slow.

#[path = "circuits/aggregatable/poseidon_preimage.rs"]
mod aggregatable_poseidon_preimage;
#[path = "circuits/aggregatable/sha_preimage.rs"]
mod aggregatable_sha_preimage;

use std::time::Instant;

use aggregatable_poseidon_preimage::PoseidonPreimageCircuit as PoseidonCircuit;
use aggregatable_sha_preimage::AggregatableShaPreimageCircuit as ShaCircuit;
use midnight_aggregation::multi_circuit_aggregator::{
    AggregationWitness, InnerCircuitsContext, ProofAggregation,
};
use midnight_circuits::{
    hash::poseidon::PoseidonState,
    verifier::{BlstrsEmulation, SelfEmulation},
};
use midnight_zk_stdlib::{prove, setup_pk, setup_vk, utils::plonk_api::filecoin_srs, ZkStdLibArch};
use rand::rngs::OsRng;

type F = <BlstrsEmulation as SelfEmulation>::F;

/// Union of all architectures needed by the inner circuits.
fn inner_arch() -> ZkStdLibArch {
    ZkStdLibArch {
        sha2_256: true,
        poseidon: true,
        ..ZkStdLibArch::default()
    }
}

fn main() {
    // Circuit size parameters (log2 of rows).
    const IVC_K: u32 = 19;

    // Shared K for all inner circuits (must accommodate the largest one).
    const INNER_K: u32 = 13;

    // The IVC aggregator only requires a shared SRS and architecture. It does
    // not need to know which circuits will be aggregated. Inner circuits can be
    // introduced, proved and folded in on-the-fly, after IVC initialization.
    let inner_srs = filecoin_srs(INNER_K);
    let inner_ctx = InnerCircuitsContext::new(inner_arch(), INNER_K, inner_srs.verifier_params());

    let aggregator_srs = filecoin_srs(IVC_K);
    let start = Instant::now();
    let (mut aggregator, verifier) = ProofAggregation::setup(aggregator_srs, IVC_K, inner_ctx);
    println!("Aggregator setup completed in {:.2?}\n", start.elapsed());

    // --- Aggregate a SHA-256 preimage proof (circuit introduced just now) ---
    let sha_vk = setup_vk(&inner_srs, &ShaCircuit);
    let sha_pk = setup_pk(&ShaCircuit, &sha_vk);

    let (sha_x, sha_w) = aggregatable_sha_preimage::random_instance();
    let inner_proof = prove::<ShaCircuit, PoseidonState<F>>(
        &inner_srs,
        &sha_pk,
        &ShaCircuit,
        &sha_x,
        sha_w,
        OsRng,
    )
    .expect("SHA-256 proof generation should not fail");
    let witness = AggregationWitness::new::<ShaCircuit>(sha_vk.clone(), sha_x, inner_proof);

    let start = Instant::now();
    aggregator.aggregate(witness).unwrap();
    println!("Aggregate a SHA2-256 proof: {:.2?}", start.elapsed());

    // --- Aggregate a Poseidon preimage proof (circuit introduced just now) ---
    let poseidon_vk = setup_vk(&inner_srs, &PoseidonCircuit);
    let poseidon_pk = setup_pk(&PoseidonCircuit, &poseidon_vk);

    let (poseidon_x, poseidon_w) = aggregatable_poseidon_preimage::random_instance();
    let inner_proof = prove::<PoseidonCircuit, PoseidonState<F>>(
        &inner_srs,
        &poseidon_pk,
        &PoseidonCircuit,
        &poseidon_x,
        poseidon_w,
        OsRng,
    )
    .expect("Poseidon proof generation should not fail");
    let witness =
        AggregationWitness::new::<PoseidonCircuit>(poseidon_vk.clone(), poseidon_x, inner_proof);

    let start = Instant::now();
    aggregator.aggregate(witness).unwrap();
    println!("Aggregate a Poseidon proof: {:.2?}", start.elapsed());

    // --- Aggregate another SHA-256 preimage proof ---
    let (sha_x, sha_w) = aggregatable_sha_preimage::random_instance();
    let inner_proof = prove::<ShaCircuit, PoseidonState<F>>(
        &inner_srs,
        &sha_pk,
        &ShaCircuit,
        &sha_x,
        sha_w,
        OsRng,
    )
    .expect("SHA-256 proof generation should not fail");
    let witness = AggregationWitness::new::<ShaCircuit>(sha_vk, sha_x, inner_proof);

    let start = Instant::now();
    let proof = aggregator.aggregate(witness).unwrap();
    println!("Aggregate a SHA2-256 proof: {:.2?}", start.elapsed());

    // --- Verify the final aggregation proof ---
    let start = Instant::now();
    let instance = aggregator.instance();
    verifier.verify_aggregation(&instance, &proof).unwrap();
    println!("\nVerification: {:.2?}", start.elapsed());

    // Print aggregated claims (derived from the verified instance).
    let claims = instance.state().claims();
    println!(
        "\nAggregated {} proofs from 2 different circuits:",
        claims.len()
    );
    for (i, claim) in claims.iter().enumerate() {
        println!(
            "  {i}: vk={:?}, statement={:?}",
            claim.vk.vk().transcript_repr(),
            claim.statement,
        );
    }
}

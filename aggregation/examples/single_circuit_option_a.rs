//! Option (A): batch proving via aggregation for a SINGLE circuit.
//!
//! Demonstrates the "batch proving" use case discussed for Zswap/Dust: given
//! `K` instances of one circuit (here an aggregation-compatible SHA-256
//! preimage circuit, all sharing one verifying key), fold their `K` inner
//! proofs into a *single* succinct proof whose verification cost and size are
//! constant in `K`.
//!
//! Flow:
//!   1. Prove `K` instances of the inner circuit (in parallel via `batch_prove`).
//!   2. Set up the IVC aggregator once.
//!   3. Fold all inner proofs into one with `aggregate_same_circuit`.
//!   4. Verify the single aggregated proof.
//!
//! Note: this is the aggregation (Option C machinery) applied to the Option (A)
//! single-circuit case. It does NOT modify the soundness-critical PLONK prover;
//! it reuses the reviewed `multi_circuit_aggregator`.
//!
//! DO NOT add this example to the CI as it is slow (needs the IVC SRS).

#[path = "circuits/aggregatable/sha_preimage.rs"]
mod aggregatable_sha_preimage;

use std::time::Instant;

use aggregatable_sha_preimage::AggregatableShaPreimageCircuit as ShaCircuit;
use midnight_aggregation::{
    ivc::IvcCircuit,
    multi_circuit_aggregator::{aggregate_same_circuit, InnerCircuitsContext, ProofAggregation},
};
use midnight_circuits::{
    hash::poseidon::PoseidonState,
    verifier::{BlstrsEmulation, SelfEmulation},
};
use midnight_zk_stdlib::{
    batch_prove, cs_degree, setup_pk, setup_vk,
    utils::plonk_api::{load_srs, SrsSource},
    Relation,
};

type F = <BlstrsEmulation as SelfEmulation>::F;

fn main() {
    // Circuit size parameters (log2 of rows).
    const IVC_K: u32 = 19;
    const INNER_K: u32 = 13;
    // Number of same-circuit instances to batch into one proof.
    const K: usize = 4;

    let inner_arch = ShaCircuit.used_chips();

    // --- 1. Prove K instances of the SAME circuit (shared vk), in parallel. ---
    let inner_srs = load_srs(SrsSource::Filecoin, INNER_K, cs_degree(inner_arch));
    let inner_vk = setup_vk(&inner_srs, &ShaCircuit);
    let inner_pk = setup_pk(&ShaCircuit, &inner_vk);

    let start = Instant::now();
    let samples: [_; K] = std::array::from_fn(|_| aggregatable_sha_preimage::random_instance());
    let instances: Vec<[u8; 32]> = samples.iter().map(|(x, _)| *x).collect();
    let witnesses: Vec<[u8; 24]> = samples.iter().map(|(_, w)| *w).collect();

    let inner_proofs = batch_prove::<ShaCircuit, PoseidonState<F>>(
        &inner_srs,
        &inner_pk,
        &ShaCircuit,
        &instances,
        witnesses,
    )
    .expect("inner proof generation should not fail");
    println!(
        "{K} inner proofs generated (in parallel) in {:.2?}",
        start.elapsed()
    );

    // --- 2. Set up the IVC aggregator once. ---
    let inner_ctx =
        InnerCircuitsContext::new(inner_arch, INNER_K, inner_srs.verifier_params());
    let aggregator_srs = load_srs(
        SrsSource::Midnight,
        IVC_K,
        IvcCircuit::<ProofAggregation>::cs_degree(),
    );
    let start = Instant::now();
    let (mut aggregator, verifier) = ProofAggregation::setup(aggregator_srs, IVC_K, inner_ctx);
    println!("Aggregator setup completed in {:.2?}", start.elapsed());

    // --- 3. Fold all K inner proofs into ONE aggregated proof. ---
    let start = Instant::now();
    let proof = aggregate_same_circuit::<ShaCircuit>(
        &mut aggregator,
        &inner_vk,
        &instances,
        &inner_proofs,
    )
    .expect("aggregation should not fail");
    println!(
        "Folded {K} proofs into one in {:.2?} ({} proof bytes)",
        start.elapsed(),
        proof.len()
    );

    // --- 4. Verify the single aggregated proof. ---
    let instance = aggregator.instance();
    let start = Instant::now();
    verifier
        .verify_aggregation(&instance, &proof)
        .expect("aggregated proof should verify");
    println!("Verified aggregated proof in {:.2?}", start.elapsed());

    let claims = instance.state().claims();
    assert_eq!(claims.len(), K, "expected one claim per instance");
    println!("\nAggregated {} same-circuit proofs into a single proof.", claims.len());
}

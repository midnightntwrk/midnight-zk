//! Protogalaxy folding example.
//!
//! Folds `NB_FOLDED` SHA-256 preimage proofs into a single accumulator and
//! verifies the fold. Also benchmarks standard PLONK proving for comparison.
//!
//! DO NOT add this example to the CI as it is slow.

#[path = "circuits/sha_multi.rs"]
mod sha_multi;

use std::time::Instant;

use sha_multi::{ShaMultiCircuit as ShaPreimageCircuit, K, N_SHA};

use midnight_proofs::{
    plonk::protogalaxy::{ProtogalaxyProver, ProtogalaxyVerifier},
    poly::commitment::Guard,
    transcript::{CircuitTranscript, Transcript},
};
use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_zk_stdlib::{
    cs_degree, prove, setup_pk, setup_vk, verify,
    utils::plonk_api::{load_srs, SrsSource},
    MidnightCircuit, Relation,
};
use midnight_proofs::circuit::Value;
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

/// Number of instances to fold together.
const NB_FOLDED: usize = 8;

fn main() {
    // ── Setup ─────────────────────────────────────────────────────────────────
    let t = Instant::now();
    let arch = ShaPreimageCircuit.used_chips();
    let srs = load_srs(SrsSource::Filecoin, K, cs_degree(arch));
    let relation = ShaPreimageCircuit;
    let vk = setup_vk(&srs, &relation);
    let pk = setup_pk(&relation, &vk);
    println!("Setup completed in {:.2?}", t.elapsed());

    // ── Generate witnesses ────────────────────────────────────────────────────
    println!("Circuit: {N_SHA}× SHA-256 per instance, K={K} ({} rows)", 1 << K);

    let pairs: [(_, _); NB_FOLDED] =
        core::array::from_fn(|_| sha_multi::random_instance());

    // ── Standard PLONK: prove all NB_FOLDED instances individually ────────────
    let t = Instant::now();
    let mut total_proof_size = 0;
    let mut circuits = Vec::with_capacity(NB_FOLDED);
    let mut instances: Vec<Vec<Vec<F>>> = Vec::with_capacity(NB_FOLDED);
    let mut proofs: Vec<Vec<u8>> = Vec::with_capacity(NB_FOLDED);

    for (instance, witness) in &pairs {
        let proof = prove::<ShaPreimageCircuit, PoseidonState<F>>(
            &srs,
            &pk,
            &relation,
            instance,
            *witness,
            OsRng,
        )
        .expect("PLONK prove failed");
        total_proof_size += proof.len();

        circuits.push(MidnightCircuit::new(
            &relation,
            Value::known(*instance),
            Value::known(*witness),
            None,
        ));
        instances.push(vec![
            vec![],
            sha_multi::ShaMultiCircuit::format_instance(instance).expect("format_instance failed"),
        ]);
        proofs.push(proof);
    }
    let plonk_time = t.elapsed();
    println!(
        "Standard PLONK ({NB_FOLDED}× prove): {plonk_time:.2?}   proof size: {total_proof_size} B total"
    );

    // ── Standard PLONK: verify all NB_FOLDED instances individually ───────────
    let t = Instant::now();
    let params_verifier = srs.verifier_params();
    for ((instance, _witness), proof) in pairs.iter().zip(proofs.iter()) {
        verify::<ShaPreimageCircuit, PoseidonState<F>>(
            &params_verifier,
            &vk,
            instance,
            None,
            proof,
        )
        .expect("PLONK verify failed");
    }
    let plonk_verify_time = t.elapsed();
    println!(
        "Standard PLONK ({NB_FOLDED}× verify): {plonk_verify_time:.2?}"
    );

    let instances_slices: Vec<Vec<&[F]>> = instances
        .iter()
        .map(|cols| cols.iter().map(|c| c.as_slice()).collect())
        .collect();
    let instances_ref: Vec<&[&[F]]> =
        instances_slices.iter().map(|cols| cols.as_slice()).collect();

    // ── Protogalaxy: fold + verify accumulator ────────────────────────────────
    let t = Instant::now();
    let mut prover_transcript = CircuitTranscript::<PoseidonState<F>>::init();
    ProtogalaxyProver::<_, _, NB_FOLDED>::fold(
        &srs,
        pk.pk().clone(),
        circuits,
        &instances_ref,
        OsRng,
        &mut prover_transcript,
    )
    .expect("Protogalaxy folding prover failed");
    let fold_time = t.elapsed();

    let proof_bytes = prover_transcript.finalize();
    println!(
        "Protogalaxy fold ({NB_FOLDED}× fold):   {fold_time:.2?}   proof size: {} B",
        proof_bytes.len()
    );

    let t = Instant::now();
    let mut verifier_transcript =
        CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&proof_bytes);
    let guard = ProtogalaxyVerifier::<_, _, NB_FOLDED>::fold(
        vk.vk(),
        &instances_ref,
        &mut verifier_transcript,
    )
    .expect("Protogalaxy folding verifier failed");
    let fold_verify_time = t.elapsed();

    let t = Instant::now();
    guard
        .verify(&params_verifier)
        .expect("Protogalaxy accumulator verification failed");
    let kzg_verify_time = t.elapsed();

    println!(
        "Protogalaxy verify ({NB_FOLDED}× fold+check): {fold_verify_time:.2?}  KZG pairing: {kzg_verify_time:.2?}"
    );
    println!("\nProtogalaxy folding succeeded for {NB_FOLDED} instances.");
}

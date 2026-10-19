//! The commit phases of the prover ([`commit_phases`]) and of the verifier
//! ([`parse_trace`]) agree on the commitments and on the challenges.

use blake2b_simd::State;
use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_core::OsRng;

use super::{
    create_proof, keygen_pk, keygen_vk_with_k, parse_trace, prepare,
    prover::commit_phases,
    test_circuit::{K, SquareCircuit},
};
use crate::{
    poly::{
        commitment::{Guard, PolynomialCommitmentScheme},
        fflonk::Fflonk,
        kzg::KZGCommitmentScheme,
    },
    transcript::{CircuitTranscript, Hashable, Transcript},
};

type T = CircuitTranscript<State>;

fn check_commit_phases<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &SquareCircuit, K).unwrap();
    let pk = keygen_pk(vk, &SquareCircuit).unwrap();
    let vk = pk.get_vk();
    let instance = [Fq::ONE];
    let instances: &[&[Fq]] = &[&instance];

    // Prover: commit phases only.
    let mut prover_transcript = T::init();
    let trace = commit_phases(
        &params,
        &pk,
        &SquareCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        &mut prover_transcript,
        OsRng,
    )
    .unwrap();
    assert!(!trace.theta.is_empty() && trace.y.len() > 1);

    // Verifier: read the commit phases from the same bytes.
    let prover_next: Fq = prover_transcript.squeeze_challenge();
    let bytes = prover_transcript.finalize();
    let mut verifier_transcript = T::init_from_bytes(&bytes);
    let parsed = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        &mut verifier_transcript,
    )
    .unwrap();

    assert_eq!(parsed.theta, trace.theta);
    assert_eq!(parsed.beta, trace.beta);
    assert_eq!(parsed.gamma, trace.gamma);
    assert_eq!(parsed.trash_challenges, trace.trash_challenges);
    assert_eq!(parsed.y, trace.y);
    // Both transcripts are left in the same state, so they hold the same
    // commitments.
    let verifier_next: Fq = verifier_transcript.squeeze_challenge();
    assert_eq!(verifier_next, prover_next);

    // The full proof, which starts with the same commit phases, still verifies.
    let mut transcript = T::init();
    create_proof::<_, CS, _, _>(
        &params,
        &pk,
        &SquareCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        &mut transcript,
        OsRng,
    )
    .unwrap();
    let proof = transcript.finalize();
    let mut transcript = T::init_from_bytes(&proof);
    let guard = prepare::<_, CS, _>(
        vk,
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        &mut transcript,
    )
    .unwrap();
    guard.verify(&CS::get_verifier_params(&params)).unwrap();
}

#[test]
fn commit_phases_match_verifier_kzg() {
    check_commit_phases::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn commit_phases_match_verifier_fflonk() {
    check_commit_phases::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

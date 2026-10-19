//! Fresh instances: the prover's commit phases and the verifier's read agree,
//! and the commitments of instances combine like their polynomials.

use blake2b_simd::State;
use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_core::OsRng;
use rayon::iter::ParallelIterator;

use super::{FoldingInstance, ProverInstance, commit_instance, read_instance};
use crate::{
    plonk::{
        ProvingKey,
        argument::prover::Committed,
        keygen_pk, keygen_vk_with_k,
        test_circuit::{K, SquareCircuit},
    },
    poly::{
        Polynomial, commitment::PolynomialCommitmentScheme, fflonk::Fflonk,
        kzg::KZGCommitmentScheme,
    },
    transcript::{CircuitTranscript, Hashable, Transcript},
};

type T = CircuitTranscript<State>;

/// Commits `circuit` as a fresh instance; returns it with the transcript
/// bytes.
fn commit<'a, CS: PolynomialCommitmentScheme<Fq>>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<Fq, CS>,
    circuit: SquareCircuit,
) -> (ProverInstance<'a, Fq, CS>, Vec<u8>)
where
    CS::Commitment: Hashable<State>,
{
    let mut transcript = T::init();
    let instance = commit_instance(
        params,
        pk,
        &circuit,
        &[&[circuit.public_input()]],
        &mut transcript,
        OsRng,
    )
    .unwrap();
    (instance, transcript.finalize())
}

fn check_round_trip<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let circuit = SquareCircuit::default();
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &circuit, K).unwrap();
    let pk = keygen_pk(vk, &circuit).unwrap();

    let (instance, bytes) = commit(&params, &pk, circuit);
    let public_input = [circuit.public_input()];
    let read: FoldingInstance<Fq, CS> = read_instance(
        pk.get_vk(),
        &[&public_input],
        &mut T::init_from_bytes(&bytes),
    )
    .unwrap();

    assert_eq!(&read, instance.public());
    assert_eq!(read.instances(), [public_input.to_vec()]);
    assert!(!read.challenges().theta.is_empty() && read.challenges().y.len() > 1);
}

fn check_commitment_combination<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &SquareCircuit::default(), K).unwrap();
    let pk = keygen_pk(vk, &SquareCircuit::default()).unwrap();

    let (a, _) = commit(&params, &pk, SquareCircuit::default());
    let other = SquareCircuit {
        start: 3,
        corrupt: false,
    };
    let (b, _) = commit(&params, &pk, other);
    let weights = [Fq::random(OsRng), Fq::random(OsRng)];

    let combined =
        FoldingInstance::linear_combination(&[a.public(), b.public()], &weights).unwrap();

    // The phase-1 group of the combined witness, committed as `commit_phases`
    // does (into a throwaway transcript).
    let group = Committed::linear_combination(
        &[&a.trace.phase1_committed, &b.trace.phase1_committed],
        &weights,
    );
    let polys = group.par_polys().map(|(l, p)| (l.clone(), p.clone())).collect();
    let (_, commitment) =
        Committed::commit::<CS, _, _>(&params, polys, Polynomial::to_delta, &mut T::init())
            .unwrap();
    assert!(combined.phase1_commitment() == &commitment);
}

#[test]
fn round_trip_kzg() {
    check_round_trip::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn round_trip_fflonk() {
    check_round_trip::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn commitment_combination_kzg() {
    check_commitment_combination::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn commitment_combination_fflonk() {
    check_commitment_combination::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

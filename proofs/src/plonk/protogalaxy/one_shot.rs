//! One-shot folding: fold `k` fresh instances in one round and produce the
//! decider proof, in a single proof.
//!
//! The output is a single proof, not an accumulator: it cannot be folded
//! further. The whole proof is one transcript: the `k` instances (commit
//! phases), the folding proof, then the decider proof.

use std::hash::Hash;

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use super::{
    Accumulator, ProverAccumulator, commit_instance, prove_relaxed_trace, read_instance,
    verify_relaxed_trace,
};
use crate::{
    plonk::{Circuit, Error, ProvingKey, VerifyingKey},
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Sampleable, Transcript},
};

/// Folds the `k = circuits.len() ≥ 1` fresh instances of `circuits` (with
/// public inputs `instances[i]` for `circuits[i]`) in one round and proves the
/// folded accumulator with the decider, all into `transcript`: the `k`
/// instances in order, then the folding proof (if `k ≥ 2`), then the decider
/// proof. Verify with [`verify_one_shot`].
pub fn prove_one_shot<F, CS, T, C>(
    params: &CS::Parameters,
    pk: &ProvingKey<F, CS>,
    circuits: &[C],
    instances: &[&[&[F]]],
    transcript: &mut T,
    mut rng: impl RngCore + CryptoRng,
) -> Result<(), Error>
where
    F: WithSmallOrderMulGroup<3>
        + Sampleable<T::Hash>
        + Hashable<T::Hash>
        + Hash
        + Ord
        + FromUniformBytes<64>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
    C: Circuit<F>,
{
    if circuits.is_empty() || instances.len() != circuits.len() {
        return Err(Error::InvalidInstances);
    }
    let mut fresh = circuits
        .iter()
        .zip(instances)
        .map(|(circuit, instance)| {
            commit_instance(params, pk, circuit, instance, transcript, &mut rng)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let rest = fresh.split_off(1);
    let first = fresh.pop().expect("k ≥ 1");

    let mut acc = ProverAccumulator::init(pk, first, transcript)?;
    if !rest.is_empty() {
        acc = acc.fold(pk, rest, None, transcript)?;
    }
    prove_relaxed_trace(params, pk, acc, transcript)
}

/// Verifies a proof of [`prove_one_shot`] for the public inputs `instances`
/// of the `k ≥ 1` circuits, up to the PCS check: finalise the returned guard.
pub fn verify_one_shot<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    if instances.is_empty() {
        return Err(Error::InvalidInstances);
    }
    let mut fresh = instances
        .iter()
        .map(|instance| read_instance(vk, instance, transcript))
        .collect::<Result<Vec<_>, _>>()?;
    let rest = fresh.split_off(1);
    let first = fresh.pop().expect("k ≥ 1");

    let mut acc = Accumulator::init(vk, first, transcript)?;
    if !rest.is_empty() {
        acc = acc.fold(vk, &rest, None, transcript)?;
    }
    verify_relaxed_trace(vk, &acc, transcript)
}

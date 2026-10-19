//! Folding verifier: reads a fresh instance.

use ff::{FromUniformBytes, WithSmallOrderMulGroup};

use super::instance::{Challenges, FoldingInstance};
use crate::{
    plonk::{Error, VerifyingKey, parse_trace},
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Sampleable, Transcript},
};

/// Reads the commit phases of a fresh instance (the partial proof written by
/// [`commit_instance`](super::commit_instance)) for the public inputs
/// `instances`.
///
/// Committed instance columns are not supported: with the
/// `committed-instances` feature, none is committed (all of `instances` are
/// public inputs).
pub fn read_instance<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    instances: &[&[F]],
    transcript: &mut T,
) -> Result<FoldingInstance<F, CS>, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Ord,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    let trace = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        transcript,
    )?;
    Ok(FoldingInstance {
        phase1_commitment: trace.phase1_committed.commitment().clone(),
        phase2_commitment: trace.phase2_committed.commitment().clone(),
        instances: instances.iter().map(|i| i.to_vec()).collect(),
        challenges: Challenges {
            theta: trace.theta,
            beta: trace.beta,
            gamma: trace.gamma,
            trash: trace.trash_challenges,
            y: trace.y,
        },
    })
}

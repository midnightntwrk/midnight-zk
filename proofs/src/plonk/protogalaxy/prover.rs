//! Folding prover: commits a fresh instance (the commit phases of a plonk
//! proof, no quotient, no opening) and holds the running accumulator.

use std::hash::Hash;

use ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};

use super::instance::{Accumulator, Challenges, FoldingInstance};
use crate::{
    plonk::{Circuit, Error, ProvingKey, prover::commit_phases, traces::ProverTrace},
    poly::{LagrangeCoeff, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Sampleable, Transcript},
};

/// A fresh instance, prover side: the Lagrange-form trace after the commit
/// phases and its public data.
#[derive(Debug)]
pub struct ProverInstance<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
    pub(crate) public: FoldingInstance<F, CS>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProverInstance<'_, F, CS> {
    /// What the folding verifier reads for this instance.
    pub fn public(&self) -> &FoldingInstance<F, CS> {
        &self.public
    }
}

/// Synthesises `circuit` and runs the commit phases (phase-1 and phase-2
/// commitments and their challenges) into `transcript`, which then holds
/// the partial proof of this instance. No quotient, no opening.
///
/// Committed instance columns are not supported: with the
/// `committed-instances` feature, none is committed (all of `instances` are
/// public inputs).
pub fn commit_instance<'a, F, CS, T, C>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<F, CS>,
    circuit: &C,
    instances: &[&[F]],
    transcript: &mut T,
    rng: impl RngCore + CryptoRng,
) -> Result<ProverInstance<'a, F, CS>, Error>
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
    let (trace, [phase1_commitment, phase2_commitment]) = commit_phases(
        params,
        pk,
        circuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        transcript,
        rng,
    )?;
    let public = FoldingInstance {
        phase1_commitment,
        phase2_commitment,
        instances: instances.iter().map(|i| i.to_vec()).collect(),
        challenges: Challenges {
            theta: trace.theta.clone(),
            beta: trace.beta,
            gamma: trace.gamma,
            trash: trace.trash_challenges.clone(),
            y: trace.y.clone(),
        },
    };
    Ok(ProverInstance { trace, public })
}

/// The running accumulator, prover side: the folded trace (Lagrange form)
/// and the public accumulator. The trace's challenges and public inputs are
/// those of `public` (both are folded with the same weights).
#[derive(Debug)]
pub struct ProverAccumulator<'a, F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) public: Accumulator<F, CS>,
    pub(crate) trace: ProverTrace<'a, F, LagrangeCoeff>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProverAccumulator<'_, F, CS> {
    /// The public accumulator (what the folding verifier computes).
    pub fn accumulator(&self) -> &Accumulator<F, CS> {
        &self.public
    }
}

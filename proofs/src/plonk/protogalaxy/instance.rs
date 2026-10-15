//! The public (verifier-side) data of folding: a fresh instance and the
//! running accumulator, their transcript encoding and their folding.

use ff::{Field, PrimeField};

use crate::{
    plonk::Error,
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Transcript},
};

/// `a + x·(b − a)`, i.e. `L₀(x)·a + L₁(x)·b` on the folding domain `{0, 1}`.
pub(crate) fn fold_scalar<F: Field>(a: F, b: F, x: F) -> F {
    a + x * (b - a)
}

fn fold_scalars<F: Field>(a: &[F], b: &[F], x: F) -> Vec<F> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| fold_scalar(*a, *b, x)).collect()
}

/// The verifier challenges of an instance (folded, for an accumulator).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Challenges<F> {
    /// Lookup tuple compression, one per tuple position.
    pub theta: Vec<F>,
    /// Permutation and logup `β` (not Protogalaxy's `β⃗`).
    pub beta: F,
    /// Permutation `γ`.
    pub gamma: F,
    /// Powers `(1, c, ..., c^{M-1})` of the trash challenge, `M = cs.max_trash_terms()`;
    /// folded entry-wise, so a folded instance does not carry a single `c`.
    pub trash_powers: Vec<F>,
    /// Identity batching, one per identity.
    pub y: Vec<F>,
}

impl<F: Field> Challenges<F> {
    pub(crate) fn fold(&self, other: &Self, x: F) -> Self {
        Challenges {
            theta: fold_scalars(&self.theta, &other.theta, x),
            beta: fold_scalar(self.beta, other.beta, x),
            gamma: fold_scalar(self.gamma, other.gamma, x),
            trash_powers: fold_scalars(&self.trash_powers, &other.trash_powers, x),
            y: fold_scalars(&self.y, &other.y, x),
        }
    }

    /// Absorbs `θ⃗, β, γ, trash, y⃗`, in this order.
    fn absorb<T: Transcript>(&self, transcript: &mut T) -> Result<(), Error>
    where
        F: Hashable<T::Hash>,
    {
        let scalars = (self.theta.iter())
            .chain([&self.beta, &self.gamma])
            .chain(&self.trash_powers)
            .chain(&self.y);
        for scalar in scalars {
            transcript.common(scalar)?;
        }
        Ok(())
    }
}

/// A committed instance as the folding verifier sees it: the phase-1 and
/// phase-2 commitments, the public inputs (one vector per instance column)
/// and the challenges. Fresh instances come from
/// [`read_instance`](super::read_instance); accumulators hold a folded one.
#[derive(Clone, Debug)]
pub struct FoldingInstance<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) phase1_commitment: CS::Commitment,
    pub(crate) phase2_commitment: CS::Commitment,
    pub(crate) instances: Vec<Vec<F>>,
    pub(crate) challenges: Challenges<F>,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PartialEq for FoldingInstance<F, CS> {
    fn eq(&self, other: &Self) -> bool {
        self.phase1_commitment == other.phase1_commitment
            && self.phase2_commitment == other.phase2_commitment
            && self.instances == other.instances
            && self.challenges == other.challenges
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> FoldingInstance<F, CS> {
    /// Commitment to the phase-1 polynomials (advice, logup multiplicities).
    pub fn phase1_commitment(&self) -> &CS::Commitment {
        &self.phase1_commitment
    }

    /// Commitment to the phase-2 polynomials (permutation, logup, trash).
    pub fn phase2_commitment(&self) -> &CS::Commitment {
        &self.phase2_commitment
    }

    /// The public inputs, one vector per instance column.
    pub fn instances(&self) -> &[Vec<F>] {
        &self.instances
    }

    /// The challenges.
    pub fn challenges(&self) -> &Challenges<F> {
        &self.challenges
    }

    /// Absorbs the commitments and the public inputs: phase-1 commitment,
    /// phase-2 commitment, then every public input, column by column. The
    /// challenges of a fresh instance are not absorbed: they are derived
    /// from its own transcript (verifying key, public inputs, commitments).
    pub(crate) fn absorb_commitments_and_instances<T: Transcript>(
        &self,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Hashable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        transcript.common(&self.phase1_commitment)?;
        transcript.common(&self.phase2_commitment)?;
        for value in self.instances.iter().flatten() {
            transcript.common(value)?;
        }
        Ok(())
    }

    /// `self + x·(other − self)`, field by field (commitments with
    /// [`PolynomialCommitmentScheme::fold_commitments`]).
    pub(crate) fn fold(&self, other: &Self, x: F) -> Result<Self, Error> {
        let same_shape = self.instances.len() == other.instances.len()
            && (self.instances.iter().zip(&other.instances)).all(|(a, b)| a.len() == b.len());
        if !same_shape {
            return Err(Error::InvalidInstances);
        }
        Ok(FoldingInstance {
            phase1_commitment: CS::fold_commitments(
                &self.phase1_commitment,
                &other.phase1_commitment,
                x,
            ),
            phase2_commitment: CS::fold_commitments(
                &self.phase2_commitment,
                &other.phase2_commitment,
                x,
            ),
            instances: (self.instances.iter().zip(&other.instances))
                .map(|(a, b)| fold_scalars(a, b, x))
                .collect(),
            challenges: self.challenges.fold(&other.challenges, x),
        })
    }
}

/// The running accumulator, verifier side: a folded instance with
/// Protogalaxy's `β⃗ ∈ F^{log n}` and error term `e`, satisfying (when honest)
/// the relaxed relation `Σᵢ powᵢ(β⃗)·fᵢ = e` over the rows `i` of the domain.
#[derive(Clone, Debug)]
pub struct Accumulator<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) instance: FoldingInstance<F, CS>,
    pub(crate) betas: Vec<F>,
    pub(crate) error: F,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PartialEq for Accumulator<F, CS> {
    fn eq(&self, other: &Self) -> bool {
        self.instance == other.instance && self.betas == other.betas && self.error == other.error
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Accumulator<F, CS> {
    /// The folded instance.
    pub fn instance(&self) -> &FoldingInstance<F, CS> {
        &self.instance
    }

    /// Protogalaxy's `β⃗` (one per bit of the row index).
    pub fn betas(&self) -> &[F] {
        &self.betas
    }

    /// The error term `e`.
    pub fn error(&self) -> F {
        self.error
    }

    /// Absorbs the whole accumulator: phase-1 commitment, phase-2 commitment,
    /// public inputs (column by column), `θ⃗, β, γ, trash, y⃗`, `β⃗`, `e`.
    pub(crate) fn absorb<T: Transcript>(&self, transcript: &mut T) -> Result<(), Error>
    where
        F: Hashable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        self.instance.absorb_commitments_and_instances(transcript)?;
        self.instance.challenges.absorb(transcript)?;
        for beta in &self.betas {
            transcript.common(beta)?;
        }
        transcript.common(&self.error)?;
        Ok(())
    }

    /// What a folding round absorbs for the accumulator: its hash `acc_hash`
    /// (one element, the same hash the caller binds the accumulator with, e.g.
    /// in a step circuit's public input) or, without one, the whole
    /// accumulator ([`Self::absorb`]).
    pub(crate) fn absorb_bound<T: Transcript>(
        &self,
        acc_hash: Option<F>,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Hashable<T::Hash>,
        CS::Commitment: Hashable<T::Hash>,
    {
        match acc_hash {
            Some(hash) => Ok(transcript.common(&hash)?),
            None => self.absorb(transcript),
        }
    }
}

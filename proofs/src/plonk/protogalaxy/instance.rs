//! The public (verifier-side) data of folding: a fresh instance and the
//! running accumulator, their transcript encoding and their linear
//! combinations. Combinations take the weights of the folding domain
//! (computed by the caller), one per combined item.

use ff::{Field, PrimeField};

use crate::{
    plonk::Error,
    poly::commitment::PolynomialCommitmentScheme,
    transcript::{Hashable, Transcript},
};

/// `Σⱼ wⱼ·xⱼ`.
pub(super) fn combine_scalars<F: Field>(weights: &[F], values: &[F]) -> F {
    assert_eq!(weights.len(), values.len());
    weights.iter().zip(values).map(|(w, x)| *w * *x).sum()
}

/// Entry-wise `Σⱼ wⱼ·vectorsⱼ`; all vectors must have the same length.
pub(super) fn combine_vectors<F: Field>(weights: &[F], vectors: &[&[F]]) -> Vec<F> {
    assert_eq!(weights.len(), vectors.len());
    assert!(!vectors.is_empty());
    let len = vectors[0].len();
    assert!(vectors.iter().all(|v| v.len() == len));
    (0..len)
        .map(|i| weights.iter().zip(vectors).map(|(w, v)| *w * v[i]).sum())
        .collect()
}

/// The verifier challenges of an instance (combined, for an accumulator).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Challenges<F> {
    /// Lookup tuple compression, one challenge per tuple position.
    pub theta: Vec<F>,
    /// Permutation and logup `β` (not Protogalaxy's `β⃗`).
    pub beta: F,
    /// Permutation `γ`.
    pub gamma: F,
    /// Trash challenges, one independent challenge per trash term.
    pub trash: Vec<F>,
    /// Identity batching, one independent challenge per identity.
    pub y: Vec<F>,
}

impl<F: Field> Challenges<F> {
    /// `Σⱼ weightsⱼ·itemsⱼ`, field by field.
    ///
    /// # Panics
    ///
    /// Panics if `items` is empty, if `weights` and `items` differ in length,
    /// or if the items differ in the lengths of `theta`, `trash` or `y`.
    pub(crate) fn linear_combination(items: &[&Self], weights: &[F]) -> Self {
        assert_eq!(weights.len(), items.len());
        let vectors = |field: fn(&Self) -> &[F]| -> Vec<F> {
            let vectors: Vec<&[F]> = items.iter().map(|c| field(c)).collect();
            combine_vectors(weights, &vectors)
        };
        let scalar = |field: fn(&Self) -> F| -> F {
            let values: Vec<F> = items.iter().map(|c| field(c)).collect();
            combine_scalars(weights, &values)
        };
        Challenges {
            theta: vectors(|c| &c.theta),
            beta: scalar(|c| c.beta),
            gamma: scalar(|c| c.gamma),
            trash: vectors(|c| &c.trash),
            y: vectors(|c| &c.y),
        }
    }

    /// Absorbs `θ⃗, β, γ, trash⃗, y⃗`, in this order.
    fn absorb<T: Transcript>(&self, transcript: &mut T) -> Result<(), Error>
    where
        F: Hashable<T::Hash>,
    {
        let scalars = (self.theta.iter())
            .chain([&self.beta, &self.gamma])
            .chain(&self.trash)
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
/// [`read_instance`](super::read_instance); accumulators hold a combined one.
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

    /// `Σⱼ weightsⱼ·itemsⱼ`, field by field (commitments with
    /// [`PolynomialCommitmentScheme::combine_commitments`], public inputs
    /// column by column, entry by entry).
    ///
    /// # Errors
    ///
    /// [`Error::InvalidInstances`] if the items differ in the shape of their
    /// public inputs.
    ///
    /// # Panics
    ///
    /// Panics if `items` is empty or `weights` and `items` differ in length.
    pub(crate) fn linear_combination(items: &[&Self], weights: &[F]) -> Result<Self, Error> {
        assert_eq!(weights.len(), items.len());
        let first = items.first().expect("at least one instance to combine");
        let same_shape = items.iter().all(|item| {
            item.instances.len() == first.instances.len()
                && (item.instances.iter().zip(&first.instances)).all(|(a, b)| a.len() == b.len())
        });
        if !same_shape {
            return Err(Error::InvalidInstances);
        }

        let commitment = |field: fn(&Self) -> &CS::Commitment| -> CS::Commitment {
            let terms: Vec<_> =
                weights.iter().copied().zip(items.iter().map(|i| field(i))).collect();
            CS::combine_commitments(&terms)
        };
        let instances = (0..first.instances.len())
            .map(|column| {
                let vectors: Vec<&[F]> =
                    items.iter().map(|i| i.instances[column].as_slice()).collect();
                combine_vectors(weights, &vectors)
            })
            .collect();
        let challenges: Vec<&Challenges<F>> = items.iter().map(|i| &i.challenges).collect();

        Ok(FoldingInstance {
            phase1_commitment: commitment(|i| &i.phase1_commitment),
            phase2_commitment: commitment(|i| &i.phase2_commitment),
            instances,
            challenges: Challenges::linear_combination(&challenges, weights),
        })
    }
}

/// The running accumulator, verifier side: a combined instance with
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
    /// The combined instance.
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
    /// public inputs (column by column), `θ⃗, β, γ, trash⃗, y⃗`, `β⃗`, `e`.
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
}

#[cfg(test)]
mod tests {
    use midnight_curves::Fq;
    use rand_core::OsRng;

    use super::*;

    fn random_challenges() -> Challenges<Fq> {
        let vec = |len: usize| (0..len).map(|_| Fq::random(OsRng)).collect();
        Challenges {
            theta: vec(2),
            beta: Fq::random(OsRng),
            gamma: Fq::random(OsRng),
            trash: vec(3),
            y: vec(4),
        }
    }

    #[test]
    fn unit_weights_select_an_item() {
        let items = [
            random_challenges(),
            random_challenges(),
            random_challenges(),
        ];
        let refs: Vec<_> = items.iter().collect();
        for (j, item) in items.iter().enumerate() {
            let weights: Vec<Fq> = (0..3).map(|l| Fq::from(u64::from(l == j))).collect();
            assert_eq!(&Challenges::linear_combination(&refs, &weights), item);
        }
    }

    #[test]
    fn two_items_are_an_affine_combination() {
        let (a, b) = (random_challenges(), random_challenges());
        let x = Fq::random(OsRng);
        let folded = Challenges::linear_combination(&[&a, &b], &[Fq::ONE - x, x]);

        let affine = |a: Fq, b: Fq| a + x * (b - a);
        let affine_vec = |a: &[Fq], b: &[Fq]| -> Vec<Fq> {
            a.iter().zip(b).map(|(a, b)| affine(*a, *b)).collect()
        };
        assert_eq!(folded.theta, affine_vec(&a.theta, &b.theta));
        assert_eq!(folded.beta, affine(a.beta, b.beta));
        assert_eq!(folded.gamma, affine(a.gamma, b.gamma));
        assert_eq!(folded.trash, affine_vec(&a.trash, &b.trash));
        assert_eq!(folded.y, affine_vec(&a.y, &b.y));
    }

    #[test]
    #[should_panic]
    fn weights_and_items_must_have_the_same_length() {
        let (a, b) = (random_challenges(), random_challenges());
        Challenges::linear_combination(&[&a, &b], &[Fq::ONE]);
    }

    #[test]
    #[should_panic]
    fn items_must_have_the_same_shape() {
        let (a, mut b) = (random_challenges(), random_challenges());
        b.trash.pop();
        Challenges::linear_combination(&[&a, &b], &[Fq::ONE, Fq::ONE]);
    }
}

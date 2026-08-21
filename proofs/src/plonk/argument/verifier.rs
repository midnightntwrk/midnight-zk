use std::collections::{BTreeMap, BTreeSet};

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{
        Error,
        argument::{self, Evaluation},
    },
    poly::{
        EvaluationDomain, PolynomialLabel, VerifierQuery, commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    commitment: CS::Commitment,
    polynomial_labels: BTreeSet<PolynomialLabel>,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    /// Reads the commitment to the group of the given labels, or `None` if the
    /// group holds no polynomials: the prover commits to nothing in that case,
    /// so there is nothing in the transcript to read.
    ///
    /// TODO: drop this function, and the `Option` it forces on the phase groups
    /// of [`crate::plonk::traces::VerifierTrace`], once every phase group is
    /// guaranteed to hold at least one polynomial. [`Self::read`] then becomes
    /// the only entry point.
    pub(crate) fn read_group<T: Transcript>(
        labels: &[PolynomialLabel],
        transcript: &mut T,
    ) -> Result<Option<Committed<F, CS>>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        if labels.is_empty() {
            return Ok(None);
        }
        Self::read(labels, transcript).map(Some)
    }

    pub(crate) fn read<T: Transcript>(
        labels: &[PolynomialLabel],
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        // A group with no polynomials is not committed to by the prover, so
        // reading one would consume bytes that are not there.
        assert!(
            !labels.is_empty(),
            "cannot read a commitment to no polynomials"
        );

        // The prover commits to the group in the labels' `Ord` order (its
        // polynomials live in a `BTreeMap`), so read them in that order,
        // whatever order the caller listed them in.
        let polynomial_labels = BTreeSet::from_iter(labels.iter().cloned());
        let ordered_labels: Vec<_> = polynomial_labels.iter().cloned().collect();
        Ok(Committed {
            commitment: CS::read_commitment(transcript, &ordered_labels)?,
            polynomial_labels,
        })
    }
}

#[derive(Debug)]
pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) committed: Committed<F, CS>,
    pub(crate) evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(crate) fn evaluate<T: Transcript>(
        self,
        x: F,
        domain: &EvaluationDomain<F>,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let mut evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>> = BTreeMap::new();

        for label in &self.polynomial_labels {
            let eval_points = argument::eval_points(label, x, domain.get_omega());
            let mut evals = Vec::with_capacity(eval_points.len());
            for point in eval_points {
                evals.push(Evaluation {
                    point,
                    eval: transcript.read()?,
                });
            }

            if evals_map.insert(label.clone(), evals).is_some() {
                return Err(Error::DuplicatedLabel);
            }
        }

        Ok(Evaluated {
            committed: self,
            evals_map,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(crate) fn queries(&self) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        self.evals_map.iter().flat_map(|(label, evaluations)| {
            evaluations.iter().map(|evaluation| {
                VerifierQuery::new(
                    evaluation.point,
                    &self.committed.commitment,
                    label.clone(),
                    evaluation.eval,
                )
            })
        })
    }
}

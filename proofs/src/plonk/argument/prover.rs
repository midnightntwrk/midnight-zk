use std::collections::BTreeMap;

use ff::{PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    plonk::{
        AbsorbedVk, ConstraintSystem, Error,
        argument::{self, Evaluation},
    },
    poly::{
        Coeff, EvaluationDomain, Polynomial, PolynomialLabel, PolynomialRepresentation,
        ProverQuery, Rotation, commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::eval_polynomial,
};

/// REVIEW-ONLY: The polynomials are kept in their labels' `Ord` order,
/// `labels[i]` being the label of `polys[i]`, so that the group can lend them
/// out as a slice.
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField, B: PolynomialRepresentation> {
    labels: Vec<PolynomialLabel>,
    polys: Vec<Polynomial<F, B>>,
}

impl<F: PrimeField, B: PolynomialRepresentation> Committed<F, B> {
    fn from_map(polys_map: BTreeMap<PolynomialLabel, Polynomial<F, B>>) -> Self {
        let (labels, polys) = polys_map.into_iter().unzip();
        Committed { labels, polys }
    }

    /// The polynomial the group holds under `label`, if any.
    pub(crate) fn poly(&self, label: &PolynomialLabel) -> Option<&Polynomial<F, B>> {
        self.labels.binary_search(label).ok().map(|i| &self.polys[i])
    }

    /// The polynomials the group holds under `labels`, as a slice in the same
    /// order.
    ///
    /// # Panics
    ///
    /// Panics if `labels` is not a run of consecutive labels of the group, in
    /// their `Ord` order.
    pub(crate) fn polys_of(&self, labels: &[PolynomialLabel]) -> &[Polynomial<F, B>] {
        let start = match labels.first() {
            Some(first) => self.labels.binary_search(first).unwrap_or(self.labels.len()),
            None => 0,
        };
        let end = start + labels.len();
        assert!(
            end <= self.labels.len() && self.labels[start..end] == *labels,
            "the labels are not a run of consecutive labels of the group"
        );
        &self.polys[start..end]
    }

    /// The group's labeled polynomials, in parallel.
    pub(crate) fn par_polys(
        &self,
    ) -> impl ParallelIterator<Item = (&PolynomialLabel, &Polynomial<F, B>)> {
        self.labels.par_iter().zip(self.polys.par_iter())
    }
}

impl<F: WithSmallOrderMulGroup<3>, B: PolynomialRepresentation> Committed<F, B> {
    pub fn into_coeff(self, domain: &EvaluationDomain<F>) -> Committed<F, Coeff> {
        Committed {
            labels: self.labels,
            polys: self.polys.into_par_iter().map(|p| B::self_to_coeff(domain, p)).collect(),
        }
    }
}

impl<F: PrimeField, B: PolynomialRepresentation> Committed<F, B> {
    pub fn commit<CS, T>(
        params: &CS::Parameters,
        polys_map: BTreeMap<PolynomialLabel, Polynomial<F, B>>,
        transcript: &mut T,
    ) -> Result<Self, Error>
    where
        CS: PolynomialCommitmentScheme<F>,
        CS::Commitment: Hashable<T::Hash>,
        T: Transcript,
    {
        let group = Self::from_map(polys_map);
        let commitment = CS::commit_many(
            params,
            &group.polys.iter().collect::<Vec<_>>(),
            &group.labels,
        );

        CS::write_commitment(transcript, &commitment)?;

        Ok(group)
    }
}

/// A group whose polynomials are committed to in the verifying key rather than
/// in the proof. It takes part in a proof, as a [`Committed`], only once that
/// verifying key has been absorbed into the transcript; see
/// [`Self::committed`].
#[derive(Debug)]
pub(crate) struct KeyGroup<F: PrimeField> {
    committed: Committed<F, Coeff>,
    /// The `transcript_repr` of the verifying key holding the group's
    /// commitment.
    vk_repr: F,
}

impl<F: PrimeField> KeyGroup<F> {
    /// The group of `polys_map`, whose commitment is held by the verifying key
    /// of `transcript_repr` `vk_repr`.
    pub(crate) fn new(
        polys_map: BTreeMap<PolynomialLabel, Polynomial<F, Coeff>>,
        vk_repr: F,
    ) -> Self {
        KeyGroup {
            committed: Committed::from_map(polys_map),
            vk_repr,
        }
    }

    /// The group as a [`Committed`], given the witness that the verifying key
    /// holding its commitment has been absorbed.
    ///
    /// # Panics
    ///
    /// Panics if `vk` is the witness of a different verifying key.
    pub(crate) fn committed<CS: PolynomialCommitmentScheme<F>>(
        &self,
        vk: &AbsorbedVk<'_, F, CS>,
    ) -> &Committed<F, Coeff> {
        assert!(
            vk.transcript_repr() == self.vk_repr,
            "the absorbed verifying key does not hold the commitment to this group"
        );
        &self.committed
    }
}

pub(crate) struct Evaluated<'a, F: PrimeField> {
    committed: &'a Committed<F, Coeff>,
    pub(crate) evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
}

impl<F: PrimeField> Committed<F, Coeff> {
    /// Evaluates every polynomial of the group at each of its evaluation
    /// points and writes the evaluations to the proof, in the labels' `Ord`
    /// order.
    ///
    /// Borrows the group rather than consuming it.
    pub(crate) fn evaluate<T>(
        &self,
        cs: &ConstraintSystem<F>,
        x_rotations: &BTreeMap<Rotation, F>,
        transcript: &mut T,
    ) -> Result<Evaluated<'_, F>, Error>
    where
        F: Hashable<T::Hash> + WithSmallOrderMulGroup<3>,
        T: Transcript,
    {
        let evaluate = |poly: &Polynomial<F, Coeff>, x: F| -> Evaluation<F> {
            Evaluation {
                point: x,
                eval: eval_polynomial(poly, x),
            }
        };

        let evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>> = self
            .labels
            .iter()
            .zip(self.polys.iter())
            .map(|(label, poly)| {
                let eval_points = argument::eval_points(cs, label, x_rotations);
                (
                    label.clone(),
                    eval_points.into_iter().map(|point| evaluate(poly, point)).collect(),
                )
            })
            .collect();

        for evals in evals_map.values() {
            for evaluation in evals.iter() {
                transcript.write(&evaluation.eval)?;
            }
        }

        Ok(Evaluated {
            committed: self,
            evals_map,
        })
    }
}

impl<F: PrimeField> Evaluated<'_, F> {
    pub(crate) fn open(&self) -> impl Iterator<Item = ProverQuery<'_, F>> + Clone {
        self.evals_map.iter().flat_map(|(label, evaluations)| {
            evaluations.iter().map(|evaluation| {
                ProverQuery::new(
                    evaluation.point,
                    self.committed.poly(label).unwrap(),
                    label.clone(),
                )
            })
        })
    }
}

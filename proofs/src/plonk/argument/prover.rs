use std::collections::BTreeMap;

use ff::{PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::{
    plonk::{
        AbsorbedVk, ConstraintSystem, Error,
        argument::{self, Evaluation},
    },
    poly::{
        Coeff, EvaluationDomain, Polynomial, PolynomialLabel, PolynomialRepresentation,
        ProverQuery, commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::eval_polynomial,
};

#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField, B: PolynomialRepresentation> {
    polys_map: BTreeMap<PolynomialLabel, Polynomial<F, B>>,
}

impl<F: PrimeField, B: PolynomialRepresentation> Committed<F, B> {
    /// The polynomial the group holds under `label`, if any.
    pub(crate) fn poly(&self, label: &PolynomialLabel) -> Option<&Polynomial<F, B>> {
        self.polys_map.get(label)
    }

    /// The group's labeled polynomials, in parallel.
    pub(crate) fn par_polys(
        &self,
    ) -> impl ParallelIterator<Item = (&PolynomialLabel, &Polynomial<F, B>)> {
        self.polys_map.par_iter()
    }
}

impl<F: WithSmallOrderMulGroup<3>, B: PolynomialRepresentation> Committed<F, B> {
    pub fn into_coeff(self, domain: &EvaluationDomain<F>) -> Committed<F, Coeff> {
        Committed {
            polys_map: self
                .polys_map
                .into_par_iter()
                .map(|(label, p)| (label, B::self_to_coeff(domain, p)))
                .collect::<BTreeMap<_, _>>(),
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
        let commitment = CS::commit_many(
            params,
            &polys_map.values().collect::<Vec<_>>(),
            &polys_map.keys().cloned().collect::<Vec<_>>(),
        );

        CS::write_commitment(transcript, &commitment)?;

        Ok(Self { polys_map })
    }
}

/// A group whose polynomials are committed to in the verifying key rather than
/// in the proof. It takes part in a proof, as a [`Committed`], only once a
/// verifying key has been absorbed into the transcript; see
/// [`Self::committed`].
///
/// # Caveat
///
/// The [`AbsorbedVk`] witness shows that *a* verifying key was absorbed, not
/// that it is the key holding this group's commitment. Pairing the two is left
/// to the caller.
#[derive(Debug)]
pub(crate) struct KeyGroup<F: PrimeField>(Committed<F, Coeff>);

impl<F: PrimeField> KeyGroup<F> {
    pub(crate) fn new(polys_map: BTreeMap<PolynomialLabel, Polynomial<F, Coeff>>) -> Self {
        KeyGroup(Committed { polys_map })
    }

    /// The group as a [`Committed`], given the witness that its verifying key
    /// has been absorbed (see the caveat on [`KeyGroup`]).
    pub(crate) fn committed<CS: PolynomialCommitmentScheme<F>>(
        &self,
        _vk: &AbsorbedVk<'_, F, CS>,
    ) -> &Committed<F, Coeff> {
        &self.0
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
        x: F,
        x_next: F,
        x_last: F,
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
            .polys_map
            .iter()
            .map(|(label, poly)| {
                let eval_points = argument::eval_points(cs, label, x, x_next, x_last);
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
                    self.committed.polys_map.get(label).unwrap(),
                    label.clone(),
                )
            })
        })
    }
}

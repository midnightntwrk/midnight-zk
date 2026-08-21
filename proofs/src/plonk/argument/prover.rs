use std::collections::BTreeMap;

use ff::{PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{
    plonk::{
        Error,
        argument::{self, Evaluation},
    },
    poly::{
        Coeff, EvaluationDomain, Polynomial, PolynomialLabel, PolynomialRepresentation,
        ProverQuery, commitment::PolynomialCommitmentScheme,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::eval_polynomial,
};

#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField, B: PolynomialRepresentation> {
    pub(crate) polys_map: BTreeMap<PolynomialLabel, Polynomial<F, B>>,
}

impl<F: WithSmallOrderMulGroup<3>, B: PolynomialRepresentation> Committed<F, B> {
    pub fn into_coeff(self, domain: &EvaluationDomain<F>) -> Committed<F, Coeff> {
        Committed {
            polys_map: BTreeMap::from_iter(
                self.polys_map
                    .into_par_iter()
                    .map(|(label, p)| (label, B::self_to_coeff(domain, p)))
                    .collect::<Vec<_>>()
                    .into_iter(),
            ),
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
        // Be general and protect ourselves against a group with no enabled
        // arguments, which has nothing to commit to.
        if polys_map.is_empty() {
            return Ok(Self { polys_map });
        }

        let commitment = CS::commit_many(
            params,
            &polys_map.values().collect::<Vec<_>>(),
            &polys_map.keys().cloned().collect::<Vec<_>>(),
        );

        CS::write_commitment(transcript, &commitment)?;

        Ok(Self { polys_map })
    }
}

pub(crate) struct Evaluated<F: PrimeField> {
    committed: Committed<F, Coeff>,
    pub(crate) evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
}

impl<F: PrimeField> Committed<F, Coeff> {
    pub(crate) fn evaluate<T>(
        self,
        domain: &EvaluationDomain<F>,
        x: F,
        transcript: &mut T,
    ) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash> + WithSmallOrderMulGroup<3>,
        T: Transcript,
    {
        let omega = domain.get_omega();

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
                let eval_points = argument::eval_points(label, x, omega);
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

impl<F: PrimeField> Evaluated<F> {
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

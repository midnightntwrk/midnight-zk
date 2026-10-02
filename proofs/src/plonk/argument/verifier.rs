use std::collections::{BTreeMap, BTreeSet};

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{
        AbsorbedVk, ConstraintSystem, Error,
        argument::{self, Evaluation},
    },
    poly::{PolynomialLabel, Rotation, VerifierQuery, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    commitment: CS::Commitment,
    polynomial_labels: BTreeSet<PolynomialLabel>,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    /// Builds the fixed group of the absorbed verifying key, which binds it to
    /// the transcript as reading a commitment from the proof does.
    pub(crate) fn from_key(vk: &AbsorbedVk<'_, F, CS>) -> Committed<F, CS> {
        Committed {
            commitment: vk.fixed_group_commitment().clone(),
            polynomial_labels: BTreeSet::from_iter(vk.fixed_group_labels()),
        }
    }

    pub(crate) fn read<T: Transcript>(
        labels: &[PolynomialLabel],
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        Ok(Committed {
            commitment: CS::read_commitment(transcript, labels)?,
            polynomial_labels: BTreeSet::from_iter(labels.iter().cloned()),
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
        cs: &ConstraintSystem<F>,
        x_rotations: &BTreeMap<Rotation, F>,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let mut evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>> = BTreeMap::new();

        for label in &self.polynomial_labels {
            let eval_points = argument::eval_points(cs, label, x_rotations);
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

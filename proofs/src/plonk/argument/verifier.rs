use std::collections::BTreeMap;

use ff::PrimeField;

use crate::{
    plonk::{
        AbsorbedVk, ConstraintSystem, Error,
        argument::{self, Evaluation},
    },
    poly::{PolynomialLabel, Rotation, VerifierQuery, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    commitment: PCS::Commitment,
    polynomial_labels: Vec<PolynomialLabel>,
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Committed<F, PCS> {
    /// Builds the fixed group of the absorbed verifying key, which binds it to
    /// the transcript as reading a commitment from the proof does.
    pub(crate) fn from_key(vk: &AbsorbedVk<'_, F, PCS>) -> Committed<F, PCS> {
        Committed {
            commitment: vk.phase0_commitment().clone(),
            polynomial_labels: vk.phase0_labels(),
        }
    }

    pub(crate) fn read<T>(
        labels: &[PolynomialLabel],
        transcript: &mut T,
    ) -> Result<Committed<F, PCS>, Error>
    where
        PCS::Commitment: Hashable<T::Hash>,
        T: Transcript,
    {
        Ok(Committed {
            commitment: PCS::read_commitment(transcript, labels)?,
            polynomial_labels: labels.to_vec(),
        })
    }
}

#[derive(Debug)]
pub struct Evaluated<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) committed: Committed<F, PCS>,
    pub(crate) evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Committed<F, PCS> {
    pub(crate) fn evaluate<T>(
        self,
        cs: &ConstraintSystem<F>,
        x_rotations: &BTreeMap<Rotation, F>,
        transcript: &mut T,
    ) -> Result<Evaluated<F, PCS>, Error>
    where
        F: Hashable<T::Hash>,
        T: Transcript,
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

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Evaluated<F, PCS> {
    /// Adds the evaluation `eval` at `point` of the group's polynomial `label`,
    /// one derived rather than read from the proof.
    pub(crate) fn insert(&mut self, label: PolynomialLabel, point: F, eval: F) {
        self.evals_map.insert(label, vec![Evaluation { point, eval }]);
    }

    pub(crate) fn queries(&self) -> impl Iterator<Item = VerifierQuery<'_, F, PCS>> + Clone {
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

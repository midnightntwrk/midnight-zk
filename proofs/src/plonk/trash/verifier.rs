use ff::{PrimeField, WithSmallOrderMulGroup};

use super::Argument;
use crate::{
    plonk::{trash, Error},
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    trash_commitment: CS::Commitment,
}

#[derive(Debug)]
pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) committed: Committed<F, CS>,
    pub(crate) evaluated: trash::Evaluated<F>,
}

impl<F: PrimeField> Argument<F> {
    pub(crate) fn read_committed<CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        &self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let trash_commitment = transcript.read()?;
        Ok(Committed { trash_commitment })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let trash_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            evaluated: trash::Evaluated { trash_eval },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(crate) fn queries(&self, x: F) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        vec![VerifierQuery::new(
            x,
            CommitmentLabel::NoLabel,
            &self.committed.trash_commitment,
            self.evaluated.trash_eval,
        )]
        .into_iter()
    }
}

use ff::{PrimeField, WithSmallOrderMulGroup};

use super::Argument;
use crate::{
    plonk::{trash, Error},
    poly::{commitment::PolynomialCommitmentScheme, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    trash_commitment: CS::Commitment,
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
    ) -> Result<(Committed<F, CS>, trash::Evaluated<F>), Error>
    where
        F: Hashable<T::Hash>,
    {
        let trash_eval = transcript.read()?;

        Ok((self, trash::Evaluated { trash_eval }))
    }
}

pub(crate) fn queries<'a, F, CS>(
    eval: &'a trash::Evaluated<F>,
    com: &'a Committed<F, CS>,
    x: F,
) -> impl Iterator<Item = VerifierQuery<'a, F, CS>> + Clone
where
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
{
    vec![VerifierQuery::new(
        x,
        &com.trash_commitment,
        eval.trash_eval,
    )]
    .into_iter()
}

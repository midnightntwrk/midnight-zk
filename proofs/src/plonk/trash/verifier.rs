use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    pcs::PolynomialCommitmentScheme,
    plonk::{Error, trash},
    poly::{PolynomialLabel, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    argument_index: usize,
    trash_commitment: CS::Commitment,
}

#[derive(Debug)]
pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) committed: Committed<F, CS>,
    pub(crate) evaluated: trash::Evaluated<F>,
}

/// Reads the batched commitment to the compressed polynomial of every trash
/// argument in one transcript entry. Each argument holds a clone of the shared
/// commitment and routes its query via its own label. Mirrors the prover's
/// `commit_trashcans`.
pub(in crate::plonk) fn read_trashcans<F, CS, T>(
    num_args: usize,
    transcript: &mut T,
) -> Result<Vec<Committed<F, CS>>, Error>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    if num_args == 0 {
        return Ok(Vec::new());
    }
    let labels: Vec<_> = (0..num_args).map(PolynomialLabel::Trash).collect();
    let shared = CS::read_commitment(transcript, &labels)?;
    Ok((0..num_args)
        .map(|argument_index| Committed {
            argument_index,
            trash_commitment: shared.clone(),
        })
        .collect())
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
            &self.committed.trash_commitment,
            PolynomialLabel::Trash(self.committed.argument_index),
            self.evaluated.trash_eval,
        )]
        .into_iter()
    }
}

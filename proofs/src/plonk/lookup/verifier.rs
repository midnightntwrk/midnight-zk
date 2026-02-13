use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};

use super::Argument;
use crate::{
    plonk::{lookup, Error, VerifyingKey},
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, Rotation, VerifierQuery},
    transcript::{Hashable, Transcript},
};

#[derive(Debug)]
pub struct PermutationCommitments<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permuted_input_commitment: CS::Commitment,
    permuted_table_commitment: CS::Commitment,
}

#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permuted: PermutationCommitments<F, CS>,
    product_commitment: CS::Commitment,
}

#[derive(Debug)]
pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub(crate) committed: Committed<F, CS>,
    pub(crate) evaluated: lookup::Evaluated<F>,
}

impl<F: PrimeField> Argument<F> {
    pub(in crate::plonk) fn read_permuted_commitments<
        CS: PolynomialCommitmentScheme<F>,
        T: Transcript,
    >(
        &self,
        transcript: &mut T,
    ) -> Result<PermutationCommitments<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let permuted_input_commitment = transcript.read()?;
        let permuted_table_commitment = transcript.read()?;

        Ok(PermutationCommitments {
            permuted_input_commitment,
            permuted_table_commitment,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PermutationCommitments<F, CS> {
    pub(in crate::plonk) fn read_product_commitment<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let product_commitment = transcript.read()?;

        Ok(Committed {
            permuted: self,
            product_commitment,
        })
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
        let product_eval = transcript.read()?;
        let product_next_eval = transcript.read()?;
        let permuted_input_eval = transcript.read()?;
        let permuted_input_inv_eval = transcript.read()?;
        let permuted_table_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            evaluated: lookup::Evaluated {
                product_eval,
                product_next_eval,
                permuted_input_eval,
                permuted_input_inv_eval,
                permuted_table_eval,
            },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        let x_inv = vk.domain.rotate_omega(x, Rotation::prev());
        let x_next = vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            // Open lookup product commitment at x
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.product_commitment,
                self.evaluated.product_eval,
            )))
            // Open lookup input commitments at x
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.permuted.permuted_input_commitment,
                self.evaluated.permuted_input_eval,
            )))
            // Open lookup table commitments at x
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.permuted.permuted_table_commitment,
                self.evaluated.permuted_table_eval,
            )))
            // Open lookup input commitments at \omega^{-1} x
            .chain(Some(VerifierQuery::new(
                x_inv,
                CommitmentLabel::NoLabel,
                &self.committed.permuted.permuted_input_commitment,
                self.evaluated.permuted_input_inv_eval,
            )))
            // Open lookup product commitment at \omega x
            .chain(Some(VerifierQuery::new(
                x_next,
                CommitmentLabel::NoLabel,
                &self.committed.product_commitment,
                self.evaluated.product_next_eval,
            )))
    }
}

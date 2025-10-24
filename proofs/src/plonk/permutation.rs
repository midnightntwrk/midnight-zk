//! Implementation of permutation argument.

use super::circuit::{Any, Column};
use crate::{
    plonk::{self, permutation::verifier::CommonEvaluated},
    poly::{Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation},
    utils::{
        helpers::{polynomial_slice_byte_length, read_polynomial_vec, write_polynomial_slice},
        SerdeFormat,
    },
};

pub(crate) mod keygen;
pub(crate) mod prover;
pub(crate) mod verifier;

use std::{io, iter};

use ff::{PrimeField, WithSmallOrderMulGroup};
use halo2curves::serde::SerdeObject;
pub use keygen::Assembly;

use crate::{
    plonk::permutation::keygen::compute_polys_and_cosets,
    poly::{commitment::PolynomialCommitmentScheme, EvaluationDomain},
    utils::helpers::{byte_length, ProcessedSerdeObject},
};

/// A permutation argument.
#[derive(Debug, Clone)]
pub struct Argument {
    /// A sequence of columns involved in the argument.
    pub columns: Vec<Column<Any>>,
}

impl Argument {
    pub(crate) fn new() -> Self {
        Argument { columns: vec![] }
    }

    /// Returns the minimum circuit degree required by the permutation argument.
    /// The argument may use larger degree gates depending on the actual
    /// circuit's degree and how many columns are involved in the permutation.
    pub(crate) fn required_degree(&self) -> usize {
        // degree 2:
        // l_0(X) * (1 - z(X)) = 0
        //
        // We will fit as many polynomials p_i(X) as possible
        // into the required degree of the circuit, so the
        // following will not affect the required degree of
        // this middleware.
        //
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
        // - z(X) \prod (p(X) + \delta^i \beta X + \gamma)
        // )
        //
        // On the first sets of columns, except the first
        // set, we will do
        //
        // l_0(X) * (z(X) - z'(\omega^(last) X)) = 0
        //
        // where z'(X) is the permutation for the previous set
        // of columns.
        //
        // On the final set of columns, we will do
        //
        // degree 3:
        // l_last(X) * (z'(X)^2 - z'(X)) = 0
        //
        // which will allow the last value to be zero to
        // ensure the argument is perfectly complete.

        // There are constraints of degree 3 regardless of the
        // number of columns involved.
        3
    }

    pub(crate) fn add_column(&mut self, column: Column<Any>) {
        if !self.columns.contains(&column) {
            self.columns.push(column);
        }
    }

    /// Returns columns that participate on the permutation argument.
    pub fn get_columns(&self) -> Vec<Column<Any>> {
        self.columns.clone()
    }
}

/// The verifying key for a single permutation argument.
#[derive(Clone, Debug)]
pub struct VerifyingKey<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    commitments: Vec<CS::Commitment>,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    /// Returns the (permutation argument) commitments of the verifying key.
    pub fn commitments(&self) -> &Vec<CS::Commitment> {
        &self.commitments
    }

    pub(crate) fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        CS::Commitment: ProcessedSerdeObject,
    {
        for commitment in &self.commitments {
            commitment.write(writer, format)?;
        }
        Ok(())
    }

    pub(crate) fn read<R: io::Read>(
        reader: &mut R,
        argument: &Argument,
        format: SerdeFormat,
    ) -> io::Result<Self>
    where
        CS::Commitment: ProcessedSerdeObject,
    {
        let commitments = (0..argument.columns.len())
            .map(|_| CS::Commitment::read(reader, format))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(VerifyingKey { commitments })
    }

    pub(crate) fn bytes_length(&self, format: SerdeFormat) -> usize
    where
        CS::Commitment: ProcessedSerdeObject,
    {
        self.commitments.len() * byte_length::<CS::Commitment>(format)
    }
}

/// The proving key for a single permutation argument.
#[derive(Clone, Debug)]
pub(crate) struct ProvingKey<F: PrimeField> {
    pub(crate) permutations: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) polys: Vec<Polynomial<F, Coeff>>,
    pub(crate) cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
}

impl<F: WithSmallOrderMulGroup<3> + SerdeObject> ProvingKey<F> {
    /// Reads proving key for a single permutation argument from buffer using
    /// `Polynomial::read`.
    pub(super) fn read<R: io::Read>(
        reader: &mut R,
        format: SerdeFormat,
        domain: &EvaluationDomain<F>,
        p: &Argument,
    ) -> io::Result<Self> {
        let permutations = read_polynomial_vec(reader, format)?;
        let (polys, cosets) = compute_polys_and_cosets::<F>(domain, p, &permutations);
        Ok(ProvingKey {
            permutations,
            polys,
            cosets,
        })
    }

    /// Writes proving key for a single permutation argument to buffer using
    /// `Polynomial::write`.
    pub(super) fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        write_polynomial_slice(&self.permutations, writer)?;
        Ok(())
    }
}

impl<F: PrimeField> ProvingKey<F> {
    /// Gets the total number of bytes in the serialization of `self`
    pub(super) fn bytes_length(&self) -> usize {
        polynomial_slice_byte_length(&self.permutations)
            + polynomial_slice_byte_length(&self.polys)
            + polynomial_slice_byte_length(&self.cosets)
    }
}
#[derive(Debug)]
pub(crate) struct EvaluatedSet<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    pub permutation_product_eval: F,
    pub permutation_product_next_eval: F,
    pub permutation_product_last_eval: Option<F>,
    _marker: std::marker::PhantomData<CS>,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::plonk) fn expressions<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    sets: &'a [EvaluatedSet<F, CS>],
    vk: &'a plonk::VerifyingKey<F, CS>,
    p: &'a Argument,
    common: &'a CommonEvaluated<F>,
    advice_evals: &'a [F],
    fixed_evals: &'a [F],
    instance_evals: &'a [F],
    l_0: F,
    l_last: F,
    l_blind: F,
    beta: F,
    gamma: F,
    x: F,
) -> impl Iterator<Item = F> + 'a {
    let chunk_len = vk.cs_degree - 2;
    iter::empty()
        // Enforce only for the first set.
        // l_0(X) * (1 - z_0(X)) = 0
        .chain(
            sets.first()
                .map(|first_set| l_0 * &(F::ONE - &first_set.permutation_product_eval)),
        )
        // Enforce only for the last set.
        // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
        .chain(sets.last().map(|last_set| {
            (last_set.permutation_product_eval.square() - &last_set.permutation_product_eval)
                * &l_last
        }))
        // Except for the first set, enforce.
        // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
        .chain(
            sets.iter()
                .skip(1)
                .zip(sets.iter())
                .map(|(set, last_set)| {
                    (
                        set.permutation_product_eval,
                        last_set.permutation_product_last_eval.unwrap(),
                    )
                })
                .map(move |(set, prev_last)| (set - &prev_last) * &l_0),
        )
        // And for all the sets we enforce:
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
        // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
        // )
        .chain(
            sets.iter()
                .zip(p.columns.chunks(chunk_len))
                .zip(common.permutation_evals.chunks(chunk_len))
                .enumerate()
                .map(move |(chunk_index, ((set, columns), permutation_evals))| {
                    let mut left = set.permutation_product_next_eval;
                    for (eval, permutation_eval) in columns
                        .iter()
                        .map(|&column| match column.column_type() {
                            Any::Advice(_) => {
                                advice_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Fixed => {
                                fixed_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Instance => {
                                instance_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                        })
                        .zip(permutation_evals.iter())
                    {
                        left *= &(eval + &(beta * permutation_eval) + &gamma);
                    }

                    let mut right = set.permutation_product_eval;
                    let mut current_delta = (beta * &x)
                        * &(<F as PrimeField>::DELTA
                            .pow_vartime([(chunk_index * chunk_len) as u64]));
                    for eval in columns.iter().map(|&column| match column.column_type() {
                        Any::Advice(_) => {
                            advice_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                        }
                        Any::Fixed => {
                            fixed_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                        }
                        Any::Instance => {
                            instance_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                        }
                    }) {
                        right *= &(eval + &current_delta + &gamma);
                        current_delta *= &F::DELTA;
                    }

                    (left - &right) * (F::ONE - &(l_last + &l_blind))
                }),
        )
}

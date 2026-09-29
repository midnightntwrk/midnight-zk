//! Implementation of permutation argument.

use super::circuit::{Any, Column};
use crate::poly::{ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation};

pub(crate) mod keygen;
pub(crate) mod prover;

use std::collections::BTreeMap;

use ff::PrimeField;
pub use keygen::Assembly;

use crate::{
    plonk::{self, argument},
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
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

    /// The labels of the permutation polynomials, one per column of the
    /// argument. They belong to the phase-0 group, whose polynomials are
    /// committed to in the verifying key, not in the proof.
    pub fn polynomial_labels(&self) -> Vec<PolynomialLabel> {
        (0..self.columns.len()).map(PolynomialLabel::PermutationFixed).collect()
    }

    /// The number of accumulator polynomials: the columns are split into chunks
    /// of `degree - 2`, each with an accumulator of its own.
    pub fn num_sets(&self, degree: usize) -> usize {
        self.columns.len().div_ceil(degree - 2)
    }

    /// The labels of the permutation accumulators. They are committed to as
    /// part of the phase-2 group.
    pub fn accumulator_labels(&self, degree: usize) -> Vec<PolynomialLabel> {
        (0..self.num_sets(degree))
            .map(PolynomialLabel::PermutationAccumulator)
            .collect()
    }
}

/// The permutation polynomials in the two bases the prover reads them in.
///
/// The polynomials themselves belong to the proving key's phase-0 group, which
/// holds them in coefficient form; these are derived from it and cached beside
/// it by [`crate::plonk::build_fixed_perm_polys`].
#[derive(Debug)]
pub(crate) struct Sigmas<F: PrimeField> {
    /// Evaluations over the domain, read row-wise when computing the
    /// accumulators. This is the form the proving key serializes.
    pub(crate) values: Vec<Polynomial<F, LagrangeCoeff>>,
    /// Evaluations over the extended domain, read when evaluating the
    /// numerator of the quotient polynomial.
    pub(crate) cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
}

/// The identities of the permutation argument, evaluated at `x`.
///
/// The permutation polynomials are opened as the phase-0 group and the
/// accumulators `z_i` as part of the phase-2 group, so both sets of evaluations
/// are looked up by label. `z_i` is opened at `x` and `omega * x`, and, for
/// every set but the last, at `omega^last * x` as well; see
/// [`eval_points`](crate::plonk::argument::eval_points).
#[allow(clippy::too_many_arguments)]
pub(in crate::plonk) fn expressions<F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    vk: &plonk::VerifyingKey<F, CS>,
    p: &Argument,
    fixed_perm_evals: &BTreeMap<PolynomialLabel, Vec<argument::Evaluation<F>>>,
    phase2_evals: &BTreeMap<PolynomialLabel, Vec<argument::Evaluation<F>>>,
    advice_evals: &[F],
    fixed_evals: &[F],
    instance_evals: &[F],
    l_0: F,
    l_last: F,
    l_blind: F,
    beta: F,
    gamma: F,
    x: F,
) -> impl Iterator<Item = F> {
    let chunk_len = vk.cs_degree - 2;
    let num_sets = p.num_sets(vk.cs_degree);

    if num_sets == 0 {
        return vec![].into_iter();
    }

    let permutation_evals: Vec<F> = (0..p.columns.len())
        .map(|i| fixed_perm_evals[&PolynomialLabel::PermutationFixed(i)][0].eval())
        .collect();

    // Per set: z_i(x), z_i(omega x) and, for every set but the last,
    // z_i(omega^last x).
    let z = |i: usize| &phase2_evals[&PolynomialLabel::PermutationAccumulator(i)];
    let z_eval = |i: usize| z(i)[0].eval();
    let z_next_eval = |i: usize| z(i)[1].eval();
    let z_last_eval = |i: usize| z(i)[2].eval();

    let column_eval = |column: &Column<Any>| match column.column_type() {
        Any::Advice => advice_evals[vk.cs.get_any_query_index(*column, Rotation::cur())],
        Any::Fixed => fixed_evals[vk.cs.get_any_query_index(*column, Rotation::cur())],
        Any::Instance => instance_evals[vk.cs.get_any_query_index(*column, Rotation::cur())],
    };

    let mut identities = Vec::new();

    // Enforce only for the first set.
    // l_0(X) * (1 - z_0(X)) = 0
    identities.push(l_0 * (F::ONE - z_eval(0)));

    // Enforce only for the last set.
    // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
    let last = z_eval(num_sets - 1);
    identities.push((last.square() - last) * l_last);

    // Except for the first set, enforce.
    // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
    for i in 1..num_sets {
        identities.push((z_eval(i) - z_last_eval(i - 1)) * l_0);
    }

    // And for all the sets we enforce:
    // (1 - (l_last(X) + l_blind(X))) * (
    //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
    // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
    // )
    for (chunk_index, (columns, permutation_evals)) in
        p.columns.chunks(chunk_len).zip(permutation_evals.chunks(chunk_len)).enumerate()
    {
        let mut left = z_next_eval(chunk_index);
        for (eval, permutation_eval) in
            columns.iter().map(column_eval).zip(permutation_evals.iter())
        {
            left *= &(eval + &(beta * permutation_eval) + &gamma);
        }

        let mut right = z_eval(chunk_index);
        let mut current_delta = (beta * &x)
            * &(<F as PrimeField>::DELTA.pow_vartime([(chunk_index * chunk_len) as u64]));
        for eval in columns.iter().map(column_eval) {
            right *= &(eval + &current_delta + &gamma);
            current_delta *= &F::DELTA;
        }

        identities.push((left - &right) * (F::ONE - &(l_last + &l_blind)));
    }

    identities.into_iter()
}

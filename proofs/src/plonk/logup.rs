// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # LogUp Lookup Argument
//!
//! This module implements the [LogUp (Logarithmic Derivative) lookup argument](https://eprint.iacr.org/2022/1530),
//! adapted for univariate polynomials in the PLONK arithmetization. LogUp
//! provides an efficient way to prove that a set of values is contained
//! within a predefined table.
//!
//! The original LogUp protocol operates over multilinear polynomials and uses
//! the sum-check protocol. Our implementation adapts this to the univariate
//! setting used in PLONK, replacing sum-check with a running sum accumulator
//! approach.
//!
//! ## The Core Idea
//!
//! Given lookup values `f₁, ..., fₖ` and a table `T = {t₁, ..., tₙ}`, the
//! logarithmic derivative relation Σⱼ 1/(fⱼ + β) = Σᵢ mᵢ/(tᵢ + β)
//! characterizes table membership as follows:
//!
//! Completeness:
//! If fⱼ ∈ T for every j, then there exists `{mᵢ}ᵢ` such that Σⱼ 1/(fⱼ + β) =
//! Σᵢ mᵢ/(tᵢ + β), for all β.
//! Here, `mᵢ` is the multiplicity of `tᵢ` (how many times it appears among the
//! `fⱼ`s).
//!
//! Soundness:
//! If fⱼ∉T for some j, then for every `{mᵢ}ᵢ` it holds Σⱼ 1/(fⱼ + β) ≠ Σᵢ
//! mᵢ/(tᵢ + β) w.o.p over the choice of β.
//!
//! This result follows from partial fraction decomposition.
//!
//! Note: When duplicate values exist in the table, multiplicities are
//! normalized: if value `v` is looked up `k` times and appears `t` times in the
//! table, multiplicities are normalized with `k/t`.
//!
//! ## Running Sum Formulation
//!
//! Rather than checking the sum equality directly (which would require
//! sum-check in the multilinear setting), we encode the constraint as a running
//! sum over the evaluation domain. We introduce:
//!
//! - **Helper polynomial** `h(X)`: Encodes `Σⱼ 1/(fⱼ(X) + β)` at each row
//! - **Multiplicities** `m(X)`: Counts how many times each table entry is used
//! - **Accumulator** `Z(X)`: Running sum that accumulates the log-derivative
//!   differences
//!
//! The accumulator satisfies:
//! ```text
//! Z(ω·X) - Z(X) = h(X) - m(X)/(t(X) + β)
//! ```
//!
//! With boundary condition `Z(1) = 0`. If the lookup is valid, the accumulator
//! returns to zero after a full cycle, which we verify by checking `Z(ωⁿ) = 0`.
//!
//! The running sum is enforced in the constraint system via the following
//! identity:
//! ```text
//! Z(ω·X)·(t(X) + β) = (Z(X) + h(X))·(t(X) + β) - m(X)
//! ```
//!
//! ## Lookup Width vs Parallel Lookups
//!
//! The LogUp argument handles two orthogonal dimensions:
//!
//! - **Lookup width**: The width of the lookup table we are looking up. For
//!   example, checking `(a, b, c) ∈ (t_1, t_2, t_3)` has width 3. These columns
//!   are compressed via θ-batching: `compressed = a + θ·b + θ²·c`, reducing a
//!   width-w lookup to a single field element.
//!
//! - **Parallel lookups**: The number of independent lookups per row. For
//!   instance, if each row performs 8 range checks against the same table,
//!   that's 8 parallel lookups. Each contributes a term `1/(fⱼ(X) + β)` to the
//!   helper polynomial.
//!
//! The helper polynomial aggregates all parallel lookups at each row:
//! ```text
//! h(X) = Σⱼ 1/(fⱼ(X) + β)
//! ```
//!
//! The constraint that enforces correctness of `h(X)` is:
//! ```text
//! h(X) · ∏ⱼ(fⱼ(X) + β) = Σⱼ ∏_{k≠j}(fₖ(X) + β)
//! ```
//!
//! This has degree `1 + lookup_degree × num_parallel_lookups`, which limits how
//! many parallel lookups can be batched into a single argument before exceeding
//! the constraint system's degree bound.

use std::fmt::{self, Debug};

use ff::{Field, PrimeField};

use super::circuit::Expression;

pub(crate) mod prover;
pub(crate) mod verifier;

/// A `BatchedArgument` collects all lookups that query the same table. For
/// multi-column lookups (e.g., checking `(a, b) ∈ (t_1, t_2)`), columns are
/// compressed using a random challenge `θ` into a single value.
///
/// # Layout
///
/// After construction, `input_expressions` is organized as
/// `[parallel_lookups][lookup_width]`:
/// - The outer dimension indexes each parallel lookup
/// - The inner dimension indexes columns within a single lookup (for
///   θ-compression)
///
/// # Splitting
///
/// The helper polynomial constraint has degree `1 + lookup_degree ×
/// num_parallel_lookups`. When this exceeds the constraint system's degree
/// bound, [`Self::split`] partitions the argument into multiple
/// [`FlattenedArgument`]s, each respecting the degree limit.
#[derive(Clone)]
pub struct BatchedArgument<F: Field> {
    pub(crate) name: String,
    pub(crate) input_expressions: Vec<Vec<Expression<F>>>,
    pub(crate) table_expressions: Vec<Expression<F>>,
}

impl<F: Field> Debug for BatchedArgument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BatchedArgument")
            .field("input_expressions", &self.input_expressions)
            .field("table_expressions", &self.table_expressions)
            .finish()
    }
}

/// A lookup argument with a bounded number of parallel lookups.
///
/// Produced by [`BatchedArgument::split`], each `FlattenedArgument` contains
/// few enough parallel lookups that the helper polynomial constraint stays
/// within the constraint system's degree bound.
#[derive(Clone)]
pub struct FlattenedArgument<F: Field> {
    pub(crate) name: String,
    pub(crate) input_expressions: Vec<Vec<Expression<F>>>,
    pub(crate) table_expressions: Vec<Expression<F>>,
}

impl<F: Field> Debug for FlattenedArgument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FlattenedArgument")
            .field("name", &self.name)
            .field("input_expressions", &self.input_expressions)
            .field("table_expressions", &self.table_expressions)
            .finish()
    }
}

impl<F: Field> BatchedArgument<F> {
    /// Computes how many parallel lookups fit within the constraint system
    /// degree.
    ///
    /// The helper constraint `h(X) · ∏ⱼ(fⱼ(X) + β) = Σⱼ ∏_{k≠j}(fₖ(X) + β)` has
    /// degree `1 + lookup_degree × num_parallel_lookups`. This method returns
    /// the maximum number of parallel lookups before exceeding `cs_degree`.
    pub(crate) fn nb_parallel_lookups(&self, cs_degree: usize) -> usize {
        let max_degree = (cs_degree - 1).next_power_of_two() + 1;

        // Find the maximum degree across all input expressions
        let lookup_degree = self
            .input_expressions
            .iter()
            .flat_map(|exprs| exprs.iter().map(|expr| expr.degree()))
            .max()
            .unwrap_or(1);

        // The dominating factor of the lookup argument is:
        // h(X) * ∏_j(f_j(X) + β) = Σ_j ∏_{k≠j}(f_k(X) + β)
        // which has degree: 1 + lookup_degree * nb_parallel_lookups
        (max_degree - 1) / lookup_degree
    }

    /// Returns the degree of the helper polynomial constraint after batching.
    pub(crate) fn degree_batched_argument(&self, cs_degree: usize) -> usize {
        // Find the maximum degree across all input expressions
        let lookup_degree = self
            .input_expressions
            .iter()
            .flat_map(|exprs| exprs.iter().map(|expr| expr.degree()))
            .max()
            .unwrap_or(1);

        self.nb_parallel_lookups(cs_degree) * lookup_degree + 1
    }

    /// Constructs a new lookup argument.
    ///
    /// `table_map` is a sequence of `(input, table)` tuples.
    pub fn new<S: AsRef<str>>(
        name: S,
        table_map: Vec<(Vec<Expression<F>>, Expression<F>)>,
    ) -> Self {
        let (input_expressions, table_expressions): (Vec<Vec<Expression<F>>>, Vec<Expression<F>>) =
            table_map.into_iter().unzip();

        // The input expressions are a 2D array, where the first dimension represents
        // the width of the lookup, while the second represents the size of the
        // parallel lookup (how many columns are we looking up in a single
        // table). The β batching happens over the first dimension.
        // Therefore, we transpose the array so that it is easier to handle later.
        let lookup_width = input_expressions.len();
        let nb_parallel_lookups = input_expressions[0].len();
        let mut transposed_input_expressions =
            vec![vec![Expression::Constant(F::ZERO); lookup_width]; nb_parallel_lookups];

        input_expressions.into_iter().enumerate().for_each(|(i, width)| {
            assert_eq!(width.len(), nb_parallel_lookups);
            width
                .into_iter()
                .enumerate()
                .for_each(|(j, parallel)| transposed_input_expressions[j][i] = parallel)
        });

        BatchedArgument {
            name: name.as_ref().to_string(),
            input_expressions: transposed_input_expressions,
            table_expressions,
        }
    }

    /// Splits this argument into [`FlattenedArgument`]s that respect the degree
    /// bound.
    ///
    /// Each resulting `FlattenedArgument` contains at most
    /// [`Self::nb_parallel_lookups`] inputs, ensuring the helper constraint
    /// degree stays within `cs_degree`.
    pub fn split(&self, cs_degree: usize) -> Vec<FlattenedArgument<F>> {
        assert_eq!(
            self.input_expressions[0].len(),
            self.table_expressions.len()
        );
        let nb_lookups = self.nb_parallel_lookups(cs_degree);
        self.input_expressions
            .chunks(nb_lookups)
            .enumerate()
            .map(|(idx, chunk)| FlattenedArgument {
                name: format!("{}-{}", self.name, idx),
                input_expressions: chunk.to_vec(),
                table_expressions: self.table_expressions.clone(),
            })
            .collect()
    }
}

impl<F: Field> FlattenedArgument<F> {
    /// Returns the input expressions for this argument.
    ///
    /// Organized as `[parallel_lookups][lookup_width]`.
    pub fn input_expressions(&self) -> &[Vec<Expression<F>>] {
        &self.input_expressions
    }

    /// Returns the table expressions for this argument.
    pub fn table_expressions(&self) -> &[Expression<F>] {
        &self.table_expressions
    }
}

#[derive(Debug)]
pub(crate) struct Evaluated<F: PrimeField> {
    multiplicities_eval: F,
    helper_eval: F,
    accumulator_eval: F,
    accumulator_next_eval: F,
}

impl<F: PrimeField> Evaluated<F> {
    #[allow(clippy::too_many_arguments)]
    /// Computes the constraint expressions.
    ///
    /// When a lookup involves multiple columns, `theta` is used as a random
    /// challenge to compress them into a single value via a random linear
    /// combination. That is, given expressions `(e₁, ..., eₗ)`, the compressed
    /// value is `e₁·θˡ⁻¹ + e₂·θˡ⁻² + ... + eₗ`. Both the input values `fⱼ`
    /// and the table value `t` are compressed this way before being
    /// substituted into the LogUp identities.
    ///
    /// Checks two identities (where `fⱼ` and `t` denote the compressed values):
    /// - **Helper constraint**: `h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)`
    /// - **Accumulator constraint**: `Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) +
    ///   β) - m(x)`
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_0: F,
        l_last: F,
        l_blind: F,
        argument: &'a FlattenedArgument<F>,
        theta: F,
        beta: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        use crate::plonk::circuit::Expression;

        let active_rows = F::ONE - (l_last + l_blind);
        let evaluate_expressions = |expressions: &[Expression<F>]| {
            expressions
                .iter()
                .map(|expression| {
                    expression.evaluate(
                        &|scalar| scalar,
                        &|_| panic!("virtual selectors are removed during optimization"),
                        &|query| fixed_evals[query.index.unwrap()],
                        &|query| advice_evals[query.index.unwrap()],
                        &|query| instance_evals[query.index.unwrap()],
                        &|challenge| challenges[challenge.index()],
                        &|a| -a,
                        &|a, b| a + b,
                        &|a, b| a * b,
                        &|a, scalar| a * scalar,
                    )
                })
                .collect::<Vec<_>>()
        };
        let compress_expressions = |expressions: &[Expression<F>]| {
            evaluate_expressions(expressions)
                .iter()
                .fold(F::ZERO, |acc, eval| acc * theta + eval)
        };

        let compressed_table = compress_expressions(&argument.table_expressions);

        let compressed_inputs_with_beta = argument
            .input_expressions
            .iter()
            .map(|input| {
                let compressed = compress_expressions(input);
                compressed + beta
            })
            .collect::<Vec<_>>();

        // Helper polynomial constraint: h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)
        // This ensures the helper polynomial has the correct structure for LogUp
        // soundness. Note: This must hold everywhere (as a polynomial
        // identity), not just at active rows.
        let product: F = compressed_inputs_with_beta.iter().product();

        // Compute partial products:
        // ∏_{k≠j}(fₖ(x) + β) = product / (fⱼ(x) + β)
        let partial_products: Vec<F> = compressed_inputs_with_beta
            .iter()
            .map(|input| product * input.invert().unwrap())
            .collect();
        let sum: F = partial_products.iter().sum();
        let helper_expression = || self.helper_eval * product - sum;

        // LogUp accumulator constraint:
        // Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) + β) - m(x)
        // Rearranging: (Z(ωx) - Z(x) - h(x)) · (t(x) + β) + m(x) = 0
        let accumulator_constraint = || {
            let diff = (self.accumulator_next_eval - self.accumulator_eval - self.helper_eval)
                * (compressed_table + beta)
                + self.multiplicities_eval;
            diff * active_rows
        };

        [
            (l_0 + l_last) * self.accumulator_eval,
            helper_expression(),
            accumulator_constraint(),
        ]
        .into_iter()
    }
}

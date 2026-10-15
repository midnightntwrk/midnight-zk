// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

use std::collections::BTreeMap;

use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
    poly::PolynomialLabel,
};

use crate::{
    CircuitField,
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    verifier::{
        ScalarChip,
        argument::Evaluation,
        utils::{mul_add, try_reduce},
    },
};

pub(crate) mod lookup;
pub(crate) mod permutation;
pub(crate) mod trash;

/// The `index`-th evaluation of the polynomial labelled `label`.
pub(crate) fn eval_at<'a, F: CircuitField>(
    evals_map: &'a BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
    label: &PolynomialLabel,
    index: usize,
) -> Result<&'a AssignedNative<F>, Error> {
    evals_map
        .get(label)
        .and_then(|evals| evals.get(index))
        .map(|evaluation| evaluation.eval())
        .ok_or_else(|| Error::Synthesis(format!("missing evaluation {index} for {label}")))
}

/// Function to evaluate expressions in-circuit.
///
/// Every sum (including its negations and scalings) is computed as a single
/// linear combination, whose terms are the leaves and products of the sum.
/// Constants are folded into the coefficients.
pub(crate) fn eval_expression<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    advice: &[AssignedNative<F>],   // advice evals
    fixed: &[AssignedNative<F>],    // fixed evals
    instance: &[AssignedNative<F>], // instance evals
    expr: &Expression<F>,
) -> Result<AssignedNative<F>, Error> {
    let evals = Evals {
        advice,
        fixed,
        instance,
    };
    let mut terms = vec![];
    let mut constant = F::ZERO;
    add_terms(
        layouter,
        scalar_chip,
        &evals,
        expr,
        F::ONE,
        &mut terms,
        &mut constant,
    )?;
    scalar_chip.linear_combination(layouter, &terms, constant)
}

/// The advice, fixed and instance evaluations that expressions refer to.
struct Evals<'a, F: CircuitField> {
    advice: &'a [AssignedNative<F>],
    fixed: &'a [AssignedNative<F>],
    instance: &'a [AssignedNative<F>],
}

/// Adds `coeff * expr` to the linear combination `sum terms + constant`.
#[allow(clippy::too_many_arguments)]
fn add_terms<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    evals: &Evals<F>,
    expr: &Expression<F>,
    coeff: F,
    terms: &mut Vec<(F, AssignedNative<F>)>,
    constant: &mut F,
) -> Result<(), Error> {
    let mut add = |e, c, terms: &mut _, constant: &mut _| {
        add_terms(layouter, scalar_chip, evals, e, c, terms, constant)
    };
    match expr {
        Expression::Selector(_) => panic!("Virtual selector are removed during optimisation"),
        Expression::Constant(k) => *constant += coeff * k,
        Expression::Negated(e) => add(e, -coeff, terms, constant)?,
        Expression::Scaled(e, k) => add(e, coeff * k, terms, constant)?,
        Expression::Sum(e1, e2) => {
            add(e1, coeff, terms, constant)?;
            add(e2, coeff, terms, constant)?;
        }
        Expression::Product(..) => {
            let mut scale = coeff;
            let mut factors = vec![];
            add_factors(layouter, scalar_chip, evals, expr, &mut scale, &mut factors)?;
            if factors.is_empty() {
                *constant += scale
            } else {
                terms.push((scale, scalar_chip.mul_many(layouter, &factors)?));
            }
        }
        Expression::Fixed(q) => terms.push((coeff, evals.fixed[q.index().unwrap()].clone())),
        Expression::Advice(q) => terms.push((coeff, evals.advice[q.index.unwrap()].clone())),
        Expression::Instance(q) => terms.push((coeff, evals.instance[q.index.unwrap()].clone())),
    }
    Ok(())
}

/// Splits the product `expr` into its factors, so that `expr` equals the
/// product of the given `scale`, every constant factor and every non-constant
/// factor. The constant factors (including the constants of `Scaled` and
/// `Negated`, and the sums that evaluate to a constant) are multiplied into
/// `scale`, and the non-constant ones are pushed to `factors`. Sums are not
/// expanded: each of them is evaluated (as a linear combination) into a
/// single factor.
fn add_factors<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    evals: &Evals<F>,
    expr: &Expression<F>,
    scale: &mut F,
    factors: &mut Vec<AssignedNative<F>>,
) -> Result<(), Error> {
    match expr {
        Expression::Constant(k) => *scale *= k,
        Expression::Negated(e) => {
            *scale = -*scale;
            add_factors(layouter, scalar_chip, evals, e, scale, factors)?
        }
        Expression::Scaled(e, k) => {
            *scale *= k;
            add_factors(layouter, scalar_chip, evals, e, scale, factors)?
        }
        Expression::Product(e1, e2) => {
            add_factors(layouter, scalar_chip, evals, e1, scale, factors)?;
            add_factors(layouter, scalar_chip, evals, e2, scale, factors)?;
        }
        Expression::Sum(..) | Expression::Selector(_) => {
            let sum = eval_expression(
                layouter,
                scalar_chip,
                evals.advice,
                evals.fixed,
                evals.instance,
                expr,
            )?;
            match scalar_chip.as_constant(&sum) {
                Some(k) => *scale *= k,
                None => factors.push(sum),
            }
        }
        Expression::Fixed(q) => factors.push(evals.fixed[q.index().unwrap()].clone()),
        Expression::Advice(q) => factors.push(evals.advice[q.index.unwrap()].clone()),
        Expression::Instance(q) => factors.push(evals.instance[q.index.unwrap()].clone()),
    }
    Ok(())
}

/// Compresses `(e_0, …, e_{l-1})` into `Σᵢ r[i]·eᵢ`, one operation per term.
pub(crate) fn compress_expressions_indexed<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    advice_evals: &[AssignedNative<F>],
    fixed_evals: &[AssignedNative<F>],
    instance_evals: &[AssignedNative<F>],
    r: &[AssignedNative<F>],
    expressions: &[Expression<F>],
) -> Result<AssignedNative<F>, Error> {
    assert!(!expressions.is_empty() && expressions.len() <= r.len());
    let evals = expressions
        .iter()
        .map(|e| {
            eval_expression::<F>(
                layouter,
                scalar_chip,
                advice_evals,
                fixed_evals,
                instance_evals,
                e,
            )
        })
        .collect::<Result<Vec<_>, Error>>()?;

    let first = scalar_chip.mul(layouter, &r[0], &evals[0], None)?;
    evals.iter().zip(r).skip(1).try_fold(first, |acc, (eval, r)| {
        // acc := r * eval + acc
        mul_add(layouter, scalar_chip, r, eval, &acc)
    })
}

pub(crate) fn compress_expressions<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    advice_evals: &[AssignedNative<F>],
    fixed_evals: &[AssignedNative<F>],
    instance_evals: &[AssignedNative<F>],
    r: &AssignedNative<F>,
    expressions: &[Expression<F>],
) -> Result<AssignedNative<F>, Error> {
    let evaluated_expressions = expressions
        .iter()
        .map(|expression| {
            eval_expression::<F>(
                layouter,
                scalar_chip,
                advice_evals,
                fixed_evals,
                instance_evals,
                expression,
            )
        })
        .collect::<Result<Vec<_>, Error>>()?;

    try_reduce(evaluated_expressions, |acc, eval| {
        // acc := acc * r + eval
        mul_add(layouter, scalar_chip, &acc, r, &eval)
    })
}

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
pub(crate) fn eval_expression<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    advice: &[AssignedNative<F>],   // advice evals
    fixed: &[AssignedNative<F>],    // fixed evals
    instance: &[AssignedNative<F>], // instance evals
    expr: &Expression<F>,
) -> Result<AssignedNative<F>, Error> {
    match expr {
        Expression::Constant(k) => scalar_chip.assign_fixed(layouter, *k),
        Expression::Selector(_) => {
            panic!("Virtual selector are removed during optimisation")
        }
        Expression::Fixed(query) => Ok(fixed[query.index().unwrap()].clone()),
        Expression::Advice(query) => Ok(advice[query.index.unwrap()].clone()),
        Expression::Instance(query) => Ok(instance[query.index.unwrap()].clone()),
        Expression::Negated(e) => {
            let val = eval_expression::<F>(layouter, scalar_chip, advice, fixed, instance, e)?;
            scalar_chip.neg(layouter, &val)
        }
        Expression::Sum(e1, e2) => {
            let e1 = eval_expression::<F>(layouter, scalar_chip, advice, fixed, instance, e1)?;
            let e2 = eval_expression::<F>(layouter, scalar_chip, advice, fixed, instance, e2)?;
            scalar_chip.add(layouter, &e1, &e2)
        }
        Expression::Product(e1, e2) => {
            let val1 = eval_expression::<F>(layouter, scalar_chip, advice, fixed, instance, e1)?;
            let val2 = eval_expression::<F>(layouter, scalar_chip, advice, fixed, instance, e2)?;
            scalar_chip.mul(layouter, &val1, &val2, None)
        }
        Expression::Scaled(e, k) => {
            let val = eval_expression::<F>(layouter, scalar_chip, advice, fixed, instance, e)?;
            scalar_chip.mul_by_constant(layouter, &val, *k)
        }
    }
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

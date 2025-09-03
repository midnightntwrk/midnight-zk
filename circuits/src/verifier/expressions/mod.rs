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

use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
};

use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    verifier::SelfEmulation,
};

pub(crate) mod lookup;
pub(crate) mod permutation;

/// Function to evaluate expressions in-circuit.
pub(crate) fn eval_expression<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    advice: &[AssignedNative<S::F>],   // advice evals
    fixed: &[AssignedNative<S::F>],    // fixed evals
    instance: &[AssignedNative<S::F>], // instance evals
    expr: &Expression<S::F>,
) -> Result<AssignedNative<S::F>, Error> {
    match expr {
        Expression::Constant(k) => scalar_chip.assign_fixed(layouter, *k),
        Expression::Selector(_) => {
            panic!("Virtual selector are removed during optimisation")
        }
        Expression::Fixed(query) => Ok(fixed[query.index().unwrap()].clone()),
        Expression::Advice(query) => Ok(advice[query.index.unwrap()].clone()),
        Expression::Instance(query) => Ok(instance[query.index.unwrap()].clone()),
        Expression::Challenge(_) => panic!("We do not suport multi-phase yet"),
        Expression::Negated(e) => {
            let val = eval_expression::<S>(layouter, scalar_chip, advice, fixed, instance, e)?;
            scalar_chip.neg(layouter, &val)
        }
        Expression::Sum(e1, e2) => {
            let e1 = eval_expression::<S>(layouter, scalar_chip, advice, fixed, instance, e1)?;
            let e2 = eval_expression::<S>(layouter, scalar_chip, advice, fixed, instance, e2)?;
            scalar_chip.add(layouter, &e1, &e2)
        }
        Expression::Product(e1, e2) => {
            let val1 = eval_expression::<S>(layouter, scalar_chip, advice, fixed, instance, e1)?;
            let val2 = eval_expression::<S>(layouter, scalar_chip, advice, fixed, instance, e2)?;
            scalar_chip.mul(layouter, &val1, &val2, None)
        }
        Expression::Scaled(e, k) => {
            let val = eval_expression::<S>(layouter, scalar_chip, advice, fixed, instance, e)?;
            scalar_chip.mul_by_constant(layouter, &val, *k)
        }
    }
}

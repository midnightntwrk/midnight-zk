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

//! In-circuit lookup argument constraint expressions.
//!
//! This is the in-circuit analog of the constraint expressions from
//! `proofs/src/plonk/logup/verifier.rs`.

use ff::Field;
use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
};

use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    verifier::{
        expressions::{compress_expressions, eval_expression},
        lookup::LookupEvaluated,
        SelfEmulation,
    },
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn lookup_expressions<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    lookup_evals: &LookupEvaluated<S>,
    selector_expression: &Expression<S::F>,
    per_flat_input_expressions: &[&[Vec<Expression<S::F>>]],
    table_expressions: &[Expression<S::F>],
    advice_evals: &[AssignedNative<S::F>],
    fixed_evals: &[AssignedNative<S::F>],
    instance_evals: &[AssignedNative<S::F>],
    l_0: &AssignedNative<S::F>,
    l_last: &AssignedNative<S::F>,
    l_blind: &AssignedNative<S::F>,
    theta: &AssignedNative<S::F>,
    beta: &AssignedNative<S::F>,
) -> Result<Vec<AssignedNative<S::F>>, Error> {
    let active_rows = {
        scalar_chip.linear_combination(
            layouter,
            &[(-S::F::ONE, l_last.clone()), (-S::F::ONE, l_blind.clone())],
            S::F::ONE,
        )?
    };

    let selector = eval_expression::<S>(
        layouter,
        scalar_chip,
        advice_evals,
        fixed_evals,
        instance_evals,
        selector_expression,
    )?;

    let compressed_table = compress_expressions::<S>(
        layouter,
        scalar_chip,
        advice_evals,
        fixed_evals,
        instance_evals,
        theta,
        table_expressions,
    )?;
    let compressed_table_with_beta = scalar_chip.add(layouter, &compressed_table, beta)?;

    // (l_0(x) + l_last(x)) * Z(x) = 0
    let l_0_plus_l_last = scalar_chip.add(layouter, l_0, l_last)?;
    let boundary = scalar_chip.mul(
        layouter,
        &l_0_plus_l_last,
        &lookup_evals.accumulator_eval,
        None,
    )?;

    let mut result = vec![boundary];
    let mut sum_helpers: Option<AssignedNative<S::F>> = None;

    for (input_expressions, h_eval) in
        per_flat_input_expressions.iter().zip(lookup_evals.helper_evals.iter())
    {
        let compressed_inputs_with_beta = input_expressions
            .iter()
            .map(|input| {
                let compressed = compress_expressions::<S>(
                    layouter,
                    scalar_chip,
                    advice_evals,
                    fixed_evals,
                    instance_evals,
                    theta,
                    input,
                )?;
                scalar_chip.add(layouter, &compressed, beta)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let partial_products: Vec<AssignedNative<S::F>> = (0..compressed_inputs_with_beta.len())
            .map(|i| {
                let mut acc = scalar_chip.assign_fixed(layouter, S::F::ONE)?;
                for (j, input) in compressed_inputs_with_beta.iter().enumerate() {
                    if j != i {
                        acc = scalar_chip.mul(layouter, &acc, input, None)?;
                    }
                }
                Ok::<_, Error>(acc)
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Helper constraint: h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)
        // This is enforced at every row so that the constraint degree stays low —
        // multiplying by the selector would raise it.
        let product: AssignedNative<S::F> = {
            let mut iter = compressed_inputs_with_beta.into_iter();
            let first = iter.next().expect("compressed_inputs_with_beta should not be empty");
            iter.try_fold(first, |acc, input| {
                scalar_chip.mul(layouter, &acc, &input, None)
            })?
        };
        let sum_pp: AssignedNative<S::F> = {
            let mut iter = partial_products.into_iter();
            let first = iter.next().expect("partial_products should not be empty");
            iter.try_fold(first, |acc, input| scalar_chip.add(layouter, &acc, &input))?
        };

        // h(x) · ∏ⱼ(fⱼ(x) + β) - Σⱼ ∏_{k≠j}(fₖ(x) + β) = 0
        let helper_constraint = {
            scalar_chip.add_and_mul(
                layouter,
                (S::F::ZERO, h_eval),
                (S::F::ZERO, &product),
                (-S::F::ONE, &sum_pp),
                S::F::ZERO,
                S::F::ONE,
            )?
        };
        result.push(helper_constraint);

        let selector_h = scalar_chip.mul(layouter, &selector, h_eval, None)?;
        sum_helpers = Some(match sum_helpers {
            None => selector_h,
            Some(acc) => scalar_chip.add(layouter, &acc, &selector_h)?,
        });
    }

    let sum_helpers = sum_helpers.expect("at least one flattened arg");

    // Accumulator constraint:
    // (Z(ωx) - Z(x) - selector·h(x)) · (t(x) + β) + m(x) = 0
    // The selector gates only the input side (h); m is always added
    // so the table-side balance is maintained (see module-level docs in
    // logup.rs).
    let acc_constraint = {
        let z_next_minus_z = scalar_chip.sub(
            layouter,
            &lookup_evals.accumulator_next_eval,
            &lookup_evals.accumulator_eval,
        )?;
        let aux = scalar_chip.sub(layouter, &z_next_minus_z, &sum_helpers)?;
        let acc_step = scalar_chip.mul(layouter, &aux, &compressed_table_with_beta, None)?;
        let balance = scalar_chip.add(layouter, &acc_step, &lookup_evals.multiplicities_eval)?;
        scalar_chip.mul(layouter, &balance, &active_rows, None)?
    };
    result.push(acc_constraint);

    Ok(result)
}

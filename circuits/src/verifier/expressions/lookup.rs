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
    verifier::{expressions::compress_expressions, lookup::Evaluated, SelfEmulation},
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn lookup_expressions<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    lookup_evals: &Evaluated<S>,
    input_expressions: &[Vec<Expression<S::F>>],
    table_expressions: &[Expression<S::F>],
    advice_evals: &[AssignedNative<S::F>],
    fixed_evals: &[AssignedNative<S::F>],
    instance_evals: &[AssignedNative<S::F>],
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

    let partial_products: Vec<AssignedNative<S::F>> = (0..compressed_inputs_with_beta.len())
        .map(|i| {
            let mut acc = scalar_chip.assign_fixed(layouter, S::F::ONE)?;
            for j in 0..compressed_inputs_with_beta.len() {
                if j != i {
                    acc = scalar_chip.mul(layouter, &acc, &compressed_inputs_with_beta[j], None)?;
                }
            }
            Ok::<_, Error>(acc)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Helper constraint: h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)
    // This must hold everywhere (as a polynomial identity), not just at active rows.
    let product: AssignedNative<S::F> = {
        let mut iter = compressed_inputs_with_beta.into_iter();
        let first = iter.next().expect("compressed_inputs_with_beta should not be empty");
        iter.try_fold(first, |acc, input| {
            scalar_chip.mul(layouter, &acc, &input, None)
        })?
    };
    let sum: AssignedNative<S::F> = {
        let mut iter = partial_products.into_iter();
        let first = iter.next().expect("partial_products should not be empty");
        iter.try_fold(first, |acc, input| scalar_chip.add(layouter, &acc, &input))?
    };

    // h(x) · ∏ⱼ(fⱼ(x) + β) - Σⱼ ∏_{k≠j}(fₖ(x) + β) = 0
    let id_1 = {
        scalar_chip.add_and_mul(
            layouter,
            (-S::F::ONE, &sum),
            (S::F::ZERO, &lookup_evals.helper_eval),
            (S::F::ZERO, &product),
            S::F::ZERO,
            S::F::ONE,
        )?
    };

    // Accumulator constraint: Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) + β) - m(x)
    let id_2 = {
        let left = {
            scalar_chip.mul(
                layouter,
                &lookup_evals.accumulator_next_eval,
                &compressed_table_with_beta,
                None,
            )?
        };

        let right = {
            let aux1 = scalar_chip.add(
                layouter,
                &lookup_evals.accumulator_eval,
                &lookup_evals.helper_eval,
            )?;
            let aux = scalar_chip.mul(layouter, &aux1, &compressed_table_with_beta, None)?;
            scalar_chip.sub(layouter, &aux, &lookup_evals.multiplicities_eval)?
        };

        let left_minus_right = scalar_chip.sub(layouter, &left, &right)?;
        scalar_chip.mul(layouter, &left_minus_right, &active_rows, None)?
    };

    Ok(vec![id_1, id_2])
}

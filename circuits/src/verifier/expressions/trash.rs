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

//! A module for in-circuit trash arguments identities (expressions).
//! This is the in-circuit analog of the expressions from file
//! proofs/src/plonk/trash.rs.

use std::collections::BTreeMap;

use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
    poly::PolynomialLabel,
};

use crate::{
    CircuitField,
    field::AssignedNative,
    instructions::ArithInstructions,
    verifier::{
        ScalarChip,
        argument::Evaluation,
        expressions::{compress_expressions, eval_expression},
    },
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn trash_expressions<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &ScalarChip<F>,
    argument_index: usize,
    evals_map: &BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
    selector: &Expression<F>,
    constraint_expressions: &[Expression<F>],
    advice_evals: &[AssignedNative<F>],
    fixed_evals: &[AssignedNative<F>],
    instance_evals: &[AssignedNative<F>],
    trash_challenge: &AssignedNative<F>,
) -> Result<Vec<AssignedNative<F>>, Error> {
    let trash_label = PolynomialLabel::Trash(argument_index);
    let trash_eval = evals_map
        .get(&trash_label)
        .and_then(|evals| evals.first())
        .ok_or_else(|| Error::Synthesis(format!("missing evaluation for {trash_label}")))?
        .eval();

    let id = {
        let compressed = compress_expressions::<F>(
            layouter,
            scalar_chip,
            advice_evals,
            fixed_evals,
            instance_evals,
            trash_challenge,
            constraint_expressions,
        )?;

        let q = eval_expression::<F>(
            layouter,
            scalar_chip,
            advice_evals,
            fixed_evals,
            instance_evals,
            selector,
        )?;

        // `compressed - (1 - q) * trash`, computed as `compressed - trash + q * trash`
        scalar_chip.add_and_mul(
            layouter,
            (F::ZERO, &q),
            (-F::ONE, trash_eval),
            (F::ONE, &compressed),
            F::ZERO,
            F::ONE,
        )?
    };

    Ok(vec![id])
}

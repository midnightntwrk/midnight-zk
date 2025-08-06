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

//! A module for in-circuit lookup arguments identities (expressions).
//! This is the in-circuit analog of the expressions from file
//! proofs/src/plonk/lookup/verifier.rs.

use ff::Field;
use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
};

use crate::{
    field::AssignedNative,
    instructions::ArithInstructions,
    verifier::{expressions::compress_expressions, lookup::Evaluated, SelfEmulation},
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn lookup_expressions<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    lookup_evals: &Evaluated<S>,
    input_expressions: &[Expression<S::F>],
    table_expressions: &[Expression<S::F>],
    advice_evals: &[AssignedNative<S::F>],
    fixed_evals: &[AssignedNative<S::F>],
    instance_evals: &[AssignedNative<S::F>],
    l_0: &AssignedNative<S::F>,
    l_last: &AssignedNative<S::F>,
    l_blind: &AssignedNative<S::F>,
    theta: &AssignedNative<S::F>,
    beta: &AssignedNative<S::F>,
    gamma: &AssignedNative<S::F>,
) -> Result<Vec<AssignedNative<S::F>>, Error> {
    let active_rows = {
        scalar_chip.linear_combination(
            layouter,
            &[(-S::F::ONE, l_last.clone()), (-S::F::ONE, l_blind.clone())],
            S::F::ONE,
        )?
    };

    // l_0(X) * (1 - z(X)) = 0
    let id_1 = {
        let z = &lookup_evals.product_eval;

        // l_0 * (1 - z) computed as l_0 - l_0 * z
        scalar_chip.add_and_mul(
            layouter,
            (S::F::ONE, l_0),
            (S::F::ZERO, z),
            (S::F::ZERO, l_0),
            S::F::ZERO,
            -S::F::ONE,
        )?
    };

    // l_last(X) * (z(X)^2 - z(X)) = 0
    let id_2 = {
        let z = &lookup_evals.product_eval;

        // z(X)^2 - z(X)
        let aux = scalar_chip.add_and_mul(
            layouter,
            (-S::F::ONE, z),
            (S::F::ZERO, z),
            (S::F::ZERO, z),
            S::F::ZERO,
            S::F::ONE,
        )?;
        scalar_chip.mul(layouter, l_last, &aux, None)?
    };

    // {z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
    // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X)
    //   + ... + s_{m-1}(X) + \gamma)}
    // * (1 - l_last(X) - l_blind(X))
    let id_3 = {
        let left = {
            let aux1 = scalar_chip.add(layouter, &lookup_evals.permuted_input_eval, beta)?;
            let aux2 = scalar_chip.add(layouter, &lookup_evals.permuted_table_eval, gamma)?;
            let aux = scalar_chip.mul(layouter, &aux1, &aux2, None)?;
            scalar_chip.mul(layouter, &lookup_evals.product_next_eval, &aux, None)?
        };

        let right = {
            let compressed1 = compress_expressions::<S>(
                layouter,
                scalar_chip,
                advice_evals,
                fixed_evals,
                instance_evals,
                theta,
                input_expressions,
            )?;
            let compressed2 = compress_expressions::<S>(
                layouter,
                scalar_chip,
                advice_evals,
                fixed_evals,
                instance_evals,
                theta,
                table_expressions,
            )?;
            let aux1 = scalar_chip.add(layouter, &compressed1, beta)?;
            let aux2 = scalar_chip.add(layouter, &compressed2, gamma)?;
            let aux = scalar_chip.mul(layouter, &aux1, &aux2, None)?;
            scalar_chip.mul(layouter, &lookup_evals.product_eval, &aux, None)?
        };

        let left_minus_right = scalar_chip.sub(layouter, &left, &right)?;
        scalar_chip.mul(layouter, &left_minus_right, &active_rows, None)?
    };

    // a'(X) - s'(X) which is a common term in id_4 and id_5
    let input_minus_table = scalar_chip.sub(
        layouter,
        &lookup_evals.permuted_input_eval,
        &lookup_evals.permuted_table_eval,
    )?;

    // l_0(X) * (a'(X) - s'(X)) = 0
    let id_4 = scalar_chip.mul(layouter, l_0, &input_minus_table, None)?;

    // (1 - (l_last(X) + l_blind(X))) * (a'(X)-s'(X))⋅(a'(X)-a'(\omega^{-1} X)) = 0
    let id_5 = {
        let input_minus_prev = scalar_chip.sub(
            layouter,
            &lookup_evals.permuted_input_eval,
            &lookup_evals.permuted_input_inv_eval,
        )?;
        let aux = scalar_chip.mul(layouter, &input_minus_table, &input_minus_prev, None)?;
        scalar_chip.mul(layouter, &aux, &active_rows, None)?
    };

    Ok(vec![id_1, id_2, id_3, id_4, id_5])
}

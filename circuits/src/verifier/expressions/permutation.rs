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

//! A module for the in-circuit permutation argument identities (expressions).
//! This is the in-circuit analog of the expressions from file
//! src/plonk/permutation/verifier.rs from halo2.

use ff::{Field, PrimeField};
use midnight_proofs::{
    circuit::Layouter,
    plonk::{Any, Column, ColumnType, ConstraintSystem, Error},
    poly::Rotation,
};

use crate::{
    field::AssignedNative,
    instructions::ArithInstructions,
    verifier::{
        permutation::{CommonEvaluated, Evaluated},
        SelfEmulation,
    },
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn permutation_expressions<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    cs: &ConstraintSystem<S::F>,
    permutation_evals: &Evaluated<S>,
    permutations_common: &CommonEvaluated<S>,
    advice_evals: &[AssignedNative<S::F>],
    fixed_evals: &[AssignedNative<S::F>],
    instance_evals: &[AssignedNative<S::F>],
    l_0: &AssignedNative<S::F>,
    l_last: &AssignedNative<S::F>,
    l_blind: &AssignedNative<S::F>,
    beta: &AssignedNative<S::F>,
    gamma: &AssignedNative<S::F>,
    x: &AssignedNative<S::F>,
) -> Result<Vec<AssignedNative<S::F>>, Error> {
    let chunk_len = cs.degree() - 2;

    // Enforce only for the first set.
    // l_0(X) * (1 - z_0(X)) = 0
    let id_1 = {
        let first_set = permutation_evals.sets.first().unwrap();
        let z_0 = &first_set.permutation_product_eval;

        // l_0 * (1 - z_0) computed as l_0 - l_0 * z_0
        scalar_chip.add_and_mul(
            layouter,
            (S::F::ONE, l_0),
            (S::F::ZERO, z_0),
            (S::F::ZERO, l_0),
            S::F::ZERO,
            -S::F::ONE,
        )?
    };

    // Enforce only for the last set.
    // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
    let id_2 = {
        let last_set = permutation_evals.sets.last().unwrap();
        let z_l = &last_set.permutation_product_eval;

        // z_l**2 - z_l
        let aux = scalar_chip.add_and_mul(
            layouter,
            (-S::F::ONE, z_l),
            (S::F::ZERO, z_l),
            (S::F::ZERO, z_l),
            S::F::ZERO,
            S::F::ONE,
        )?;
        scalar_chip.mul(layouter, l_last, &aux, None)?
    };

    // Except for the first set, enforce.
    // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
    let ids_3 = permutation_evals
        .sets
        .iter()
        .skip(1)
        .zip(permutation_evals.sets.iter())
        .map(|(set, prev_set)| {
            let z_i = &set.permutation_product_eval;
            let z_i_prev = &prev_set.permutation_product_last_eval.clone().unwrap();

            // TODO: Optimize with add_and_double_mul
            // l_0 * (z_i - z_i_prev)
            let aux = scalar_chip.sub(layouter, z_i, z_i_prev)?;
            scalar_chip.mul(layouter, l_0, &aux, None)
        })
        .collect::<Result<Vec<AssignedNative<S::F>>, Error>>()?;

    // And for all the sets we enforce:
    // (1 - (l_last(X) + l_blind(X))) * (
    //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
    // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
    // )
    let ids_4 = permutation_evals
        .sets
        .iter()
        .zip(cs.permutation().get_columns().chunks(chunk_len))
        .zip(permutations_common.permutation_evals.chunks(chunk_len))
        .enumerate()
        .map(move |(chunk_index, ((set, columns), permutation_evals))| {
            let mut left = set.permutation_product_next_eval.clone();
            for (eval, permutation_eval) in columns
                .iter()
                .map(|&column| match column.column_type() {
                    Any::Advice(_) => {
                        advice_evals[get_query_index(column, cs.advice_queries())].clone()
                    }
                    Any::Fixed => fixed_evals[get_query_index(column, cs.fixed_queries())].clone(),
                    Any::Instance => {
                        instance_evals[get_query_index(column, cs.instance_queries())].clone()
                    }
                })
                .zip(permutation_evals.iter())
            {
                // left *= &(eval + &(*beta * permutation_eval) + &*gamma);
                let aux = scalar_chip.mul(layouter, beta, permutation_eval, None)?;
                let aux = scalar_chip.linear_combination(
                    layouter,
                    &[
                        (S::F::ONE, aux),
                        (S::F::ONE, gamma.clone()),
                        (S::F::ONE, eval),
                    ],
                    S::F::ZERO,
                )?;

                left = scalar_chip.mul(layouter, &left, &aux, None)?;
            }

            let mut right = set.permutation_product_eval.clone();

            let mut current_delta = {
                let delta_power = S::F::DELTA.pow_vartime([(chunk_index * chunk_len) as u64]);
                scalar_chip.mul(layouter, beta, x, Some(delta_power))?
            };

            for eval in columns.iter().map(|&column| match column.column_type() {
                Any::Advice(_) => {
                    advice_evals[get_query_index(column, cs.advice_queries())].clone()
                }
                Any::Fixed => fixed_evals[get_query_index(column, cs.fixed_queries())].clone(),
                Any::Instance => {
                    instance_evals[get_query_index(column, cs.instance_queries())].clone()
                }
            }) {
                // right *= &(eval + &current_delta + &*gamma);
                let aux = scalar_chip.linear_combination(
                    layouter,
                    &[
                        (S::F::ONE, eval),
                        (S::F::ONE, current_delta.clone()),
                        (S::F::ONE, gamma.clone()),
                    ],
                    S::F::ZERO,
                )?;
                right = scalar_chip.mul(layouter, &right, &aux, None)?;
                current_delta =
                    scalar_chip.mul_by_constant(layouter, &current_delta.clone(), S::F::DELTA)?;
            }

            // (left - &right) * (S::F::ONE - &(l_last + &l_blind))
            let aux1 = scalar_chip.sub(layouter, &left, &right)?;
            let aux2 = scalar_chip.linear_combination(
                layouter,
                &[(-S::F::ONE, l_last.clone()), (-S::F::ONE, l_blind.clone())],
                S::F::ONE,
            )?;
            scalar_chip.mul(layouter, &aux1, &aux2, None)
        })
        .collect::<Result<Vec<AssignedNative<S::F>>, Error>>()?;

    Ok([vec![id_1, id_2], ids_3, ids_4].concat())
}

fn get_query_index<C: ColumnType>(column: Column<Any>, queries: &[(Column<C>, Rotation)]) -> usize
where
    Column<C>: TryFrom<Column<Any>>,
    <Column<C> as TryFrom<Column<Any>>>::Error: std::fmt::Debug,
{
    for (index, query) in queries.iter().enumerate() {
        if query == &(Column::<C>::try_from(column).unwrap(), Rotation::cur()) {
            return index;
        }
    }
    panic!("Query index not found");
}

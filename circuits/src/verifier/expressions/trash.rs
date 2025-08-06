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

//! A module for in-circuit trash arguments identities (expressions).
//! This is the in-circuit analog of the expressions from file
//! proofs/src/plonk/trash/verifier.rs.

use ff::Field;
use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
};

use crate::{
    field::AssignedNative,
    instructions::ArithInstructions,
    verifier::{
        expressions::{compress_expressions, eval_expression},
        trash::Evaluated,
        SelfEmulation,
    },
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn trash_expressions<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    trash_evaluated: &Evaluated<S>,
    selector: &Expression<S::F>,
    constraint_expressions: &[Expression<S::F>],
    advice_evals: &[AssignedNative<S::F>],
    fixed_evals: &[AssignedNative<S::F>],
    instance_evals: &[AssignedNative<S::F>],
    trash_challenge: &AssignedNative<S::F>,
) -> Result<Vec<AssignedNative<S::F>>, Error> {
    let id = {
        let compressed = compress_expressions::<S>(
            layouter,
            scalar_chip,
            advice_evals,
            fixed_evals,
            instance_evals,
            trash_challenge,
            constraint_expressions,
        )?;

        let q = eval_expression::<S>(
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
            (S::F::ZERO, &q),
            (-S::F::ONE, &trash_evaluated.trash_eval),
            (S::F::ONE, &compressed),
            S::F::ZERO,
            S::F::ONE,
        )?
    };

    Ok(vec![id])
}

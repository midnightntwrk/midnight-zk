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

use midnight_circuits::instructions::AssertionInstructions;
use midnight_proofs::circuit::Layouter;
use midnight_zk_stdlib::ZkStdLib;

use crate::{types::CircuitValue, utils::F, Error, Operation};

/// Asserts in-circuit that the given inputs are equal. The circuit becomes
/// unsatisfiable if they are not.
///
/// This operation is supported on all types except on `JubjubScalar`.
///
/// # Errors
///
/// This function results in an error if the two inputs are not of the same type
/// or if their type does not support equality assertions.
//
// NB: The off-circuit version of this function is derived automatically and a
// bit more general (e.g. it works on `JubjubScalar`s).
pub fn assert_equal_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<(), Error> {
    use CircuitValue::*;
    match (x, y) {
        (Bool(a), Bool(b)) => std_lib.assert_equal(layouter, a, b)?,

        (Bytes(v), Bytes(w)) if v.len() == w.len() => {
            (v.iter().zip(w)).try_for_each(|(vi, wi)| std_lib.assert_equal(layouter, vi, wi))?
        }

        (Native(a), Native(b)) => std_lib.assert_equal(layouter, a, b)?,

        (BigUint(a), BigUint(b)) => std_lib.biguint().assert_equal(layouter, a, b)?,

        (JubjubPoint(p), JubjubPoint(q)) => std_lib.jubjub().assert_equal(layouter, p, q)?,

        _ => {
            return Err(Error::Unsupported(
                Operation::AssertEqual,
                vec![x.get_type(), y.get_type()],
            ))
        }
    }

    Ok(())
}

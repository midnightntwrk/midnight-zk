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

use midnight_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, Error, Fixed},
};
use num_bigint::BigInt as BI;

use super::unified::CoeffBounds;
use crate::{
    field::foreign::params::FieldEmulationParams, types::AssignedField, utils::util::bigint_to_fe,
    CircuitField,
};

/// Asserts that each coefficient lies within `bounds`, then assigns the six
/// fixed coefficient columns at `offset`.
///
/// The bounds check is a hard `assert!`: a violation means the caller used
/// coefficients outside the range for which the carry witness bounds were
/// computed, which could break soundness.
pub(super) fn assign_coeffs<F: CircuitField>(
    region: &mut Region<'_, F>,
    offset: usize,
    coeff_cols: &[Column<Fixed>; 6],
    bounds: &CoeffBounds,
    a: &BI,
    b: &BI,
    d: &BI,
    e: &BI,
    ca: &BI,
    cd: &BI,
) -> Result<(), Error> {
    assert!(
        bounds.a.0 <= *a && *a <= bounds.a.1,
        "coefficient a={a} ∉ [{}, {}]",
        bounds.a.0,
        bounds.a.1
    );
    assert!(
        bounds.b.0 <= *b && *b <= bounds.b.1,
        "coefficient b={b} ∉ [{}, {}]",
        bounds.b.0,
        bounds.b.1
    );
    assert!(
        bounds.d.0 <= *d && *d <= bounds.d.1,
        "coefficient d={d} ∉ [{}, {}]",
        bounds.d.0,
        bounds.d.1
    );
    assert!(
        bounds.e.0 <= *e && *e <= bounds.e.1,
        "coefficient e={e} ∉ [{}, {}]",
        bounds.e.0,
        bounds.e.1
    );
    assert!(
        bounds.ca.0 <= *ca && *ca <= bounds.ca.1,
        "coefficient ca={ca} ∉ [{}, {}]",
        bounds.ca.0,
        bounds.ca.1
    );
    assert!(
        bounds.cd.0 <= *cd && *cd <= bounds.cd.1,
        "coefficient cd={cd} ∉ [{}, {}]",
        bounds.cd.0,
        bounds.cd.1
    );

    let vals = [a, b, d, e, ca, cd];
    let names = ["a", "b", "d", "e", "ca", "cd"];
    for ((&col, v), name) in coeff_cols.iter().zip(vals.iter()).zip(names.iter()) {
        region.assign_fixed(|| *name, col, offset, || Value::known(bigint_to_fe::<F>(v)))?;
    }
    Ok(())
}

/// Copies every limb of `var` into the corresponding column in `cols` at
/// `offset`.
pub(super) fn copy_limbs<F, K, P>(
    region: &mut Region<'_, F>,
    var: &AssignedField<F, K, P>,
    cols: &[Column<Advice>],
    offset: usize,
    label: &'static str,
) -> Result<(), Error>
where
    F: CircuitField,
    K: CircuitField,
    P: FieldEmulationParams<F, K>,
{
    var.limb_values()
        .iter()
        .zip(cols.iter())
        .try_for_each(|(cell, &col)| cell.copy_advice(|| label, region, col, offset).map(|_| ()))
}

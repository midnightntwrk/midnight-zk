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

//! Shared utilities for foreign EC chips.

use std::{cmp::max, collections::HashMap, hash::Hash};

use ff::Field;
use group::Group;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

use crate::{
    ecc::curves::CircuitCurve,
    field::{foreign::field_chip::FieldChipConfig, AssignedNative},
    instructions::{
        AssignmentInstructions, ControlFlowInstructions, EccInstructions, ScalarFieldInstructions,
    },
    types::InnerValue,
    CircuitField,
};

/// Preprocessing of MSM inputs.
///
/// Takes a list of `(scalar, bound)` pairs and their corresponding bases,
/// and returns a simplified, deduplicated representation in three parts:
///
///  - **Scalars and bases** ready for windowed scalar multiplication (with
///    updated bounds after deduplication).
///  - **1-bit scalar bases**: pairs `(base, scalar)` where the scalar is known
///    to be 0 or 1, to be handled separately by [`add_1bit_scalar_bases`].
///
/// The simplification proceeds in two phases:
///  1. Filters out identity bases (no-ops) and separates 1-bit scalars.
///  2. Deduplicates equal bases (by adding their scalars) and equal scalars (by
///     adding their bases).
#[allow(clippy::type_complexity)]
pub(crate) fn msm_preprocess<F, C, EI, SFI>(
    ec_chip: &EI,
    scalar_chip: &SFI,
    layouter: &mut impl Layouter<F>,
    scalars: &[(EI::Scalar, usize)],
    bases: &[EI::Point],
) -> Result<
    (
        Vec<(EI::Scalar, usize)>,
        Vec<EI::Point>,
        Vec<(EI::Point, EI::Scalar)>,
    ),
    Error,
>
where
    F: CircuitField,
    C: CircuitCurve,
    EI: EccInstructions<F, C, Scalar = SFI::Scalar> + AssignmentInstructions<F, EI::Point>,
    SFI: ScalarFieldInstructions<F>,
    SFI::Scalar: InnerValue<Element = C::ScalarField>,
    EI::Point: PartialEq + Eq + Hash,
{
    // Phase 1:
    // --------

    // Filter out bases that are known to be the identity at compile time.
    // These contribute nothing to the MSM result.
    let identity = ec_chip.assign_fixed(layouter, C::CryptographicGroup::identity())?;
    let (scalars, bases): (Vec<_>, Vec<_>) = scalars
        .iter()
        .zip(bases.iter())
        .filter(|(_, base)| *base != &identity)
        .map(|(s, b)| (s.clone(), b.clone()))
        .unzip();

    // If any of the scalars is known to be 1, or has a bound of 1 (i.e. it is
    // known to be either 0 or 1) remove it (with its base) from the list and
    // simply add it at the end.
    let one: EI::Scalar = scalar_chip.assign_fixed(layouter, C::ScalarField::ONE)?;
    let mut bases_with_1bit_scalar = vec![];
    let mut filtered_scalars = vec![];
    let mut filtered_bases = vec![];
    for (scalar, base) in scalars.iter().zip(bases.iter()) {
        if scalar.0 == one || scalar.1 == 1 {
            bases_with_1bit_scalar.push((base.clone(), scalar.0.clone()));
        } else {
            filtered_scalars.push(scalar.clone());
            filtered_bases.push(base.clone());
        }
    }

    let scalars = filtered_scalars;
    let bases = filtered_bases;

    // Phase 2:
    // --------

    // If two bases are exactly the same (as symbolic PLONK variables), we
    // deduplicate them by adding their scalars.
    let mut cache_bases: HashMap<EI::Point, (EI::Scalar, usize)> = HashMap::new();
    let mut unique_bases: Vec<EI::Point> = vec![];
    for (base, scalar) in bases.iter().zip(scalars.iter()) {
        if let Some(acc) = cache_bases.insert(base.clone(), scalar.clone()) {
            let new_scalar = scalar_chip.add(layouter, &acc.0, &scalar.0)?;
            let new_bound = max(acc.1, scalar.1) + 1;
            cache_bases.insert(base.clone(), (new_scalar, new_bound));
        } else {
            unique_bases.push(base.clone());
        }
    }
    let scalars = unique_bases
        .iter()
        .map(|b| cache_bases.get(b).unwrap().clone())
        .collect::<Vec<_>>();
    let bases = unique_bases;

    // If two scalars are exactly the same (as symbolic PLONK variables), we
    // deduplicate them by adding their bases.
    let mut cache_scalars: HashMap<(EI::Scalar, usize), EI::Point> = HashMap::new();
    let mut unique_scalars: Vec<(EI::Scalar, usize)> = vec![];
    for (scalar, base) in scalars.iter().zip(bases.iter()) {
        if let Some(acc) = cache_scalars.insert(scalar.clone(), base.clone()) {
            let new_acc = ec_chip.add(layouter, &acc, base)?;
            cache_scalars.insert(scalar.clone(), new_acc);
        } else {
            unique_scalars.push(scalar.clone());
        }
    }
    let bases = unique_scalars
        .iter()
        .map(|s| cache_scalars.get(s).unwrap().clone())
        .collect::<Vec<_>>();
    let scalars = unique_scalars;

    Ok((scalars, bases, bases_with_1bit_scalar))
}

/// Adds the 1-bit scalar bases (as returned by [`msm_preprocess`]) into an
/// accumulator.
///
/// For each `(base, scalar)` pair, if the scalar is known to be 1 the base
/// is added directly; otherwise we select between the identity and the base
/// based on whether the scalar is zero, and add the result.
pub(crate) fn add_1bit_scalar_bases<F, C, EI, SFI>(
    layouter: &mut impl Layouter<F>,
    ec_chip: &EI,
    scalar_chip: &SFI,
    bases_with_1bit_scalar: &[(EI::Point, EI::Scalar)],
    acc: EI::Point,
) -> Result<EI::Point, Error>
where
    F: CircuitField,
    C: CircuitCurve,
    EI: EccInstructions<F, C, Scalar = SFI::Scalar>
        + AssignmentInstructions<F, EI::Point>
        + ControlFlowInstructions<F, EI::Point>,
    SFI: ScalarFieldInstructions<F>,
    SFI::Scalar: InnerValue<Element = C::ScalarField>,
{
    let identity = ec_chip.assign_fixed(layouter, C::CryptographicGroup::identity())?;
    let one: EI::Scalar = scalar_chip.assign_fixed(layouter, C::ScalarField::ONE)?;

    bases_with_1bit_scalar.iter().try_fold(acc, |acc, (b, s)| {
        let s_times_b = if s == &one {
            b.clone()
        } else {
            let s_is_zero = scalar_chip.is_zero(layouter, s)?;
            ec_chip.select(layouter, &s_is_zero, &identity, b)?
        };
        ec_chip.add(layouter, &acc, &s_times_b)
    })
}

/// Configures the self-referential dynamic lookup used by `multi_select`.
///
/// Returns `(q_multi_select, idx_col_multi_select, tag_col_multi_select)`.
/// The caller must store these in its config and pass them to
/// [`fill_dynamic_lookup_row`].
pub(crate) fn configure_multi_select_lookup<F: CircuitField>(
    meta: &mut ConstraintSystem<F>,
    advice_columns: &[Column<Advice>],
    base_field_config: &FieldChipConfig,
) -> (Selector, Column<Advice>, Column<Fixed>) {
    let q_multi_select = meta.complex_selector();
    assert!(advice_columns.len() > 2 * base_field_config.x_cols.len());
    let idx_col_multi_select = *advice_columns.last().unwrap();
    meta.enable_equality(idx_col_multi_select);

    // The tag column should not be shared with other fixed columns since it is used
    // as a separator. It could be done if an extra selector were used as a
    // separator instead.
    let tag_col_multi_select = meta.fixed_column();

    meta.lookup_any("multi_select lookup", None, |meta| {
        let sel = meta.query_selector(q_multi_select);
        let not_sel = Expression::from(1) - sel.clone();

        // This is a lookup of a column (set) on itself!
        //
        // All identities are of the form: `(value, (1 - sel) * value)`.
        // Here, `value` is actually a tuple, but it is helpful to ignore this detail
        // initially, for the sake of simplicity, we will come back to it later.
        //
        // The above should be interpreted as a set inclusion:
        // {value(ω) | ω ∈ Ω}  ⊆  {(1 - sel(ω)) * value(ω) | ω ∈ Ω}.
        //
        // Note that this lookup is requiring that every `value` be in the table!
        //
        // - Values where the selector is disabled (those we do not want to lookup) are
        //   trivially in the table (they appear at least at their own ω).
        //
        // - Values that we do want to lookup have `sel = 1` thus `(1 - sel) * value` is
        //   0 at their offset, forcing them to be somewhere else in the table.
        //
        // Observe that the table is then defined by all the entries where `sel = 0`,
        // and there is no distinction between the intended lookup table and the values
        // from other circuit regions where we simply want to skip this lookup check.
        // This is not a problem (for soundness) because `value`, as we anticipated, is
        // indeed a tuple `(value', tag)` where, in turn, `value'` may be a tuple
        // itself. Importantly, `tag` is a fixed column which allows us to use it as a
        // domain separator to solve the above ambiguity:
        //
        //  - The case `tag = 0` is reserved for disabled checks that are not supposed
        //    to be part of the payload table,
        //  - Any other value of `tag` is dedicated to table positions.
        //
        // Note that different values of `tag` can be used to encode independent tables
        // with the same lookup argument.
        let mut identities = [idx_col_multi_select]
            .iter()
            .chain(base_field_config.x_cols.iter())
            .chain(base_field_config.z_cols.iter())
            .map(|col| {
                let val = meta.query_advice(*col, Rotation::cur());
                (val.clone(), not_sel.clone() * val)
            })
            .collect::<Vec<_>>();

        // Handle tag independently, since it is a fixed column
        let tag = meta.query_fixed(tag_col_multi_select, Rotation::cur());
        identities.push((tag.clone(), not_sel * tag));

        identities
    });

    (q_multi_select, idx_col_multi_select, tag_col_multi_select)
}

/// Fills a single row in the dynamic-lookup region for `multi_select`.
///
/// Returns a pair of vectors corresponding to the assigned limbs of the
/// x coordinate and the y coordinate respectively.
/// (The assigned index and table_tag are not returned.)
///
/// If `enable_lookup` is set, the selector `q_multi_select` is enabled at
/// this row and the values of the coordinate limbs ARE NOT copied, but
/// witnessed freely. It is the responsibility of the caller (with
/// `enable_lookup = true`) to further restrict these cells, which are an
/// output of this function.
#[allow(clippy::type_complexity, clippy::too_many_arguments)]
pub(crate) fn fill_dynamic_lookup_row<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    x_limbs: &[AssignedNative<F>],
    y_limbs: &[AssignedNative<F>],
    index: &AssignedNative<F>,
    x_cols: &[Column<Advice>],
    y_cols: &[Column<Advice>],
    idx_col: Column<Advice>,
    tag_col: Column<Fixed>,
    q_multi_select: Selector,
    table_tag: F,
    enable_lookup: bool,
) -> Result<(Vec<AssignedNative<F>>, Vec<AssignedNative<F>>), Error> {
    layouter.assign_region(
        || "multi_select table",
        |mut region| {
            if enable_lookup {
                q_multi_select.enable(&mut region, 0)?;
            };

            let mut xs = vec![];
            let mut ys = vec![];
            for i in 0..x_limbs.len() {
                // If the lookup is enabled, we do not copy the limbs into the current row,
                // because copying imposes restrictions at compile-time (through the permutation
                // argument). Instead, we want to give freedom to witness any value (from the
                // table) and we will enforce that it is correct through the lookup check.
                if enable_lookup {
                    let x_val = x_limbs[i].value().copied();
                    let y_val = y_limbs[i].value().copied();
                    xs.push(region.assign_advice(|| "x", x_cols[i], 0, || x_val)?);
                    ys.push(region.assign_advice(|| "y", y_cols[i], 0, || y_val)?);
                }
                // If the lookup is disabled we copy the limbs into the current row.
                else {
                    xs.push(x_limbs[i].copy_advice(|| "x", &mut region, x_cols[i], 0)?);
                    ys.push(y_limbs[i].copy_advice(|| "y", &mut region, y_cols[i], 0)?);
                }
            }
            index.copy_advice(|| "x", &mut region, idx_col, 0)?;
            region.assign_fixed(|| "assign tag", tag_col, 0, || Value::known(table_tag))?;

            Ok((xs, ys))
        },
    )
}

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
    CircuitField,
    ecc::curves::CircuitCurve,
    field::{AssignedNative, foreign::field_chip::FieldChipConfig},
    instructions::{
        AssignmentInstructions, ControlFlowInstructions, EccInstructions, ScalarFieldInstructions,
    },
    types::InnerValue,
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
/// The simplification proceeds in two steps:
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
    // Step 1:
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

    // Step 2:
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
/// Returns `(q_multi_select, tag_col_multi_select)`. The caller must store
/// these in its config and pass them to [`fill_dynamic_lookup_row`].
///
/// A row of the lookup holds the limbs of a point in the `x_cols` and
/// `z_cols` of the base field chip, plus a fixed tag. A table entry encodes
/// its index in the tag, `tag * MULTI_SELECT_INDEX_SHIFT + index`, so it
/// needs no advice cell for it. A lookup row holds the bare `tag * SHIFT` in
/// its fixed cell and its (witnessed) index in the next row, first `x` column.
pub(crate) fn configure_multi_select_lookup<F: CircuitField>(
    meta: &mut ConstraintSystem<F>,
    advice_columns: &[Column<Advice>],
    base_field_config: &FieldChipConfig,
) -> (Selector, Column<Fixed>) {
    let q_multi_select = meta.complex_selector();
    assert!(advice_columns.len() >= 2 * base_field_config.x_cols.len());

    // The index of a lookup row lives in the next row (equality is enabled on
    // `x_cols` by the field chip).
    let idx_col_multi_select = base_field_config.x_cols[0];

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
        let mut identities = (base_field_config.x_cols.iter())
            .chain(base_field_config.z_cols.iter())
            .map(|col| {
                let val = meta.query_advice(*col, Rotation::cur());
                (val.clone(), not_sel.clone() * val)
            })
            .collect::<Vec<_>>();

        // The tag of a table entry carries its index. A lookup row (sel = 1) adds
        // its witnessed index, read from the next row, to its bare tag.
        let tag = meta.query_fixed(tag_col_multi_select, Rotation::cur());
        let idx = meta.query_advice(idx_col_multi_select, Rotation::next());
        identities.push((tag.clone() + sel * idx, not_sel * tag));

        identities
    });

    (q_multi_select, tag_col_multi_select)
}

/// Shift separating the table tag from the entry index in the tag cell of
/// the `multi_select` lookup. Lookup indices must be below it, see
/// [`configure_multi_select_lookup`].
pub(crate) const MULTI_SELECT_INDEX_SHIFT: u128 = 1 << 64;

/// What a row of the `multi_select` lookup region is.
pub(crate) enum MultiSelectRow<'a, F: CircuitField> {
    /// A table entry with the given index.
    Table(usize),
    /// A lookup of the entry at the given (assigned) index.
    Lookup(&'a AssignedNative<F>),
}

/// Fills the `multi_select` lookup region of one table entry or one lookup.
///
/// Returns a pair of vectors corresponding to the assigned limbs of the
/// x coordinate and the y coordinate respectively.
///
/// For a lookup, `q_multi_select` is enabled and the values of the coordinate
/// limbs ARE NOT copied, but witnessed freely. It is the responsibility of
/// the caller to further restrict these cells, which are an output of this
/// function. The index must be below [`MULTI_SELECT_INDEX_SHIFT`].
#[allow(clippy::type_complexity, clippy::too_many_arguments)]
pub(crate) fn fill_dynamic_lookup_row<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    x_limbs: &[AssignedNative<F>],
    y_limbs: &[AssignedNative<F>],
    row: MultiSelectRow<'_, F>,
    x_cols: &[Column<Advice>],
    y_cols: &[Column<Advice>],
    tag_col: Column<Fixed>,
    q_multi_select: Selector,
    table_tag: F,
) -> Result<(Vec<AssignedNative<F>>, Vec<AssignedNative<F>>), Error> {
    let shifted_tag = table_tag * F::from_u128(MULTI_SELECT_INDEX_SHIFT);
    layouter.assign_region(
        || "multi_select table",
        |mut region| {
            let mut xs = vec![];
            let mut ys = vec![];
            for i in 0..x_limbs.len() {
                match row {
                    // The limbs of a lookup are not copied into the current row, because
                    // copying imposes restrictions at compile-time (through the permutation
                    // argument). Instead, we want to give freedom to witness any value (from
                    // the table) and we will enforce that it is correct through the lookup.
                    MultiSelectRow::Lookup(_) => {
                        let x_val = x_limbs[i].value().copied();
                        let y_val = y_limbs[i].value().copied();
                        xs.push(region.assign_advice(|| "x", x_cols[i], 0, || x_val)?);
                        ys.push(region.assign_advice(|| "y", y_cols[i], 0, || y_val)?);
                    }
                    MultiSelectRow::Table(_) => {
                        xs.push(x_limbs[i].copy_advice(|| "x", &mut region, x_cols[i], 0)?);
                        ys.push(y_limbs[i].copy_advice(|| "y", &mut region, y_cols[i], 0)?);
                    }
                }
            }
            let tag = match row {
                MultiSelectRow::Table(index) => shifted_tag + F::from(index as u64),
                MultiSelectRow::Lookup(index) => {
                    q_multi_select.enable(&mut region, 0)?;
                    index.copy_advice(|| "index", &mut region, x_cols[0], 1)?;
                    shifted_tag
                }
            };
            region.assign_fixed(|| "assign tag", tag_col, 0, || Value::known(tag))?;

            Ok((xs, ys))
        },
    )
}

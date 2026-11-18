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

//! Range-check chip, asserting that native values lie in ranges `[0, 2^n)` and
//! decomposing them in limbs.
//!
//! Assertions and decompositions are recorded during synthesis and laid out
//! all together when the chip is loaded, which must therefore happen at the end
//! of synthesis.
//!
//! A row has `num_groups` groups, `G` from now on. Each group `k < G` has four
//! lanes `l_{4k}, ..., l_{4k+3}` and an output `out_k`, all advice cells. A
//! row also has the fixed cells `tag`, `tag_msl` (the tag of the most
//! significant lane of every group), a base `b`, and a link `link_k` per group.
//! For `G = 2`:
//!
//! ```text
//!                         advice                          |            fixed
//!           |     group 0     |     group 1     |         |
//!   row r   | l0  l1  l2  l3* | l4  l5  l6  l7* | o0  o1  | tag  tag_msl  b  link0  link1
//!   weight  | 1   b   b^2 b^3 | 1   b   b^2 b^3 |         |
//!   row r+1 |                 |                 | o0'     |
//! ```
//!
//! where `o_k` stands for `out_k`, `o0'` is `out_0` of the next row, and the
//! lanes marked `*` are looked up against `tag_msl`. Every lane is looked up in
//! the table of the pairs `(t, v)` with `0 <= v < 2^t`:
//!
//! ```text
//!   (tag, l_i)      for the first three lanes of every group,
//!   (tag_msl, l_i)  for its last lane,
//! ```
//!
//! and every group `k` enforces
//!
//! ```text
//!   out_k = l_{4k} + b l_{4k+1} + b^2 l_{4k+2} + b^3 l_{4k+3} + link_k * out_{k+1},
//! ```
//!
//! where `out_G` is `out_0` of the next row and `link_k` is 0, or `b^4` to
//! continue the group into the next one. With `T` the chip's `max_bit_len`,
//! range checks are laid out in rows with `b = 2^T`, and decompositions in
//! limbs of `s` bits in rows with `b = 2^s`.
//!
//! For instance, to assert `x < 2^n` with `3T < n <= 4T`, the chip places `x`
//! in the output of a group, and its limbs of `T` bits in the lanes, in a row
//! with `tag = T`, `tag_msl = n - 3T` and `link = 0`. The identity makes the
//! lanes add up to `x`, and the lookups bound the three low lanes to `T` bits
//! and the most significant one to `n - 3T` bits.
//!
//! A value that does not fit in a group spans several linked groups. For
//! instance, to assert `x < 2^(8T)`, the chip places `x` in the output of a
//! first group and `x >> 4T` in the output of a second one, both with
//! `tag = tag_msl = T`, and the limbs of `T` bits of `x` in their lanes: the
//! four least significant ones in the first group, and the others in the
//! second one. The first group has `link = b^4`, so its identity reads
//! `x = l_0 + b l_1 + b^2 l_2 + b^3 l_3 + b^4 (x >> 4T)`, and the second one
//! has `link = 0`. With `G = 2`, both groups take one row; with `G = 1`, they
//! take two consecutive rows, and the first identity reads `o0'`.
//!
//! The first assertion or decomposition places a sentinel row that looks up
//! `(sentinel, 0)`, which the table only contains once the chip is loaded, so a
//! circuit that records assertions but never loads the chip is unsatisfiable.
//!
//! The recorded assertions and decompositions, and whether the sentinel is
//! placed and the chip loaded, are kept in the configuration, so all the chips
//! built on it share them: loading any of them lays out what all of them
//! recorded. A configuration must therefore serve a single synthesis.

mod layout;
mod state;

use std::{
    cell::{RefCell, RefMut},
    rc::Rc,
};

use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use self::{
    layout::{bit_slice, pow2},
    state::{Decomposition, Pending, State},
};
use crate::{
    CircuitField, field::NativeChip, instructions::AssignmentInstructions, types::AssignedNative,
    utils::ComposableChip,
};

/// [RangeCheckChip] configuration, with the columns of the module
/// documentation.
#[derive(Clone, Debug)]
pub struct RangeCheckConfig<F: CircuitField> {
    /// The four lanes of each of the `G` groups.
    lanes: Vec<[Column<Advice>; 4]>,
    /// The `G` outputs.
    outs: Vec<Column<Advice>>,
    /// The tag of the first three lanes of every group.
    tag: Column<Fixed>,
    /// The tag of the last lane of every group.
    tag_msl: Column<Fixed>,
    /// The base `b` of the identities.
    base: Column<Fixed>,
    /// The `G` links.
    links: Vec<Column<Fixed>>,
    /// The selector of the identities and the lookups.
    q_range_check: Selector,
    /// The tags of the lookup table.
    t_tag: TableColumn,
    /// The values of the lookup table.
    t_val: TableColumn,
    /// The largest limb size `T`, set when configuring the chip.
    max_bit_len: usize,
    /// The state shared by all the chips built on this configuration.
    state: Rc<RefCell<State<F>>>,
}

/// [RangeCheckChip] asserts that native values lie in `[0, 2^n)`, and
/// decomposes them in limbs.
///
/// Assertions and decompositions both go through a lookup table with all the
/// pairs `(t, v)` with `0 <= v < 2^t`, for every limb size `t <= max_bit_len`
/// in use.
///
/// The lanes of a decomposition that have no limb are copies of a fixed zero
/// of the underlying [NativeChip]: otherwise, they could take any value of
/// `s` bits, and the limbs would not add up to `x`.
#[derive(Clone, Debug)]
pub struct RangeCheckChip<F: CircuitField> {
    config: RangeCheckConfig<F>,
    native_chip: NativeChip<F>,
}

impl<F: CircuitField> Chip<F> for RangeCheckChip<F> {
    type Config = RangeCheckConfig<F>;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: CircuitField> RangeCheckChip<F> {
    /// Asserts that `x` lies in `[0, 2^n)`.
    ///
    /// With `T` the chip's `max_bit_len`, the chip lays out `x < 2^n` as:
    ///
    /// - one lane of `n` bits, if `n <= T`,
    /// - one group, with three lanes of `T` bits and a most significant one of
    ///   `n - 3T` bits, if `3T < n <= 4T`,
    /// - `n / 4T` linked groups with lanes of `T` bits, if `n` is a multiple of
    ///   `4T`,
    ///
    /// and otherwise splits `x` in limbs with such bounds, see
    /// [RangeCheckChip::decompose].
    ///
    /// The assertion is recorded, and only laid out when the chip is loaded.
    /// If the same element is asserted several times, only the tightest bound
    /// is laid out.
    ///
    /// Returns an error if the chip has already been loaded.
    ///
    /// # Panics
    ///
    /// If `n >= F::NUM_BITS`.
    pub fn assert_lower_than_pow2(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        n: usize,
    ) -> Result<(), Error> {
        assert!(
            n < F::NUM_BITS as usize,
            "RangeCheckChip: cannot assert x < 2^{n}: the field elements have {} bits",
            F::NUM_BITS
        );
        let t = self.config.max_bit_len;
        if !self.is_supported_bound(n) {
            let (mut sizes, mut rest) = (vec![], n);
            while rest > 0 {
                let size = match rest {
                    _ if self.is_supported_bound(rest) => rest,
                    _ if rest < 4 * t => t,
                    _ => 4 * t * (rest / (4 * t)),
                };
                sizes.push(size);
                rest -= size;
            }
            return self.decompose(layouter, x, &sizes).map(|_| ());
        }
        self.assert_not_loaded()?;
        self.place_sentinel_once(layouter)?;
        let pending = &mut *self.pending();
        match pending.index.get(x) {
            Some(&i) => pending.checks[i].1 = pending.checks[i].1.min(n),
            None => {
                pending.index.insert(x.clone(), pending.checks.len());
                pending.checks.push((x.clone(), n));
            }
        }
        Ok(())
    }

    /// Decomposes `x` in limbs of the given bit sizes, in little-endian order,
    /// and returns them: `x = sum_i 2^(s_0 + ... + s_(i-1)) limb_i`.
    ///
    /// Every limb, the most significant one included, is range-checked to its
    /// size. So this also asserts that `x` lies in `[0, 2^(sum_i s_i))`, as
    /// long as `sum_i s_i < F::NUM_BITS`. With more bits, the limbs add up to
    /// `x` modulo the field order, and are not necessarily the canonical
    /// decomposition of `x`.
    ///
    /// Limbs of a common size of at most `max_bit_len` bits are recorded as a
    /// decomposition, and only laid out when the chip is loaded. Other limbs
    /// are constrained to add up to `x` by the underlying [NativeChip], and
    /// range-checked one by one.
    ///
    /// Returns an error if the chip has already been loaded.
    ///
    /// # Panics
    ///
    /// If some size is 0 or not lower than `F::NUM_BITS`.
    pub fn decompose(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        sizes: &[usize],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert!(
            sizes.iter().all(|&s| 0 < s && s < F::NUM_BITS as usize),
            "RangeCheckChip: cannot decompose in limbs of sizes {sizes:?}: the limbs have \
             between 1 and {} bits",
            F::NUM_BITS - 1
        );
        if let Some(&s) = sizes.first()
            && s <= self.config.max_bit_len
            && sizes.iter().all(|&size| size == s)
        {
            self.assert_not_loaded()?;
            self.place_sentinel_once(layouter)?;
            let limbs: Vec<_> = (0..sizes.len())
                .map(|i| AssignedNative::free(bit_slice(x, s * i, Some(s))))
                .collect();
            self.pending().decompositions.push(Decomposition {
                x: x.clone(),
                limbs: limbs.clone(),
                size: s,
            });
            return Ok(limbs);
        }

        let limbs = layouter.assign_region(
            || "decompose",
            |mut region| {
                let mut shift = 0;
                let terms = sizes
                    .iter()
                    .map(|&size| {
                        shift += size;
                        (
                            pow2::<F>(shift - size),
                            bit_slice(x, shift - size, Some(size)),
                        )
                    })
                    .collect::<Vec<_>>();
                let nb_cols = self.native_chip.config().value_cols.len() - 1;
                let (limbs, y) = self.native_chip.assign_linear_combination_aux(
                    &mut region,
                    &terms,
                    F::ZERO,
                    &x.value().copied(),
                    nb_cols,
                    &mut 0,
                )?;
                x.constrain_equal(&mut region, &y)?;
                Ok(limbs)
            },
        )?;
        for (limb, &size) in limbs.iter().zip(sizes) {
            self.assert_lower_than_pow2(layouter, limb, size)?;
        }
        Ok(limbs)
    }

    /// Whether the chip lays out `x < 2^n` directly, see
    /// [RangeCheckChip::assert_lower_than_pow2].
    fn is_supported_bound(&self, n: usize) -> bool {
        is_supported_bound(self.config.max_bit_len, n)
    }
}

impl<F: CircuitField> ComposableChip<F> for RangeCheckChip<F> {
    /// - `5G` advice columns: the `4G` lanes, then the `G` outputs.
    /// - `G + 3` fixed columns: `tag`, `tag_msl`, `base`, then the `G` links.
    /// - `max_bit_len`.
    type SharedResources = (Vec<Column<Advice>>, Vec<Column<Fixed>>, usize);

    type InstructionDeps = NativeChip<F>;

    fn new(config: &RangeCheckConfig<F>, native_chip: &NativeChip<F>) -> Self {
        Self {
            config: config.clone(),
            native_chip: native_chip.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        (advice, fixed, max_bit_len): &Self::SharedResources,
    ) -> RangeCheckConfig<F> {
        let t = *max_bit_len;
        assert!(
            0 < t && t < 64 && 4 * t < F::NUM_BITS as usize,
            "RangeCheckChip: max_bit_len = {t} is out of range"
        );
        assert!(
            !advice.is_empty() && advice.len().is_multiple_of(5),
            "RangeCheckChip: 5 advice columns per group are required, got {}",
            advice.len()
        );
        let num_groups = advice.len() / 5;
        assert_eq!(
            fixed.len(),
            num_groups + 3,
            "RangeCheckChip: {} fixed columns are required for {num_groups} groups",
            num_groups + 3
        );
        let (lanes, outs) = advice.split_at(4 * num_groups);
        let lanes: Vec<[Column<Advice>; 4]> =
            lanes.chunks(4).map(|cols| cols.try_into().unwrap()).collect();
        let (tag, tag_msl, base, links) = (fixed[0], fixed[1], fixed[2], &fixed[3..]);
        advice.iter().for_each(|col| meta.enable_equality(*col));

        let q_range_check = meta.complex_selector();
        let t_tag = meta.lookup_table_column();
        let t_val = meta.lookup_table_column();

        // Every lane `l_i` is looked up as `(tag, l_i)`, or as `(tag_msl, l_i)` for
        // the last lane of its group, in the table of the pairs `(t, v)` with
        // `0 <= v < 2^t`: so `l_i` has at most `tag` (or `tag_msl`) bits.
        meta.batched_lookup("range check", Some(q_range_check), |meta| {
            let tags = (0..4 * num_groups)
                .map(|i| meta.query_fixed(if i % 4 == 3 { tag_msl } else { tag }, Rotation::cur()))
                .collect();
            let vals = (lanes.iter().flatten())
                .map(|col| meta.query_advice(*col, Rotation::cur()))
                .collect();
            vec![(tags, t_tag), (vals, t_val)]
        });

        // Every group `k` enforces the identity of the module documentation:
        //
        //   out_k = l_{4k} + b l_{4k+1} + b^2 l_{4k+2} + b^3 l_{4k+3}
        //         + link_k * out_{k+1},
        //
        // where `out_G` is `out_0` of the next row. The sum of the lanes is
        // computed in Horner form, from the last lane down.
        meta.create_gate("range-check groups", |meta| {
            let b = meta.query_fixed(base, Rotation::cur());
            let ids = (0..num_groups)
                .map(|k| {
                    let sum = (0..4)
                        .rev()
                        .map(|j| meta.query_advice(lanes[k][j], Rotation::cur()))
                        .reduce(|acc, l| acc * b.clone() + l)
                        .unwrap();
                    let next = match outs.get(k + 1) {
                        Some(out) => meta.query_advice(*out, Rotation::cur()),
                        None => meta.query_advice(outs[0], Rotation::next()),
                    };
                    meta.query_advice(outs[k], Rotation::cur())
                        - sum
                        - meta.query_fixed(links[k], Rotation::cur()) * next
                })
                .collect::<Vec<_>>();
            Constraints::with_selector(q_range_check, ids)
        });

        RangeCheckConfig {
            lanes,
            outs: outs.to_vec(),
            tag,
            tag_msl,
            base,
            links: links.to_vec(),
            q_range_check,
            t_tag,
            t_val,
            max_bit_len: t,
            state: Rc::default(),
        }
    }

    /// Lays out all the assertions and decompositions recorded by the chips
    /// built on this configuration.
    ///
    /// Then lays out the lookup table, with the limb sizes in use.
    ///
    /// Loading again, through this chip or another one built on the same
    /// configuration, does nothing.
    ///
    /// Cost model only: the cost model counts the rows of an operation by the
    /// regions laid out between a pair of measurement markers, while the chip
    /// lays out the assertions and decompositions of the operation here, after
    /// the markers. So the assertions and decompositions recorded between the
    /// markers are kept apart, and laid out in a region of their own between
    /// a new pair of markers. Outside of tests, there are none.
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        if std::mem::replace(&mut self.state().loaded, true) {
            return Ok(());
        }
        let zero = self.native_chip.assign_fixed(layouter, F::ZERO)?;
        let (outside, in_window) = {
            let state = self.state();
            let layout = |pending| self.layout(pending, &zero);
            (
                layout(&state.pending),
                layout(&state.pending_in_cost_window),
            )
        };
        self.assign_groups(layouter, &outside)?;

        if !in_window.is_empty() {
            #[cfg(any(test, feature = "testing"))]
            crate::utils::circuit_modeling::cost_measure_start(layouter);
            self.assign_groups(layouter, &in_window)?;
            #[cfg(any(test, feature = "testing"))]
            crate::utils::circuit_modeling::cost_measure_end(layouter);
        }

        let mut tags: Vec<usize> = (outside.keys().chain(in_window.keys()))
            .flat_map(|&(tag, tag_msl, _)| [tag, tag_msl])
            .collect();
        tags.sort_unstable();
        tags.dedup();

        let config = &self.config;
        layouter.assign_table(
            || "range-check table",
            |mut table| {
                let mut assign = |offset: usize, tag: F, val: F| -> Result<(), Error> {
                    table.assign_cell(|| "t_tag", config.t_tag, offset, || Value::known(tag))?;
                    table.assign_cell(|| "t_val", config.t_val, offset, || Value::known(val))?;
                    Ok(())
                };
                assign(0, sentinel_tag::<F>(), F::ZERO)?;
                let mut offset = 1;
                for &tag in tags.iter() {
                    for v in 0..(1u64 << tag) {
                        assign(offset, F::from(tag as u64), F::from(v))?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

impl<F: CircuitField> RangeCheckChip<F> {
    /// Returns an error if the chip has already been loaded.
    ///
    /// Assertions and decompositions recorded after loading would never be
    /// laid out.
    fn assert_not_loaded(&self) -> Result<(), Error> {
        if self.state().loaded {
            return Err(Error::Synthesis(
                "RangeCheckChip: range check recorded after the chip was loaded".into(),
            ));
        }
        Ok(())
    }

    /// The recorded assertions and decompositions: those recorded inside a
    /// cost-model measurement window if synthesis is inside one, and the
    /// others otherwise.
    fn pending(&self) -> RefMut<'_, Pending<F>> {
        RefMut::map(self.state(), |state| match in_cost_window() {
            true => &mut state.pending_in_cost_window,
            false => &mut state.pending,
        })
    }

    /// The state shared by the chips built on this configuration.
    fn state(&self) -> RefMut<'_, State<F>> {
        self.config.state.borrow_mut()
    }

    /// Places the sentinel row, unless it is already placed.
    ///
    /// The sentinel row looks up `(sentinel, 0)` on every lane, which is only
    /// satisfied once the chip is loaded.
    ///
    /// It is placed on the first recording, as it needs a layouter, and as a
    /// chip that records nothing must not need to be loaded.
    fn place_sentinel_once(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        if std::mem::replace(&mut self.state().sentinel_placed, true) {
            return Ok(());
        }
        let config = &self.config;
        layouter.assign_region(
            || "range-check sentinel",
            |mut region| {
                config.q_range_check.enable(&mut region, 0)?;
                for col in config.lanes.iter().flatten().chain(&config.outs) {
                    region.assign_advice(|| "sentinel", *col, 0, || Value::known(F::ZERO))?;
                }
                for col in config.links.iter().chain([&config.base]) {
                    region.assign_fixed(|| "sentinel", *col, 0, || Value::known(F::ZERO))?;
                }
                for col in [config.tag, config.tag_msl] {
                    region.assign_fixed(
                        || "sentinel",
                        col,
                        0,
                        || Value::known(sentinel_tag::<F>()),
                    )?;
                }
                Ok(())
            },
        )
    }
}

/// Whether a chip of the given `max_bit_len` lays out `x < 2^n` directly,
/// see [RangeCheckChip::assert_lower_than_pow2].
pub(crate) fn is_supported_bound(max_bit_len: usize, n: usize) -> bool {
    let t = max_bit_len;
    n <= t || (3 * t < n && n <= 4 * t) || n.is_multiple_of(4 * t)
}

/// The tag of the sentinel row, which differs from every limb size.
fn sentinel_tag<F: CircuitField>() -> F {
    -F::ONE
}

/// Whether synthesis is inside a cost-model measurement window.
fn in_cost_window() -> bool {
    #[cfg(any(test, feature = "testing"))]
    return crate::utils::circuit_modeling::in_cost_measure();
    #[cfg(not(any(test, feature = "testing")))]
    false
}

#[cfg(test)]
mod tests;

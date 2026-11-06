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

//! Range-check chip, asserting that native values lie in ranges `[0, 2^n)`.
//!
//! Assertions are recorded during synthesis and laid out all together when
//! the chip is loaded, which must therefore happen at the end of synthesis.
//!
//! A row has `num_groups` groups of four lanes `l_0, ..., l_{4 num_groups - 1}`
//! and one output per
//! group, `out_1, ..., out_G` (advice), and fixed tags `tag`, `tag_msl` and
//! links `link_1, ..., link_G`. With `T` the chip's `max_bit_len`, every row
//! looks up, in the table of the pairs `(t, v)` with `0 <= v < 2^t`,
//!
//! ```text
//!   (tag, l_i)      for the first three lanes of every group,
//!   (tag_msl, l_i)  for its last lane,
//! ```
//!
//! and enforces, for every group `k`,
//!
//! ```text
//!   out_k = l_{4k} + 2^T l_{4k+1} + 2^{2T} l_{4k+2} + 2^{3T} l_{4k+3} + link_k * out_{k+1},
//! ```
//!
//! where `out_{num_groups + 1}` is `out_1` of the next row and `link_k` is 0 or
//! `2^{4T}`.
//!
//! The chip takes assertions of three sizes, laid out in rows of three kinds:
//!
//! - `n <= T`: short checks, one per lane of a row of `tag = tag_msl = n`,
//!   whose outputs hold the sums of their groups.
//! - `3T < n <= 4T`: one group of a row of `tag = T` and `tag_msl = n - 3T`,
//!   with `x` copied to the group's output.
//! - `n = 4Tj`: `j` linked groups of rows of `tag = tag_msl = T`, continuing on
//!   the next row after the last group of a row, with `x` copied to the output
//!   of the first group and `x >> 4Ti` in the output of the `i`-th one.
//!
//! The first assertion places a sentinel row that looks up `(sentinel, 0)`,
//! which the table only contains once the chip is loaded, so a circuit that
//! records assertions but never loads the chip is unsatisfiable.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap},
    rc::Rc,
};

use midnight_proofs::{
    circuit::{Cell, Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use num_bigint::BigUint;

use crate::{
    CircuitField,
    types::AssignedNative,
    utils::{ComposableChip, util::big_to_fe},
};

/// Range-check chip configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeCheckConfig {
    q_range_check: Selector,
    lanes: Vec<Column<Advice>>,
    outs: Vec<Column<Advice>>,
    tag: Column<Fixed>,
    tag_msl: Column<Fixed>,
    links: Vec<Column<Fixed>>,
    max_bit_len: usize,
    t_tag: TableColumn,
    t_val: TableColumn,
}

/// Assertions recorded and not yet laid out: `(x, n, measured)`, in
/// recording order, where `measured` tells whether the assertion was recorded
/// inside a cost-model measurement window.
#[derive(Debug, Default)]
struct Pending<F: CircuitField> {
    checks: Vec<(AssignedNative<F>, usize, bool)>,
    /// Position in `checks` of the assertion on each cell.
    index: HashMap<Cell, usize>,
    sentinel_placed: bool,
    loaded: bool,
}

/// A cell of a row: a copy of an assigned element, or a new value.
#[derive(Clone, Debug)]
enum Entry<F: CircuitField> {
    Copy(AssignedNative<F>),
    New(Value<F>),
}

impl<F: CircuitField> Entry<F> {
    fn value(&self) -> Value<F> {
        match self {
            Entry::Copy(x) => x.value().copied(),
            Entry::New(v) => *v,
        }
    }
}

/// A group of a row: its lanes, its output, and whether it links to the next
/// group.
#[derive(Clone, Debug)]
struct Group<F: CircuitField> {
    lanes: Vec<Entry<F>>,
    out: Entry<F>,
    link: bool,
}

/// A row of the chip: its tags, lanes, outputs, and which groups link to the
/// next one.
#[derive(Debug)]
struct Row<F: CircuitField> {
    tag: usize,
    tag_msl: usize,
    lanes: Vec<Entry<F>>,
    outs: Vec<Entry<F>>,
    links: Vec<bool>,
}

impl<F: CircuitField> Row<F> {
    fn new(tag: usize, tag_msl: usize, num_groups: usize) -> Self {
        let zero = Entry::New(Value::known(F::ZERO));
        Row {
            tag,
            tag_msl,
            lanes: vec![zero.clone(); 4 * num_groups],
            outs: vec![zero; num_groups],
            links: vec![false; num_groups],
        }
    }
}

/// [RangeCheckChip] asserts that native values lie in `[0, 2^n)`, through a
/// lookup table with all the pairs `(t, v)` with `0 <= v < 2^t`, for every
/// limb size `t <= max_bit_len` in use.
#[derive(Clone, Debug)]
pub struct RangeCheckChip<F: CircuitField> {
    config: RangeCheckConfig,
    pending: Rc<RefCell<Pending<F>>>,
}

impl<F: CircuitField> Chip<F> for RangeCheckChip<F> {
    type Config = RangeCheckConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: CircuitField> ComposableChip<F> for RangeCheckChip<F> {
    /// `5 num_groups` advice columns (the `4 num_groups` lanes, then the
    /// `num_groups` outputs), `num_groups + 2` fixed columns (`tag`, `tag_msl`,
    /// then the `num_groups` links) and `max_bit_len`.
    type SharedResources = (Vec<Column<Advice>>, Vec<Column<Fixed>>, usize);

    type InstructionDeps = ();

    fn new(config: &RangeCheckConfig, _: &()) -> Self {
        Self {
            config: config.clone(),
            pending: Rc::new(RefCell::new(Pending::default())),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        (advice, fixed, max_bit_len): &Self::SharedResources,
    ) -> RangeCheckConfig {
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
            num_groups + 2,
            "RangeCheckChip: {} fixed columns are required for {num_groups} groups",
            num_groups + 2
        );
        let (lanes, outs) = advice.split_at(4 * num_groups);
        let (tag, tag_msl, links) = (fixed[0], fixed[1], &fixed[2..]);
        advice.iter().for_each(|col| meta.enable_equality(*col));

        let q_range_check = meta.complex_selector();
        let t_tag = meta.lookup_table_column();
        let t_val = meta.lookup_table_column();

        meta.batched_lookup("range check", Some(q_range_check), |meta| {
            let tags = (0..4 * num_groups)
                .map(|i| meta.query_fixed(if i % 4 == 3 { tag_msl } else { tag }, Rotation::cur()))
                .collect();
            let vals = lanes.iter().map(|col| meta.query_advice(*col, Rotation::cur())).collect();
            vec![(tags, t_tag), (vals, t_val)]
        });

        meta.create_gate("range-check groups", |meta| {
            let ids = (0..num_groups)
                .map(|k| {
                    let sum = (0..4)
                        .map(|j| {
                            meta.query_advice(lanes[4 * k + j], Rotation::cur()) * pow2::<F>(t * j)
                        })
                        .reduce(|a, b| a + b)
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
            q_range_check,
            lanes: lanes.to_vec(),
            outs: outs.to_vec(),
            tag,
            tag_msl,
            links: links.to_vec(),
            max_bit_len: t,
            t_tag,
            t_val,
        }
    }

    /// Lays out all the recorded assertions and the lookup table.
    ///
    /// Returns an error if the chip has already been loaded.
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let checks = {
            let mut pending = self.pending.borrow_mut();
            if pending.loaded {
                return Err(Error::Synthesis("RangeCheckChip loaded twice".into()));
            }
            pending.loaded = true;
            pending.index.clear();
            std::mem::take(&mut pending.checks)
        };

        let (measured, unmeasured): (Vec<_>, Vec<_>) =
            checks.into_iter().partition(|(_, _, measured)| *measured);
        let (measured, unmeasured) = (self.layout(measured), self.layout(unmeasured));
        let tags: BTreeSet<usize> = (measured.iter().chain(&unmeasured))
            .flat_map(|row| [row.tag, row.tag_msl])
            .collect();

        self.assign_rows(layouter, &unmeasured)?;
        if !measured.is_empty() {
            #[cfg(any(test, feature = "testing"))]
            crate::utils::circuit_modeling::cost_measure_start(layouter);
            self.assign_rows(layouter, &measured)?;
            #[cfg(any(test, feature = "testing"))]
            crate::utils::circuit_modeling::cost_measure_end(layouter);
        }

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
    /// Whether the chip takes assertions of `n` bits: `n <= T`,
    /// `3T < n <= 4T` or `n` a multiple of `4T`, for `T` its `max_bit_len`.
    pub fn fits(&self, n: usize) -> bool {
        let t = self.config.max_bit_len;
        n <= t || (3 * t < n && n <= 4 * t) || n.is_multiple_of(4 * t)
    }

    /// Asserts that `x` lies in `[0, 2^n)`.
    ///
    /// The assertion is recorded and laid out when the chip is loaded. If the
    /// same cell is asserted several times, only the tightest bound is laid
    /// out.
    ///
    /// Returns an error if the chip has already been loaded.
    ///
    /// # Panics
    ///
    /// If the chip does not take assertions of `n` bits, see
    /// [RangeCheckChip::fits], or `n >= F::NUM_BITS`.
    pub fn assert_lower_than_pow2(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        n: usize,
    ) -> Result<(), Error> {
        let t = self.config.max_bit_len;
        assert!(
            self.fits(n) && n < F::NUM_BITS as usize,
            "RangeCheckChip: cannot assert x < 2^{n}: n must be at most {t}, in ({}, {}] or a \
             multiple of {}, and below {}",
            3 * t,
            4 * t,
            4 * t,
            F::NUM_BITS
        );
        if self.pending.borrow().loaded {
            return Err(Error::Synthesis(
                "RangeCheckChip: range check recorded after the chip was loaded".into(),
            ));
        }
        if !self.pending.borrow().sentinel_placed {
            self.place_sentinel(layouter)?;
            self.pending.borrow_mut().sentinel_placed = true;
        }
        let pending = &mut *self.pending.borrow_mut();
        match pending.index.get(&x.cell()) {
            Some(&i) => pending.checks[i].1 = pending.checks[i].1.min(n),
            None => {
                pending.index.insert(x.cell(), pending.checks.len());
                pending.checks.push((x.clone(), n, in_cost_measure()));
            }
        }
        Ok(())
    }

    /// Lays out the given assertions in rows: the values of more than `T`
    /// bits as groups of rows of their `tag_msl`, the ones of `4Tj` bits in
    /// `j` linked groups, and the short checks in rows of their size.
    fn layout(&self, checks: Vec<(AssignedNative<F>, usize, bool)>) -> Vec<Row<F>> {
        let (t, num_groups) = (self.config.max_bit_len, self.config.outs.len());
        let shifted = |x: &AssignedNative<F>, from: usize, len: Option<usize>| -> Value<F> {
            x.value().map(|x| {
                let x = x.to_biguint() >> from;
                big_to_fe(len.map_or(x.clone(), |len| x % (BigUint::from(1u8) << len)))
            })
        };

        let mut groups: BTreeMap<usize, Vec<Group<F>>> = BTreeMap::new();
        let mut shorts: BTreeMap<usize, Vec<AssignedNative<F>>> = BTreeMap::new();
        for (x, n, _) in checks {
            if n <= t {
                shorts.entry(n).or_default().push(x);
                continue;
            }
            let span = n.div_ceil(4 * t);
            let tag_msl = n - 4 * t * (span - 1) - 3 * t;
            for i in 0..span {
                groups.entry(tag_msl).or_default().push(Group {
                    lanes: (0..4)
                        .map(|j| Entry::New(shifted(&x, 4 * t * i + t * j, Some(t))))
                        .collect(),
                    out: match i {
                        0 => Entry::Copy(x.clone()),
                        _ => Entry::New(shifted(&x, 4 * t * i, None)),
                    },
                    link: i + 1 < span,
                });
            }
        }

        let mut rows = vec![];
        for (tag_msl, groups) in groups {
            for chunk in groups.chunks(num_groups) {
                let mut row = Row::new(t, tag_msl, num_groups);
                for (k, group) in chunk.iter().enumerate() {
                    row.lanes[4 * k..4 * k + 4].clone_from_slice(&group.lanes);
                    row.outs[k] = group.out.clone();
                    row.links[k] = group.link;
                }
                rows.push(row);
            }
        }
        for (n, xs) in shorts {
            for chunk in xs.chunks(4 * num_groups) {
                let mut row = Row::new(n, n, num_groups);
                for (lane, x) in row.lanes.iter_mut().zip(chunk) {
                    *lane = Entry::Copy(x.clone());
                }
                for k in 0..num_groups {
                    row.outs[k] = Entry::New((0..4).fold(Value::known(F::ZERO), |sum, j| {
                        sum + row.lanes[4 * k + j].value() * Value::known(pow2::<F>(t * j))
                    }));
                }
                rows.push(row);
            }
        }
        rows
    }

    /// Lays out the given rows in a region of their own.
    fn assign_rows(&self, layouter: &mut impl Layouter<F>, rows: &[Row<F>]) -> Result<(), Error> {
        if rows.is_empty() {
            return Ok(());
        }
        let config = &self.config;
        let link = |linked: bool| {
            if linked {
                pow2::<F>(4 * config.max_bit_len)
            } else {
                F::ZERO
            }
        };
        layouter.assign_region(
            || "range checks",
            |mut region| {
                for (r, row) in rows.iter().enumerate() {
                    config.q_range_check.enable(&mut region, r)?;
                    let cells = (config.lanes.iter().chain(&config.outs))
                        .zip(row.lanes.iter().chain(&row.outs));
                    for (col, entry) in cells {
                        match entry {
                            Entry::Copy(x) => {
                                x.copy_advice(|| "range check", &mut region, *col, r)?
                            }
                            Entry::New(v) => {
                                region.assign_advice(|| "range check", *col, r, || *v)?
                            }
                        };
                    }
                    let tags = [(config.tag, row.tag), (config.tag_msl, row.tag_msl)]
                        .map(|(col, tag)| (col, F::from(tag as u64)));
                    let links =
                        (config.links.iter().zip(&row.links)).map(|(col, l)| (*col, link(*l)));
                    for (col, v) in tags.into_iter().chain(links) {
                        region.assign_fixed(|| "range check", col, r, || Value::known(v))?;
                    }
                }
                Ok(())
            },
        )
    }

    /// Places a sentinel row that looks up `(sentinel, 0)` on every lane,
    /// which is only satisfied once the chip is loaded.
    fn place_sentinel(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let config = &self.config;
        layouter.assign_region(
            || "range-check sentinel",
            |mut region| {
                config.q_range_check.enable(&mut region, 0)?;
                for col in config.lanes.iter().chain(&config.outs) {
                    region.assign_advice(|| "sentinel", *col, 0, || Value::known(F::ZERO))?;
                }
                for col in config.links.iter() {
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

/// `2^k` as a field element.
fn pow2<F: CircuitField>(k: usize) -> F {
    big_to_fe(BigUint::from(1u8) << k)
}

/// The tag of the sentinel row, which differs from every limb size.
fn sentinel_tag<F: CircuitField>() -> F {
    -F::ONE
}

/// Whether synthesis is inside a cost-model measurement window.
fn in_cost_measure() -> bool {
    #[cfg(any(test, feature = "testing"))]
    return crate::utils::circuit_modeling::in_cost_measure();
    #[cfg(not(any(test, feature = "testing")))]
    false
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_curves::Fq as F;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;

    const T: usize = 8;
    const NUM_GROUPS: usize = 2;

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mode {
        Load,
        SkipLoad,
        RecordAfterLoad,
        LoadTwice,
    }

    /// Values with the bounds `n` they are asserted against, in order.
    struct TestCircuit {
        inputs: Vec<(F, Vec<usize>)>,
        mode: Mode,
    }

    impl Circuit<F> for TestCircuit {
        type Config = (RangeCheckConfig, Column<Advice>);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = (0..5 * NUM_GROUPS).map(|_| meta.advice_column()).collect();
            let fixed = (0..NUM_GROUPS + 2).map(|_| meta.fixed_column()).collect();
            let input = meta.advice_column();
            meta.enable_equality(input);
            (RangeCheckChip::configure(meta, &(advice, fixed, T)), input)
        }

        fn synthesize(
            &self,
            (config, input): Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = RangeCheckChip::<F>::new(&config, &());
            let xs = layouter.assign_region(
                || "inputs",
                |mut region| {
                    (self.inputs.iter().enumerate())
                        .map(|(i, (x, _))| {
                            region.assign_advice(|| "x", input, i, || Value::known(*x))
                        })
                        .collect::<Result<Vec<_>, _>>()
                },
            )?;
            let record = |layouter: &mut _| {
                (xs.iter().zip(&self.inputs)).try_for_each(|(x, (_, ns))| {
                    ns.iter().try_for_each(|&n| chip.assert_lower_than_pow2(layouter, x, n))
                })
            };
            match self.mode {
                Mode::Load => record(&mut layouter).and_then(|_| chip.load(&mut layouter)),
                Mode::SkipLoad => record(&mut layouter),
                Mode::RecordAfterLoad => {
                    chip.load(&mut layouter).and_then(|_| record(&mut layouter))
                }
                Mode::LoadTwice => {
                    record(&mut layouter)?;
                    chip.load(&mut layouter).and_then(|_| chip.load(&mut layouter))
                }
            }
        }
    }

    fn satisfied(inputs: Vec<(F, Vec<usize>)>, mode: Mode) -> bool {
        MockProver::run(&TestCircuit { inputs, mode }, vec![])
            .is_ok_and(|prover| prover.verify().is_ok())
    }

    /// Short checks, values of one group with every kind of top limb, and
    /// chains of up to three rows.
    const SIZES: [usize; 9] = [0, 1, 5, 8, 25, 26, 32, 64, 96];

    #[test]
    fn in_range() {
        let inputs = SIZES
            .iter()
            .flat_map(|&n| {
                [
                    (F::ZERO, vec![n]),
                    (pow2::<F>(n) - F::ONE, vec![n]),
                    (F::from((n > 0) as u64), vec![n]),
                ]
            })
            .chain([(pow2::<F>(25) - F::ONE, vec![32, 25]), (F::ZERO, vec![0])])
            .collect();
        assert!(satisfied(inputs, Mode::Load));
    }

    #[test]
    fn out_of_range() {
        for n in SIZES {
            assert!(
                !satisfied(vec![(pow2::<F>(n), vec![n])], Mode::Load),
                "2^{n} < 2^{n}"
            );
        }
        // The tightest of several bounds is enforced.
        assert!(!satisfied(vec![(pow2::<F>(25), vec![32, 25])], Mode::Load));
    }

    #[test]
    fn loading() {
        let inputs = vec![(F::ONE, vec![1])];
        assert!(!satisfied(inputs.clone(), Mode::SkipLoad));
        assert!(!satisfied(inputs.clone(), Mode::RecordAfterLoad));
        assert!(!satisfied(inputs, Mode::LoadTwice));
    }

    #[test]
    #[should_panic(expected = "cannot assert x < 2^9")]
    fn unsupported_size() {
        satisfied(vec![(F::ONE, vec![9])], Mode::Load);
    }
}

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

//! Layout of the recorded assertions and decompositions of a
//! [RangeCheckChip] in groups, and assignment of the groups in rows.

use std::collections::BTreeMap;

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;

use super::{RangeCheckChip, state::Pending};
use crate::{CircuitField, types::AssignedNative, utils::util::big_to_fe};

/// Groups to lay out, by the `(tag, tag_msl, shift)` of their rows.
///
/// The base of the rows is `b = 2^shift`.
pub(super) type Groups<F> = BTreeMap<(usize, usize, usize), Vec<Group<F>>>;

impl<F: CircuitField> RangeCheckChip<F> {
    /// Lays out in groups the given assertions and decompositions.
    ///
    /// With `T` the chip's `max_bit_len`:
    ///
    /// - `n <= T`: four checks per group, with `tag = tag_msl = n`, whose
    ///   output holds the sum of its lanes.
    /// - `3T < n <= 4T`: one group, with `tag = T` and `tag_msl = n - 3T`, and
    ///   `x` as output.
    /// - `n = 4Tj`: `j` linked groups, with `tag = tag_msl = T`, `x` as the
    ///   output of the first one and `x >> 4Ti` as the output of the `i`-th
    ///   one.
    /// - a decomposition in limbs of `s` bits: the limbs in linked groups, with
    ///   `tag = tag_msl = s` and `b = 2^s`, and `x` as the output of the first
    ///   one.
    pub(super) fn layout(&self, pending: &Pending<F>) -> Groups<F> {
        let t = self.config.max_bit_len;
        let zero = || AssignedNative::free(Value::known(F::ZERO));
        let mut groups = Groups::new();
        // The checks with `n <= T`, by `n`, which take a single lane each.
        let mut single_lane: BTreeMap<usize, Vec<AssignedNative<F>>> = BTreeMap::new();
        for &(ref x, n) in &pending.checks {
            if n <= t {
                single_lane.entry(n).or_default().push(x.clone());
                continue;
            }
            let span = n.div_ceil(4 * t);
            let tag_msl = n - 4 * t * (span - 1) - 3 * t;
            for i in 0..span {
                groups.entry((t, tag_msl, t)).or_default().push(Group {
                    lanes: std::array::from_fn(|j| {
                        AssignedNative::free(bit_slice(x, 4 * t * i + t * j, Some(t)))
                    }),
                    out: match i {
                        0 => x.clone(),
                        _ => AssignedNative::free(bit_slice(x, 4 * t * i, None)),
                    },
                    link: (i + 1) < span,
                });
            }
        }

        for (n, xs) in single_lane {
            for chunk in xs.chunks(4) {
                let out = chunk.iter().rev().fold(Value::known(F::ZERO), |acc, x| {
                    acc * Value::known(pow2::<F>(t)) + x.value().copied()
                });
                groups.entry((n, n, t)).or_default().push(Group {
                    lanes: std::array::from_fn(|j| chunk.get(j).cloned().unwrap_or_else(zero)),
                    out: AssignedNative::free(out),
                    link: false,
                });
            }
        }

        for d in &pending.decompositions {
            let (x, limbs, size) = (&d.x, &d.limbs, d.size);
            let span = limbs.len().div_ceil(4);
            for i in 0..span {
                let rest = limbs[4 * i..].iter().rev().fold(Value::known(F::ZERO), |acc, l| {
                    acc * Value::known(pow2::<F>(size)) + l.value().copied()
                });
                groups.entry((size, size, size)).or_default().push(Group {
                    lanes: std::array::from_fn(|j| {
                        limbs.get(4 * i + j).cloned().unwrap_or_else(zero)
                    }),
                    out: match i {
                        0 => x.clone(),
                        _ => AssignedNative::free(rest),
                    },
                    link: (i + 1) < span,
                });
            }
        }
        groups
    }

    /// Lays out the given groups in a region of their own.
    ///
    /// Groups take `G` per row, in rows of their `(tag, tag_msl, shift)`. The
    /// last row of each `(tag, tag_msl, shift)` is padded with zero groups.
    pub(super) fn assign_groups(
        &self,
        layouter: &mut impl Layouter<F>,
        groups: &Groups<F>,
    ) -> Result<(), Error> {
        if groups.is_empty() {
            return Ok(());
        }
        let config = &self.config;
        let num_groups = config.outs.len();
        layouter.assign_region(
            || "range checks",
            |mut region| {
                let mut row = 0;
                for (&(tag, tag_msl, shift), groups) in groups {
                    let padding: Vec<_> = (groups.len()..groups.len().next_multiple_of(num_groups))
                        .map(|_| Group::zero())
                        .collect();
                    for (i, group) in groups.iter().chain(&padding).enumerate() {
                        let (r, k) = (row + i / num_groups, i % num_groups);
                        let cols = config.lanes[k].iter().chain([&config.outs[k]]);
                        for (col, x) in cols.zip(group.lanes.iter().chain([&group.out])) {
                            x.copy_advice(|| "range check", &mut region, *col, r)?;
                        }
                        let link = if group.link {
                            pow2::<F>(4 * shift)
                        } else {
                            F::ZERO
                        };
                        let mut fixed = vec![(config.links[k], link)];
                        if k == 0 {
                            config.q_range_check.enable(&mut region, r)?;
                            fixed.extend([
                                (config.tag, F::from(tag as u64)),
                                (config.tag_msl, F::from(tag_msl as u64)),
                                (config.base, pow2::<F>(shift)),
                            ]);
                        }
                        for (col, v) in fixed {
                            region.assign_fixed(|| "range check", col, r, || Value::known(v))?;
                        }
                    }
                    row += groups.len().div_ceil(num_groups);
                }
                Ok(())
            },
        )
    }
}

/// A group: its four lanes, its output, and whether it links to the next
/// group.
///
/// Elements that are not assigned to a cell yet are assigned to the cells of
/// the group.
#[derive(Debug)]
pub(super) struct Group<F: CircuitField> {
    lanes: [AssignedNative<F>; 4],
    out: AssignedNative<F>,
    link: bool,
}

impl<F: CircuitField> Group<F> {
    /// A group of zeros, not linked to the next group.
    fn zero() -> Self {
        let zero = || AssignedNative::free(Value::known(F::ZERO));
        Group {
            lanes: std::array::from_fn(|_| zero()),
            out: zero(),
            link: false,
        }
    }
}

/// The value of the bits of `x` from position `from` on: `len` of them if
/// given, and all of them otherwise.
pub(super) fn bit_slice<F: CircuitField>(
    x: &AssignedNative<F>,
    from: usize,
    len: Option<usize>,
) -> Value<F> {
    x.value().map(|x| {
        let x = x.to_biguint() >> from;
        big_to_fe(len.map_or(x.clone(), |len| x % (BigUint::from(1u8) << len)))
    })
}

/// `2^k` as a field element.
pub(super) fn pow2<F: CircuitField>(k: usize) -> F {
    big_to_fe(BigUint::from(1u8) << k)
}

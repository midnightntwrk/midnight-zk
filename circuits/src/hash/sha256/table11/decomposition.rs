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

// Define L_spread = { (t, W, W') | W \in [0, 2^t) and W' = spread(W) }
//
// The config uses a lookup to satisfy that (t, W, W') satisfy (t, W, W') \in
// L_spread
//
// The config only needs to verify L_spread for specific bitlengths,
// specifically for t \in {3, 4, 7, 8, 10, 11, 13, 14, 16}. This is because this
// is all that is needed by the sha implementation.
//
// Because we *do not want* a big lookup table, we will satisfy the above
// relation using a small lookup and decomposing the big values that can not fit
// in it. More concretely, given a lookup that contains values of the form
//
// | t_tag | t_dense    | t_spread    |
// |-------|------------|-------------|
// | 0     | 0b0        | 0b0         |
// | 1     | 0b0        | 0b00        |
// | 1     | 0b1        | 0b01        |
// | 2     | 0b00       | 0b0000      |
// | 2     | 0b01       | 0b0001      |
// | 2     | 0b10       | 0b0100      |
// | 2     | 0b11       | 0b0101      |
// | ....  | ......     | ......      |
// | 11    | 0b00...00  | 0b00...00   |
// | 11    | 0b00...01  | 0b00...01   |
// | ....  | ......     | ......      |
// | 11    | 0b11...1   | 0b0101...01 |
//
// The config should look as follows:
//
// | a | a_spread | a_lo | a_hi | a_lo_spread | a_hi_spread |
// |---|----------|------|------|-------------|-------------|
// | W | W'       | Wlo  | Whi  | W'lo        |  W'hi       |
//
// We consider two cases:
//  - (t, W, W') \in Lookup (i.e t \in {3,4,7,8,10,11}). In this case two we
//    just add this to (a_lo, a_lo_spread) *or* (a_hi, a_hi_spread) and verify
//    via the lookup that (t, W, W') \in Table
//  - (t, W, W') \not\in Lookup (i.e t \in {13, 14, 16}). In this case we
//    decompose the word in two limbs and assert
//          1. (t_lo, Wlo, Wlo') \in Table
//          2. (t_hi, Whi, Whi') \in Table
//          3. Wlo + c Whi = W
//          4. W'lo + c' W'hi = W'
//
//      where the values t_lo, t_hi, c, c' are fixed and depend on t.
// Specifically, t is mapped as      follows:
//          - 3     ->   (3,  0)
//          - 7     ->   (7,  0)
//          - 8     ->   (8,  0)
//          - 10    ->   (10, 0)
//          - 11    ->   (11, 0)
//          - 13    ->   (10, 3)
//          - 14    ->   (7,  7)
//          - 16    ->   (8,  8)
//      which is enough to guarantee (t, W, W') \in L_spread
//
// Note that in the first case we can place the claim in either
// (a_lo, a_lo_spread) *or* (a_hi, a_hi_spread) which means we can add two in
// a single row and verify them in parallel, minimizing the total number of
// rows needed. In such cases we will do a "trivial" decomposition, that is,
// we set W = Wlo and W' = W'lo so the row becomes:
//
// | a   | a_spread | a_lo | a_hi | a_lo_spread | a_hi_spread |
// |-----|----------|------|------|-------------|-------------|
// | Wlo | W'lo     | Wlo  | Whi  | W'lo        |  W'hi       |
//
// and we set the constants c = c' = 0. Thus the four relations
//
//  1. (t_lo, Wlo, Wlo') \in Table
//  2. (t_hi, Whi, Whi') \in Table
//  3. Wlo + 0 Whi = Wlo
//  4. W'lo + 0 W'hi = W'lo
//
//  are indeed satisfied
//
//
// An example input that would satisfy the row constraints for t = 13 is:
// W  = 0b0_0_1_0_1_1_0_0_1_1_1_0_1
// W' = 0b00_00_01_00_01_01_00_00_01_01_01_00_01
// Wlo = 0b0_1_1_0_0_1_1_1_0_1
// Whi  = 0b0_0_1
// W'lo = 0b00_01_01_00_00_01_01_01_00_01
// W'hi  = 0b00_00_01
//
// with the values defined by t = 13 being:
// t1 = 10
// t2 = 3
// c = 2^10
// c' = 4^10
//
// An example input that would satisfy the row constraints for t = 3, t = 7 is:
// W  = 0b0_1_1_1_0_0_1
// W'  = 0b00_01_01_01_00_00_01
// W_lo  = 0b0_1_1_1_0_0_1
// W'_lo  = 0b00_01_01_01_00_00_01
// Whi  = 0b1_0_1
// W'hi  = 0b01_00_01
//
// with constants c = c' = 0

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use super::spread_table::PostponedSpreadVar;
use crate::hash::sha256::util::i2lebsp;

// The available bit lengths supported by the lookup
const BIT_LENGTHS: [usize; 7] = [0, 3, 4, 7, 8, 10, 11];

// The max bit length
const MAX_BIT_LENGTH: usize = 11;

// function that given a large lookup tag returns the tags for the two
// decomposed lookups and the constants to recompose the limbs
fn get_constraint_constants(t: u8) -> (u8, u8, u32, u32) {
    // result corresponds to t1, t2, c, c' with
    // t1: low limbs lookup tag
    // t2: hi limbs lookup tag
    // c: dense form constant
    // c': spread form constant
    if t == 13 {
        (10, 3, 1 << 10, 1 << 20)
    } else if t == 14 {
        (7, 7, 1 << 7, 1 << 14)
    } else if t == 16 {
        (8, 8, 1 << 8, 1 << 16)
    } else {
        unreachable!()
    }
}

// a triplet representing a word with its spread form. The dense and spread form
// are represented as unsigned integers
#[derive(Copy, Clone, Debug)]
struct SpreadWordAsUInt {
    tag: Value<u64>,
    dense: Value<u64>,
    spread: Value<u64>,
}

/// A decomposed spread word, with each limb containing the tag, dense, and
/// spread forms.
#[derive(Copy, Clone, Debug)]
struct DecomposedSpreadWord {
    lo: SpreadWordAsUInt,
    hi: SpreadWordAsUInt,
}

/// Returns the integer representation of a little-endian bit-array.
/// We need this new version because we need to not depend on const generics
fn lebs2ip_helper(bits: &[bool]) -> u64 {
    assert!(bits.len() <= 32);
    bits.iter()
        .enumerate()
        .fold(0u64, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
}

/// We implement `From<Box<dyn PostponedSpreadVar>>` for
/// [`DecomposedSpreadWord`]. The boxed type will be the type of "postponed"
/// dense/spread value pairs that need to be checked and the trait
/// implementation will be used to take the corresponding values for the two low
/// and high limbs in order to assign them.
impl From<Box<dyn PostponedSpreadVar>> for DecomposedSpreadWord {
    fn from(value: Box<dyn PostponedSpreadVar>) -> Self {
        let len = value.bit_length();
        let dense = value.dense();
        let spread = value.spread();

        // only these values are accepted for decomposition
        assert!(len == 16 || len == 14 || len == 13);

        // NOTE: It is hard to overcome the type check here. In the `lebs2ip` and
        // `spread` function calls we use the constants 16, 32 respectively
        // which will be enough for all possible LEN <= 16. This is not an issue
        // since we don't do any use of the type system after this call.

        let (t1, t2, _, _) = get_constraint_constants(len as u8);

        let dense_bits = dense.map(i2lebsp::<32>);
        let dense_lo = dense_bits.map(|bits| lebs2ip_helper(&bits[..(t1 as usize)]));
        let dense_hi = dense_bits.map(|bits| lebs2ip_helper(&bits[(t1 as usize)..]));

        let spread_bits = spread.map(i2lebsp::<32>);
        let spread_lo = spread_bits.map(|bits| lebs2ip_helper(&bits[..(2 * t1 as usize)]));
        let spread_hi = spread_bits.map(|bits| lebs2ip_helper(&bits[(2 * t1 as usize)..]));

        // create low-limb word
        let (tag, dense, spread) = (Value::known(t1 as u64), dense_lo, spread_lo);
        let lo = SpreadWordAsUInt { tag, dense, spread };

        // create high-limb word
        let (tag, dense, spread) = (Value::known(t2 as u64), dense_hi, spread_hi);
        let hi = SpreadWordAsUInt { tag, dense, spread };

        DecomposedSpreadWord { lo, hi }
    }
}

#[derive(Clone, Debug)]
struct DecomposedSpreadColumns {
    // columns that contain the spread/dense form of the value to be decomposed
    a: Column<Advice>,
    a_spread: Column<Advice>,
    // columns for the low limbs lookup
    tag_lo: Column<Fixed>,
    a_lo: Column<Advice>,
    a_lo_spread: Column<Advice>,
    // columns for the high limbs lookup
    tag_hi: Column<Fixed>,
    a_hi: Column<Advice>,
    a_hi_spread: Column<Advice>,
    // Fixed columns for the decomposition constants
    c: Column<Fixed>,
    c_prime: Column<Fixed>,
}

#[derive(Clone, Debug)]
// the lookup table columns consisting of tag (=dense bit_length bound), dense
// and spread word
struct SpreadTable {
    tag: TableColumn,
    dense: TableColumn,
    spread: TableColumn,
}

#[derive(Clone, Debug)]
pub struct SpreadTableConfig {
    selector: Selector,
    decomposed: DecomposedSpreadColumns,
    table: SpreadTable,
}

impl SpreadTableConfig {
    /// Given a SpreadVar, it assigns the low and high limbs (in both dense and
    /// spread forms) and assigns the corresponding tags for the lookup
    fn assign_decomposed<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        row: usize,
        word: Box<dyn PostponedSpreadVar>,
    ) -> Result<(), Error> {
        let cols = self.decomposed.clone();
        let selector = self.selector;

        // enable the selector in the row
        selector.enable(region, row)?;

        // get the dense and spread words as u64
        let word_dense = word.dense();
        let word_spread = word.spread();

        // assign and copy-constraint the full dense and spread words
        let dense_new = region.assign_advice(
            || "dense",
            cols.a,
            row,
            || word_dense.map(|dense| F::from(dense)),
        )?;
        let spread_new = region.assign_advice(
            || "spread",
            cols.a_spread,
            row,
            || word_spread.map(|spread| F::from(spread)),
        )?;
        region.constrain_equal(dense_new.cell(), word.assigned_dense_cell())?;
        region.constrain_equal(spread_new.cell(), word.assigned_spread_cell())?;

        // compute and assign low/high limbs
        let limbs = DecomposedSpreadWord::from(word.clone());

        // assign low limbs
        let tag_lo = limbs.lo.tag;
        let dense_lo = limbs.lo.dense;
        let spread_lo = limbs.lo.spread;

        region.assign_fixed(
            || "tag_lo",
            cols.tag_lo,
            row,
            || tag_lo.map(|tag| F::from(tag)),
        )?;
        region.assign_advice(
            || "dense_lo",
            cols.a_lo,
            row,
            || dense_lo.map(|dense| F::from(dense)),
        )?;
        region.assign_advice(
            || "spread_lo",
            cols.a_lo_spread,
            row,
            || spread_lo.map(|spread| F::from(spread)),
        )?;

        // assign high limbs
        let tag_hi = limbs.hi.tag;
        let dense_hi = limbs.hi.dense;
        let spread_hi = limbs.hi.spread;

        region.assign_fixed(
            || "tag_hi",
            cols.tag_hi,
            row,
            || tag_hi.map(|tag| F::from(tag)),
        )?;
        region.assign_advice(
            || "dense_hi",
            cols.a_hi,
            row,
            || dense_hi.map(|dense| F::from(dense)),
        )?;
        region.assign_advice(
            || "spread_hi",
            cols.a_hi_spread,
            row,
            || spread_hi.map(|spread| F::from(spread)),
        )?;

        // assign decomposition constants
        let (_, _, c_val, c_prime_val) = get_constraint_constants(word.bit_length() as u8);
        region.assign_fixed(
            || "Constant for dense decomposition",
            cols.c,
            row,
            || Value::known(F::from(c_val as u64)),
        )?;
        region.assign_fixed(
            || "Constant for spread decomposition",
            cols.c_prime,
            row,
            || Value::known(F::from(c_prime_val as u64)),
        )?;

        Ok(())
    }

    /// Assigns values for checking small spreads. Two small spread checks can
    /// be done in parallel since these values are done by a single lookup
    /// without needed decomposition constraints. The position value defines
    /// if this is the Left or the Right lookup.
    fn assign_small_spread<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        row: usize,
        word: Box<dyn PostponedSpreadVar>,
        position: SpreadPosition,
    ) -> Result<(), Error> {
        let cols = self.decomposed.clone();
        let selector = self.selector;
        // enable the selector
        selector.enable(region, row)?;

        let (tag, word_dense, word_spread) =
            (word.bit_length() as u64, word.dense(), word.spread());

        // copy the lookedup word and assign the appropriate tag
        match position {
            // in this case we assign the pair to (a_lo, a_lo_spread) columns
            SpreadPosition::Left => {
                let dense_new = region.assign_advice(
                    || "small left dense",
                    cols.a_lo,
                    row,
                    || word_dense.map(|v| F::from(v)),
                )?;
                let spread_new = region.assign_advice(
                    || "small left spread",
                    cols.a_lo_spread,
                    row,
                    || word_spread.map(|v| F::from(v)),
                )?;

                region.constrain_equal(dense_new.cell(), word.assigned_dense_cell())?;
                region.constrain_equal(spread_new.cell(), word.assigned_spread_cell())?;

                // assign the lookup tag
                region.assign_fixed(|| "tag", cols.tag_lo, row, || Value::known(F::from(tag)))?;

                // in this case we assign the value also in the a, a_spread columns to satisfy
                // the decomposition constraints. These do not need to be
                // copied, the prover can assign them at will (but only the
                // following assignement will make the circuit satisfy)
                region.assign_advice(
                    || "assign small left dense in a",
                    cols.a,
                    row,
                    || word_dense.map(|dense| F::from(dense)),
                )?;
                region.assign_advice(
                    || "assign small left spread in a_spread",
                    cols.a_spread,
                    row,
                    || word_spread.map(|spread| F::from(spread)),
                )?;
            }
            // in this case we assign the pair to (a_hi, a_hi_spread) columns
            SpreadPosition::Right => {
                let dense_new = region.assign_advice(
                    || "small right dense",
                    cols.a_hi,
                    row,
                    || word_dense.map(|v| F::from(v)),
                )?;
                let spread_new = region.assign_advice(
                    || "small right dense",
                    cols.a_hi_spread,
                    row,
                    || word_spread.map(|v| F::from(v)),
                )?;

                region.constrain_equal(dense_new.cell(), word.assigned_dense_cell())?;
                region.constrain_equal(spread_new.cell(), word.assigned_spread_cell())?;

                region.assign_fixed(|| "tag", cols.tag_hi, row, || Value::known(F::from(tag)))?;
            }
        }

        // assign trivial decomposition constants
        region.assign_fixed(
            || "Trivial constant for dense decomposition",
            cols.c,
            row,
            || Value::known(F::ZERO),
        )?;
        region.assign_fixed(
            || "Trivial constant for spread decomposition",
            cols.c_prime,
            row,
            || Value::known(F::ZERO),
        )?;

        Ok(())
    }

    /// Assigns all postponed values to be checked. It takes as input a region
    /// and a relative offset and assigns it as follows:
    /// 1. assign all the "big" values that need decomposition
    /// 2. assign all the "small" values as pairs to be checked in parallel.
    ///
    /// Concretely, in row offset+i the values `postponed[2*i]`,  `postponed[2*i
    /// + 1]` are checked.
    pub(crate) fn assign_postponed_vector<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        postponed: &[Box<dyn PostponedSpreadVar>],
    ) -> Result<(), Error> {
        // first assign the "big" values which need decomposition
        postponed
            .iter()
            .filter(|x| x.bit_length() > MAX_BIT_LENGTH)
            .enumerate()
            .try_for_each(|(i, postponed)| {
                self.assign_decomposed(region, offset + i, postponed.clone())
            })?;

        // next assign the small values. We do that in pairs, i.e. the odds go to the
        // "Left" positions and the evens to the "Right".

        // the rest of the values
        let postponed_small = postponed
            .iter()
            .filter(|x| x.bit_length() <= MAX_BIT_LENGTH)
            .collect::<Vec<_>>();

        // we start right after the "big" values
        let offset = offset + postponed.len() - postponed_small.len();

        // second assign the "small" values
        (0..(postponed_small.len() / 2)).try_for_each(|i| {
            self.assign_small_spread(
                region,
                offset + i,
                postponed_small[2 * i + 1].clone(),
                SpreadPosition::Left,
            )?;
            self.assign_small_spread(
                region,
                offset + i,
                postponed_small[2 * i].clone(),
                SpreadPosition::Right,
            )
        })?;

        // in case we had an odd number of small values we are left with checking an
        // extra one
        if postponed_small.len() % 2 != 0 {
            let last = *postponed_small.last().unwrap();
            self.assign_small_spread(
                region,
                offset + (postponed_small.len() / 2),
                last.clone(),
                SpreadPosition::Left,
            )?;
        }

        Ok(())
    }
}

/// Enum defining the left/right position for small spread lookups.
/// If only one position is used, it should be the left. Otherwise the circuit
/// becomes unsatisfiable.
enum SpreadPosition {
    Left,
    Right,
}

impl SpreadTableConfig {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        // columns that contain the full value
        a: Column<Advice>,
        a_spread: Column<Advice>,
        // columns for the low limbs lookup
        tag_lo: Column<Fixed>,
        a_lo: Column<Advice>,
        a_lo_spread: Column<Advice>,
        // columns for the high limbs lookup
        tag_hi: Column<Fixed>,
        a_hi: Column<Advice>,
        a_hi_spread: Column<Advice>,
        // Fixed columns for the decomposition constants
        c: Column<Fixed>,
        c_prime: Column<Fixed>,
    ) -> Self {
        // enable equality in all dense/spread pairs since values will be copied in
        // these
        meta.enable_equality(a);
        meta.enable_equality(a_spread);
        meta.enable_equality(a_lo);
        meta.enable_equality(a_lo_spread);
        meta.enable_equality(a_hi);
        meta.enable_equality(a_hi_spread);

        // create table columns
        let table_tag = meta.lookup_table_column();
        let table_dense = meta.lookup_table_column();
        let table_spread = meta.lookup_table_column();

        let selector = meta.complex_selector();

        // low limb lookup
        meta.lookup("lookup low", |meta| {
            let tag_lo = meta.query_fixed(tag_lo, Rotation::cur());
            let dense_lo = meta.query_advice(a_lo, Rotation::cur());
            let spread_lo = meta.query_advice(a_lo_spread, Rotation::cur());

            // note that (0,0,0) is always on the table, so when q is disabled any triplet
            // will satisfy the lookup
            let q = meta.query_selector(selector);

            vec![
                (q.clone() * tag_lo, table_tag),
                (q.clone() * dense_lo, table_dense),
                (q * spread_lo, table_spread),
            ]
        });

        // high limb lookup
        meta.lookup("lookup high", |meta| {
            let tag_hi = meta.query_fixed(tag_hi, Rotation::cur());
            let dense_hi = meta.query_advice(a_hi, Rotation::cur());
            let spread_hi = meta.query_advice(a_hi_spread, Rotation::cur());

            // note that (0,0,0) is always on the table, so when q is disabled any triplet
            // will satisfy the lookup
            let q = meta.query_selector(selector);

            vec![
                (q.clone() * tag_hi, table_tag),
                (q.clone() * dense_hi, table_dense),
                (q * spread_hi, table_spread),
            ]
        });

        // dense and spread decompositions are correct decomposition
        meta.create_gate("dense/spread decomposition", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let a_lo = meta.query_advice(a_lo, Rotation::cur());
            let a_hi = meta.query_advice(a_hi, Rotation::cur());

            let a_spread = meta.query_advice(a_spread, Rotation::cur());
            let a_lo_spread = meta.query_advice(a_lo_spread, Rotation::cur());
            let a_hi_spread = meta.query_advice(a_hi_spread, Rotation::cur());

            let c = meta.query_fixed(c, Rotation::cur());
            let c_prime = meta.query_fixed(c_prime, Rotation::cur());

            let dense = a - (a_lo + c * a_hi);
            let spread = a_spread - (a_lo_spread + c_prime * a_hi_spread);

            Constraints::with_selector(selector, vec![dense, spread])
        });

        let decomposed = DecomposedSpreadColumns {
            a,
            a_spread,
            tag_lo,
            a_lo,
            a_lo_spread,
            tag_hi,
            a_hi,
            a_hi_spread,
            c,
            c_prime,
        };

        SpreadTableConfig {
            decomposed,
            selector,
            table: SpreadTable {
                tag: table_tag,
                dense: table_dense,
                spread: table_spread,
            },
        }
    }

    pub fn load<F: PrimeField>(
        config: SpreadTableConfig,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "spread table",
            |mut table| {
                // We generate the row values lazily (we only need them during keygen).
                let mut rows = SpreadTableConfig::generate::<F>();

                // We don't fully populate the table, but rather only fill the BIT_LENGTHS that
                // we will need. This needs (more than) enough rows to not
                // increase the K and require K = MAX_BIT_LENGTH + 1
                let number_of_rows = BIT_LENGTHS.iter().map(|x| 1 << x).sum();

                for index in 0..number_of_rows {
                    let mut row = None;
                    table.assign_cell(
                        || "tag",
                        config.table.tag,
                        index,
                        || {
                            row = rows.next();
                            Value::known(row.map(|(tag, _, _)| tag).unwrap())
                        },
                    )?;
                    table.assign_cell(
                        || "dense",
                        config.table.dense,
                        index,
                        || Value::known(row.map(|(_, dense, _)| dense).unwrap()),
                    )?;
                    table.assign_cell(
                        || "spread",
                        config.table.spread,
                        index,
                        || Value::known(row.map(|(_, _, spread)| spread).unwrap()),
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl SpreadTableConfig {
    fn generate<F: PrimeField>() -> impl Iterator<Item = (F, F, F)> {
        // create the dense/spread pairs for all needed tags
        let words: Vec<_> = (1..=(1 << MAX_BIT_LENGTH))
            .scan((F::ZERO, F::ZERO), |(dense, spread), i| {
                // We computed this table row in the previous iteration.
                let res = (*dense, *spread);

                *dense += F::ONE;
                if i & 1 == 0 {
                    // On even-numbered rows we recompute the spread.
                    *spread = F::ZERO;
                    for b in 0..MAX_BIT_LENGTH {
                        if (i >> b) & 1 != 0 {
                            *spread += F::from(1 << (2 * b));
                        }
                    }
                } else {
                    // On odd-numbered rows we add one.
                    *spread += F::ONE;
                }

                Some(res)
            })
            .collect();

        let number_of_rows: usize = BIT_LENGTHS.iter().map(|x| 1 << x).sum();
        let mut result: Vec<(F, F, F)> = Vec::with_capacity(number_of_rows);

        // for each length add the appropriate words
        for bit_length in BIT_LENGTHS {
            let tag = F::from(bit_length as u64);
            let rows = &words[0..1 << bit_length]
                .iter()
                .map(|(dense, spread)| (tag, *dense, *spread))
                .collect::<Vec<_>>();
            result.extend_from_slice(rows);
        }
        result.into_iter()
    }
}
#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use halo2curves::pasta::Fp;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use rand::Rng;

    use super::SpreadTableConfig;
    use crate::hash::sha256::{
        table11::spread_table::{PostponedSpreadVar, SpreadVar},
        util::i2lebsp,
        AssignedBits, Bits,
    };

    // The circuit assigns values along with their spread form
    // and checks their correctness. It also check the correctness of small
    // decompositions in parallel.
    struct MyCircuit<
        const B: usize,        // length of word for "big" decompostion
        const S: usize,        // length of spread form of word for "big" decompostion
        const B_SMALL1: usize, // length of word for first small decompostion
        const S_SMALL1: usize, // length of spread form of word for first small decompostion
        const B_SMALL2: usize, // length of word for second small decompostion
        const S_SMALL2: usize, // length of spread form of word for second small decompostion
    > {
        // big values that should be decomposed
        values: Vec<u64>,
        // small values are given in pairs
        small_values: Vec<(u64, u64)>,
    }

    #[derive(Clone, Debug)]
    struct MyCircuitConfig {
        spread_table_config: SpreadTableConfig,
        // the circuit takes two extra advice columns to assign the initial input
        witness_input: (Column<Advice>, Column<Advice>),
    }

    impl<
            F: PrimeField,
            const B: usize,
            const S: usize,
            const B_SMALL1: usize,
            const S_SMALL1: usize,
            const B_SMALL2: usize,
            const S_SMALL2: usize,
        > Circuit<F> for MyCircuit<B, S, B_SMALL1, S_SMALL1, B_SMALL2, S_SMALL2>
    {
        // the circuit takes two extra advice columns to assign the initial input
        type Config = MyCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // columns that contain the full value
            let a = meta.advice_column();
            let a_spread = meta.advice_column();
            // columns for the low limbs lookup
            let tag_lo = meta.fixed_column();
            let a_lo = meta.advice_column();
            let a_lo_spread = meta.advice_column();
            // columns for the high limbs lookup
            let tag_hi = meta.fixed_column();
            let a_hi = meta.advice_column();
            let a_hi_spread = meta.advice_column();
            // Fixed columns for the decomposition constants
            let c = meta.fixed_column();
            let c_prime = meta.fixed_column();

            let spread_table_config = SpreadTableConfig::configure(
                meta,
                a,
                a_spread,
                tag_lo,
                a_lo,
                a_lo_spread,
                tag_hi,
                a_hi,
                a_hi_spread,
                c,
                c_prime,
            );

            let input_dense = meta.advice_column();
            let input_spread = meta.advice_column();

            meta.enable_equality(input_dense);
            meta.enable_equality(input_spread);

            let witness_input = (input_dense, input_spread);

            MyCircuitConfig {
                spread_table_config,
                witness_input,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // load the lookup table
            SpreadTableConfig::load(config.spread_table_config.clone(), &mut layouter)?;

            // region to assign all "big" inputs
            let assigned_inputs = layouter.assign_region(
                || "assign_input",
                |mut region| {
                    let mut row = 0;
                    let mut assign_input_value = |input: u64| -> Result<SpreadVar<B, S, F>, Error> {
                        let dense_input_col = config.witness_input.0;
                        let spread_input_col = config.witness_input.1;

                        let dense_bits: Bits<B> = Bits::from(i2lebsp(input));
                        let spread_bits: Bits<S> = dense_bits.spread().into();

                        let assigned_dense = region.assign_advice(
                            || "assign dense input",
                            dense_input_col,
                            row,
                            || Value::known(dense_bits.clone()),
                        )?;

                        let assigned_spread = region.assign_advice(
                            || "assign spread input",
                            spread_input_col,
                            row,
                            || Value::known(spread_bits.clone()),
                        )?;

                        row += 1;
                        let spread_var = SpreadVar {
                            dense: AssignedBits(assigned_dense),
                            spread: AssignedBits(assigned_spread),
                        };
                        Ok(spread_var)
                    };

                    self.values
                        .iter()
                        .map(|v| assign_input_value(*v))
                        .collect::<Result<Vec<_>, _>>()
                },
            )?;

            let assigned_small_inputs = layouter.assign_region(
                || "assign_small_input",
                |mut region| {
                    let mut row = 0;
                    let mut assign_input_value = |(input1, input2): (u64, u64)| -> Result<
                        (
                            SpreadVar<B_SMALL1, S_SMALL1, F>,
                            SpreadVar<B_SMALL2, S_SMALL2, F>,
                        ),
                        Error,
                    > {
                        let dense_input_col = config.witness_input.0;
                        let spread_input_col = config.witness_input.1;

                        let dense_bits: Bits<B_SMALL1> = Bits::from(i2lebsp(input1));
                        let spread_bits: Bits<S_SMALL1> = dense_bits.spread().into();

                        let assigned_dense = region.assign_advice(
                            || "assign small dense input",
                            dense_input_col,
                            row,
                            || Value::known(dense_bits.clone()),
                        )?;

                        let assigned_spread = region.assign_advice(
                            || "assign small spread input",
                            spread_input_col,
                            row,
                            || Value::known(spread_bits.clone()),
                        )?;

                        let spread_var1 = SpreadVar {
                            dense: AssignedBits(assigned_dense),
                            spread: AssignedBits(assigned_spread),
                        };

                        row += 1;

                        let dense_bits: Bits<B_SMALL2> = Bits::from(i2lebsp(input2));
                        let spread_bits: Bits<S_SMALL2> = dense_bits.spread().into();

                        let assigned_dense = region.assign_advice(
                            || "assign small dense input",
                            dense_input_col,
                            row,
                            || Value::known(dense_bits.clone()),
                        )?;

                        let assigned_spread = region.assign_advice(
                            || "assign small spread input",
                            spread_input_col,
                            row,
                            || Value::known(spread_bits.clone()),
                        )?;

                        let spread_var2 = SpreadVar {
                            dense: AssignedBits(assigned_dense),
                            spread: AssignedBits(assigned_spread),
                        };

                        row += 1;

                        Ok((spread_var1, spread_var2))
                    };

                    self.small_values
                        .iter()
                        .map(|v| assign_input_value(*v))
                        .collect::<Result<Vec<_>, _>>()
                },
            )?;

            // collect all the values that need to be checked
            let mut postponed: Vec<Box<dyn PostponedSpreadVar>> = Vec::new();
            for input in assigned_inputs {
                postponed.push(Box::new(input.clone()));
            }

            for input in assigned_small_inputs {
                postponed.push(Box::new(input.0.clone()));
                postponed.push(Box::new(input.1.clone()));
            }

            layouter.assign_region(
                || "flush postponed spread",
                |mut region| {
                    config
                        .spread_table_config
                        .assign_postponed_vector(&mut region, 0, &postponed)
                },
            )?;

            Ok(())
        }
    }

    fn decomposed_spread_helper<
        const B: usize,
        const S: usize,
        const B_SMALL1: usize,
        const S_SMALL1: usize,
        const B_SMALL2: usize,
        const S_SMALL2: usize,
    >() {
        const INSTANCES_NUMBER: usize = 200;

        let mut rng = rand::thread_rng();

        let values = (0..INSTANCES_NUMBER)
            .map(|_| rng.gen_range(0..(1 << B)))
            .collect::<Vec<_>>();
        let small_values = (0..(INSTANCES_NUMBER))
            .map(|_| {
                (
                    rng.gen_range(0..(1 << B_SMALL1)),
                    rng.gen_range(0..(1 << B_SMALL2)),
                )
            })
            .collect::<Vec<_>>();
        let circuit: MyCircuit<B, S, B_SMALL1, S_SMALL1, B_SMALL2, S_SMALL2> = MyCircuit {
            values: values.clone(),
            small_values: small_values.clone(),
        };
        let prover = match MockProver::<Fp>::run(12, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn decomposed_spread() {
        // we run some combinations
        // BIG: 13, SMALL: 8, 10
        decomposed_spread_helper::<13, 26, 8, 16, 10, 20>();
        // BIG: 13, SMALL: 7, 11
        decomposed_spread_helper::<13, 26, 7, 14, 11, 22>();
        // BIG: 14, SMALL: 10, 10
        decomposed_spread_helper::<14, 28, 10, 20, 10, 20>();
        // BIG: 14, SMALL: 7, 11
        decomposed_spread_helper::<14, 28, 7, 14, 11, 22>();
        // BIG: 16, SMALL: 11, 3
        decomposed_spread_helper::<16, 32, 11, 22, 3, 6>();
    }
}

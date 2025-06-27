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

//! `pow2range` is a chip for performing membership assertions in ranges of the
//! form [0, 2^n) via lookups.

use std::{fmt::Debug, marker::PhantomData};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use crate::{instructions::decomposition::Pow2RangeInstructions, types::AssignedNative};

/// Number of pow2range check lookup columns enabled.
pub const NB_POW2RANGE_COLS: usize = 4;

/// Pow2Range gate configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pow2RangeConfig {
    pub(crate) q_pow2range: Selector,
    pub(crate) tag_col: Column<Fixed>,
    /// The columns where the range-checked values are placed.
    pub(crate) val_cols: [Column<Advice>; NB_POW2RANGE_COLS],
    t_tag: TableColumn,
    t_val: TableColumn,
}

/// [Pow2RangeChip] applies membership assertions in ranges of the form [0,
/// 2^n), for n = 0..=max_bit_len, through a lookup table of the following form
/// (where N := max_bit_len):
//    |  tag  |  value  |
//    |-------|---------|
//    |   0   |    0    |
//    |   1   |    0    |
//    |   1   |    1    |
//    |   2   |    0    |
//    |   2   |    1    |
//    |   2   |    2    |
//    |   2   |    3    |
//    |   3   |    0    |
//    |  ...  |   ...   |
//    |   N   |    0    |
//    |   N   |    1    |
//    |  ...  |   ...   |
//    |   N   | 2^N - 1 |
/// There exist `NB_POW2RANGE_COLS` columns designated for the lookup. If the
/// lookup is enabled, the values in those columns will be asserted to be in the
/// range [0, 2^tag), where tag is the value of the tag column at the relevant
/// offset. Note that if the lookup is enabled, all lookup columns are
/// range-checked in the same range. It is not possible range-check only some of
/// them. However, different rows may assert different ranges (specified by the
/// tag).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pow2RangeChip<F: PrimeField> {
    config: Pow2RangeConfig,
    max_bit_len: usize,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Chip<F> for Pow2RangeChip<F> {
    type Config = Pow2RangeConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> Pow2RangeChip<F> {
    pub(crate) fn assert_row_lower_than_2_pow_n(
        &self,
        region: &mut Region<'_, F>,
        n: usize,
    ) -> Result<(), Error> {
        if n > self.max_bit_len {
            panic!(
                "assert_row_lower_than_2_pow_n: n={} cannot exceed max_bit_len={}",
                n, self.max_bit_len
            )
        }
        self.config.q_pow2range.enable(region, 0)?;
        region.assign_fixed(
            || "pow2range_tag",
            self.config.tag_col,
            0,
            || Value::known(F::from(n as u64)),
        )?;
        Ok(())
    }
}

impl<F: PrimeField> Pow2RangeInstructions<F> for Pow2RangeChip<F> {
    fn assert_values_lower_than_2_pow_n(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[AssignedNative<F>],
        n: usize,
    ) -> Result<(), Error> {
        for chunk in values.chunks(NB_POW2RANGE_COLS) {
            layouter.assign_region(
                || "Assign values",
                |mut region| {
                    // Assign the chunk of values at the current offset.
                    for (assigned, col) in chunk.iter().zip(self.config.val_cols.iter()) {
                        let x = region.assign_advice(
                            || "pow2range val",
                            *col,
                            0,
                            || assigned.value().copied(),
                        )?;
                        region.constrain_equal(x.cell(), assigned.cell())?
                    }
                    // Assign zeros in the unassigned lookup columns in case |chunk| <
                    // NB_POW2RANGE_COLS.
                    for i in chunk.len()..NB_POW2RANGE_COLS {
                        region.assign_advice(
                            || "pow2range zero",
                            self.config.val_cols[i],
                            0,
                            || Value::known(F::ZERO),
                        )?;
                    }
                    self.assert_row_lower_than_2_pow_n(&mut region, n)
                },
            )?;
        }
        Ok(())
    }
}

impl<F: PrimeField> Pow2RangeChip<F> {
    /// Creates a new Pow2RangeChip given the corresponding configuration and a
    /// given `max_bit_len`.
    pub fn new(config: &Pow2RangeConfig, max_bit_len: usize) -> Self {
        Self {
            config: config.clone(),
            max_bit_len,
            _marker: PhantomData,
        }
    }

    /// Returns the max_bit_len of the chip
    pub fn max_bit_len(&self) -> usize {
        self.max_bit_len
    }

    /// Creates a Pow2RangeConfig given a constraint system and a set of
    /// available advice columns.
    ///
    /// # Panics
    ///
    /// If the number of provided columns is smaller than `NB_POW2RANGE_COLS`.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        columns: &[Column<Advice>],
    ) -> Pow2RangeConfig {
        let val_cols: [Column<Advice>; NB_POW2RANGE_COLS] =
            columns[..NB_POW2RANGE_COLS].try_into().unwrap();

        let q_pow2range = meta.complex_selector();
        let tag_col = meta.fixed_column();
        let t_tag = meta.lookup_table_column();
        let t_val = meta.lookup_table_column();

        for val_col in val_cols {
            meta.lookup("pow2range column check", |meta| {
                let sel = meta.query_selector(q_pow2range);
                let tag = meta.query_fixed(tag_col, Rotation::cur());
                let val = meta.query_advice(val_col, Rotation::cur());
                vec![(tag, t_tag), (sel * val, t_val)]
            });
        }

        Pow2RangeConfig {
            q_pow2range,
            tag_col,
            val_cols,
            t_tag,
            t_val,
        }
    }

    /// Load the pow2range lookup table (to be used in synthesis).
    pub fn load_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "pow2range table",
            |mut table| {
                let mut offset = 0;
                for bit_len in 0..=self.max_bit_len {
                    let tag = Value::known(F::from(bit_len as u64));
                    for value in 0..(1 << bit_len) {
                        let val = Value::known(F::from(value));
                        table.assign_cell(|| "t_tag", self.config.t_tag, offset, || tag)?;
                        table.assign_cell(|| "t_val", self.config.t_val, offset, || val)?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use pasta_curves::Fp;
    use rand::Rng;

    use super::*;

    struct TestCircuit<F: PrimeField> {
        inputs: Vec<([u64; NB_POW2RANGE_COLS], usize)>, // (values, bit_len)
        max_bit_len: usize,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
        type Config = Pow2RangeConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: vec![],
                max_bit_len: 0,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let columns = (0..NB_POW2RANGE_COLS)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>();
            Pow2RangeChip::configure(meta, &columns)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let pow2range_chip = Pow2RangeChip::<F>::new(&config, self.max_bit_len);
            pow2range_chip.load_table(&mut layouter)?;
            layouter.assign_region(
                || "pow2range test",
                |mut region| {
                    for (offset, input) in self.inputs.iter().enumerate() {
                        for i in 0..NB_POW2RANGE_COLS {
                            let col = pow2range_chip.config.val_cols[i];
                            let val = Value::known(F::from(input.0[i]));
                            region.assign_advice(|| "pow2range val", col, offset, || val)?;
                        }
                        pow2range_chip.assert_row_lower_than_2_pow_n(&mut region, input.1)?;
                    }

                    Ok(())
                },
            )
        }
    }

    #[test]
    fn test_pow2range() {
        const MAX_BIT_LEN: usize = 10;
        // FIXME: Ideally k should be (MAX_BIT_LEN + 1), this is currently not possible
        // because there seem to be 6 unusable rows for the ZK adjustment.
        let k = (MAX_BIT_LEN + 2) as u32;
        let mut rng = rand::thread_rng();

        let inputs = (0..MAX_BIT_LEN)
            .map(|n| {
                let mut values = [0u64; NB_POW2RANGE_COLS];
                values[0] = (1 << n) - 1;
                for value in values.iter_mut().skip(1) {
                    *value = rng.gen_range(0..(1 << n));
                }
                (values, n)
            })
            .collect::<Vec<_>>();

        let circuit = TestCircuit::<Fp> {
            inputs,
            max_bit_len: MAX_BIT_LEN,
            _marker: PhantomData,
        };

        let public_inputs = vec![];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_pow2range_negative() {
        const MAX_BIT_LEN: usize = 10;
        // FIXME: Ideally k should be (MAX_BIT_LEN + 1), this is currently not possible
        // because there seem to be 6 unusable rows for the ZK adjustment.
        let k = (MAX_BIT_LEN + 2) as u32;

        (0..MAX_BIT_LEN).for_each(|n| {
            let mut values = [0u64; NB_POW2RANGE_COLS];
            // Set the i-th position to 2^n to make the circuit fail.
            // We vary i to check that the assertion works in all enabled columns.
            let i = n % NB_POW2RANGE_COLS;
            values[i] = 1 << n;

            let circuit = TestCircuit::<Fp> {
                inputs: vec![(values, n)],
                max_bit_len: MAX_BIT_LEN,
                _marker: PhantomData,
            };

            let public_inputs = vec![];
            let prover = match MockProver::run(k, &circuit, public_inputs) {
                Ok(prover) => prover,
                Err(e) => panic!("{e:#?}"),
            };

            assert!(prover.verify() != Ok(()));
        })
    }
}

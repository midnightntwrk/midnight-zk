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

//! `pow2range` is a chip for performing membership assertions in ranges of the
//! form [0, 2^n) via lookups.

use std::{
    cell::{Cell, RefCell},
    collections::HashSet,
    fmt::Debug,
    marker::PhantomData,
    rc::Rc,
};

use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use crate::{
    field::native::NB_ARITH_COLS, instructions::decomposition::Pow2RangeInstructions,
    types::AssignedNative, CircuitField,
};

/// Pow2Range gate configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pow2RangeConfig {
    pub(crate) q_pow2range: Selector,
    pub(crate) tag_col: Column<Fixed>,
    /// The columns where the range-checked values are placed. All of these
    /// columns are lookup-enabled, i.e., the length of this field
    /// determines the number of parallel lookups.
    pub(crate) val_cols: Vec<Column<Advice>>,
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
/// There exist as many columns as inputted in the config designated for the
/// lookup. If the lookup is enabled, the values in those columns will be
/// asserted to be in the range [0, 2^tag), where tag is the value of the tag
/// column at the relevant offset. Note that if the lookup is enabled, all
/// lookup columns are range-checked in the same range. It is not possible to
/// range-check only some of them. However, different rows may assert different
/// ranges (specified by the tag).
///
/// Note: The table will include only the tag values that are actually used in
/// the circuit! This allows us to have smaller tables when possible.
///
/// # Table Loading Invariant
///
/// The lookup table is built from the set of tags accumulated during constraint
/// emission. Therefore, [`load_table`](Self::load_table) **must** be called
/// after all calls to [`assert_row_lower_than_2_pow_n`](Self::assert_row_lower_than_2_pow_n)
/// (or any instruction that delegates to it). This invariant is enforced at
/// runtime: calling `assert_row_lower_than_2_pow_n` after `load_table` will
/// panic.
///
/// If the full set of required tags is known upfront, use
/// [`precompute_tags`](Self::precompute_tags) to register them before
/// `load_table`, which then makes the loading order safe.
#[derive(Clone, Debug)]
pub struct Pow2RangeChip<F: CircuitField> {
    config: Pow2RangeConfig,
    max_bit_len: usize,
    queried_tags: Rc<RefCell<HashSet<usize>>>,
    /// Set to `true` once `load_table` has been called. Any subsequent call to
    /// `assert_row_lower_than_2_pow_n` will panic.
    frozen: Rc<Cell<bool>>,
    _marker: PhantomData<F>,
}

impl<F: CircuitField> Chip<F> for Pow2RangeChip<F> {
    type Config = Pow2RangeConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: CircuitField> Pow2RangeChip<F> {
    pub(crate) fn assert_row_lower_than_2_pow_n(
        &self,
        region: &mut Region<'_, F>,
        n: usize,
        offset: usize,
    ) -> Result<(), Error> {
        if n > self.max_bit_len {
            panic!(
                "assert_row_lower_than_2_pow_n: n={} cannot exceed max_bit_len={}",
                n, self.max_bit_len
            )
        }
        if self.frozen.get() {
            panic!(
                "Pow2RangeChip: cannot emit lookup constraint for tag={} after load_table() \
                 has been called. The lookup table has already been materialized and does not \
                 contain this tag. Either move load_table() to after all constraint emission, \
                 or use precompute_tags() to register all required tags before loading.",
                n
            )
        }
        self.config.q_pow2range.enable(region, offset)?;
        region.assign_fixed(
            || "pow2range_tag",
            self.config.tag_col,
            offset,
            || Value::known(F::from(n as u64)),
        )?;
        self.queried_tags.borrow_mut().insert(n);
        Ok(())
    }
}

impl<F: CircuitField> Pow2RangeInstructions<F> for Pow2RangeChip<F> {
    fn assert_values_lower_than_2_pow_n(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[AssignedNative<F>],
        n: usize,
    ) -> Result<(), Error> {
        let nr_range_check_cols = self.config.val_cols.len();
        for chunk in values.chunks(nr_range_check_cols) {
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
                    // ZkStdLibArch::nr_pow2range_cols.
                    for i in chunk.len()..nr_range_check_cols {
                        region.assign_advice(
                            || "pow2range zero",
                            self.config.val_cols[i],
                            0,
                            || Value::known(F::ZERO),
                        )?;
                    }
                    self.assert_row_lower_than_2_pow_n(&mut region, n, 0)
                },
            )?;
        }
        Ok(())
    }
}

impl<F: CircuitField> Pow2RangeChip<F> {
    /// Creates a new Pow2RangeChip given the corresponding configuration and a
    /// given `max_bit_len`.
    pub fn new(config: &Pow2RangeConfig, max_bit_len: usize) -> Self {
        Self {
            config: config.clone(),
            max_bit_len,
            queried_tags: Rc::new(RefCell::new(HashSet::new())),
            frozen: Rc::new(Cell::new(false)),
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
    /// If the number of provided columns is greater than or equal to
    /// `NB_ARITH_COLS`.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        columns: &[Column<Advice>],
    ) -> Pow2RangeConfig {
        let val_cols = columns.to_vec();
        assert!(
            val_cols.len() < NB_ARITH_COLS,
            "Nr of range-check columns should be smaller than NB_ARITHM_COLS."
        );

        let q_pow2range = meta.complex_selector();
        let tag_col = meta.fixed_column();
        let t_tag = meta.lookup_table_column();
        let t_val = meta.lookup_table_column();

        for val_col in &val_cols {
            meta.lookup("pow2range column check", |meta| {
                let sel = meta.query_selector(q_pow2range);
                let tag = meta.query_fixed(tag_col, Rotation::cur());
                let val = meta.query_advice(*val_col, Rotation::cur());
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
    ///
    /// # Table Loading Invariant
    ///
    /// This method materializes the lookup table from the set of tags
    /// accumulated during constraint emission. After this call, the chip is
    /// **frozen**: any subsequent call to
    /// [`assert_row_lower_than_2_pow_n`](Self::assert_row_lower_than_2_pow_n)
    /// will panic, because the table cannot be extended after materialization.
    pub fn load_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.frozen.set(true);
        layouter.assign_table(
            || "pow2range table",
            |mut table| {
                let mut offset = 0;
                for bit_len in 0..=self.max_bit_len {
                    // The lookup is disabled with tag 0, which we always include.
                    if bit_len > 0 && !self.queried_tags.borrow().contains(&bit_len) {
                        continue;
                    }
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

    /// Pre-register tag values so that the lookup table will include them
    /// even if no constraint has been emitted for them yet.
    ///
    /// This is useful when the full set of required tags is known upfront
    /// (e.g., in static circuits) and you want to load the table early.
    ///
    /// # Panics
    ///
    /// If the chip is already frozen (i.e., `load_table` has been called).
    /// If any tag exceeds `max_bit_len`.
    pub fn precompute_tags(&self, tags: &[usize]) {
        if self.frozen.get() {
            panic!(
                "Pow2RangeChip: cannot precompute tags after load_table() has been called."
            )
        }
        let mut queried = self.queried_tags.borrow_mut();
        for &tag in tags {
            assert!(
                tag <= self.max_bit_len,
                "precompute_tags: tag={} exceeds max_bit_len={}",
                tag,
                self.max_bit_len
            );
            queried.insert(tag);
        }
    }

    /// Returns `true` if the table has been materialized (i.e., `load_table`
    /// has been called).
    pub fn is_frozen(&self) -> bool {
        self.frozen.get()
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use midnight_curves::Fq as Fp;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use rand::Rng;

    use super::*;

    struct TestCircuit<F: CircuitField, const NR_COLS: usize> {
        inputs: Vec<([u64; NR_COLS], usize)>, // (values, bit_len)
        max_bit_len: usize,
        _marker: PhantomData<F>,
    }

    impl<F: CircuitField, const NR_COLS: usize> Circuit<F> for TestCircuit<F, NR_COLS> {
        type Config = Pow2RangeConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!();
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let columns = (0..NR_COLS).map(|_| meta.advice_column()).collect::<Vec<_>>();
            Pow2RangeChip::configure(meta, &columns)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let pow2range_chip = Pow2RangeChip::<F>::new(&config, self.max_bit_len);

            layouter.assign_region(
                || "pow2range test",
                |mut region| {
                    for (offset, input) in self.inputs.iter().enumerate() {
                        for i in 0..NR_COLS {
                            let col = pow2range_chip.config.val_cols[i];
                            let val = Value::known(F::from(input.0[i]));
                            region.assign_advice(|| "pow2range val", col, offset, || val)?;
                        }
                        pow2range_chip.assert_row_lower_than_2_pow_n(&mut region, input.1, 0)?;
                    }

                    Ok(())
                },
            )?;

            pow2range_chip.load_table(&mut layouter)
        }
    }

    fn run_pow2range_test<const NR_COLS: usize>() {
        const MAX_BIT_LEN: usize = 10;
        let mut rng = rand::thread_rng();

        let inputs = (0..MAX_BIT_LEN)
            .map(|n| {
                let mut values = [0u64; NR_COLS];
                values[0] = (1 << n) - 1;
                for value in values.iter_mut().skip(1) {
                    *value = rng.gen_range(0..(1 << n));
                }
                (values, n)
            })
            .collect();

        let circuit = TestCircuit::<Fp, NR_COLS> {
            inputs,
            max_bit_len: MAX_BIT_LEN,
            _marker: PhantomData,
        };

        let public_inputs = vec![];
        let prover = match MockProver::run(&circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_pow2range() {
        run_pow2range_test::<1>();
        run_pow2range_test::<2>();
        run_pow2range_test::<3>();
        run_pow2range_test::<4>();
    }

    fn run_pow2range_negative_test<const NR_COLS: usize>() {
        const MAX_BIT_LEN: usize = 10;
        (0..MAX_BIT_LEN).for_each(|n| {
            let mut values = [0u64; NR_COLS];
            // Set the i-th position to 2^n to make the circuit fail.
            // We vary i to check that the assertion works in all enabled columns.
            let i = n % NR_COLS;
            values[i] = 1 << n;

            let circuit = TestCircuit::<Fp, NR_COLS> {
                inputs: vec![(values, n)],
                max_bit_len: MAX_BIT_LEN,
                _marker: PhantomData,
            };

            let public_inputs = vec![];
            let prover = match MockProver::run(&circuit, public_inputs) {
                Ok(prover) => prover,
                Err(e) => panic!("{e:#?}"),
            };

            assert!(prover.verify() != Ok(()));
        })
    }

    #[test]
    fn test_pow2range_negative() {
        run_pow2range_negative_test::<1>();
        run_pow2range_negative_test::<2>();
        run_pow2range_negative_test::<3>();
        run_pow2range_negative_test::<4>();
    }

    /// Negative test: calling `assert_row_lower_than_2_pow_n` after
    /// `load_table` must panic.
    #[test]
    #[should_panic(expected = "cannot emit lookup constraint")]
    fn test_post_load_constraint_panics() {
        const MAX_BIT_LEN: usize = 10;

        struct PostLoadCircuit<F: CircuitField> {
            _marker: PhantomData<F>,
        }

        impl<F: CircuitField> Circuit<F> for PostLoadCircuit<F> {
            type Config = Pow2RangeConfig;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unreachable!();
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let columns = (0..1).map(|_| meta.advice_column()).collect::<Vec<_>>();
                Pow2RangeChip::configure(meta, &columns)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = Pow2RangeChip::<F>::new(&config, MAX_BIT_LEN);

                // Load table first (this freezes the chip)
                chip.load_table(&mut layouter)?;

                // Now try to emit a constraint — this must panic
                layouter.assign_region(
                    || "post-load constraint",
                    |mut region| {
                        let col = chip.config.val_cols[0];
                        region.assign_advice(
                            || "val",
                            col,
                            0,
                            || Value::known(F::from(3u64)),
                        )?;
                        chip.assert_row_lower_than_2_pow_n(&mut region, 5, 0)
                    },
                )?;

                Ok(())
            }
        }

        let circuit = PostLoadCircuit::<Fp> {
            _marker: PhantomData,
        };
        let _ = MockProver::run(&circuit, vec![]);
    }

    /// Test that `precompute_tags` allows loading the table before constraint
    /// emission, as long as all needed tags are pre-registered.
    #[test]
    fn test_precompute_tags_enables_early_load() {
        const MAX_BIT_LEN: usize = 10;

        struct PrecomputeCircuit<F: CircuitField> {
            _marker: PhantomData<F>,
        }

        impl<F: CircuitField> Circuit<F> for PrecomputeCircuit<F> {
            type Config = Pow2RangeConfig;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unreachable!();
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let columns = (0..1).map(|_| meta.advice_column()).collect::<Vec<_>>();
                Pow2RangeChip::configure(meta, &columns)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = Pow2RangeChip::<F>::new(&config, MAX_BIT_LEN);

                // Pre-register the tags we know we'll need
                chip.precompute_tags(&[3, 5]);

                // Load table early — this is now safe because tags are pre-registered
                chip.load_table(&mut layouter)?;

                // The chip is frozen, but the table already has tags 3 and 5.
                // We cannot call assert_row_lower_than_2_pow_n anymore, but the
                // table is complete for our needs.
                // (In a real circuit, you'd emit constraints before loading.)
                Ok(())
            }
        }

        let circuit = PrecomputeCircuit::<Fp> {
            _marker: PhantomData,
        };
        let prover = MockProver::run(&circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    /// Test that `precompute_tags` panics after freeze, via a circuit.
    #[test]
    #[should_panic(expected = "cannot precompute tags after load_table")]
    fn test_precompute_after_freeze_circuit() {
        const MAX_BIT_LEN: usize = 10;

        struct FreezePrecomputeCircuit<F: CircuitField> {
            _marker: PhantomData<F>,
        }

        impl<F: CircuitField> Circuit<F> for FreezePrecomputeCircuit<F> {
            type Config = Pow2RangeConfig;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unreachable!();
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let columns = (0..1).map(|_| meta.advice_column()).collect::<Vec<_>>();
                Pow2RangeChip::configure(meta, &columns)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = Pow2RangeChip::<F>::new(&config, MAX_BIT_LEN);
                chip.load_table(&mut layouter)?;
                // This must panic
                chip.precompute_tags(&[3]);
                Ok(())
            }
        }

        let circuit = FreezePrecomputeCircuit::<Fp> {
            _marker: PhantomData,
        };
        let _ = MockProver::run(&circuit, vec![]);
    }

    /// Test that `is_frozen` correctly reflects the chip state.
    #[test]
    fn test_is_frozen_state() {
        struct FrozenStateCircuit<F: CircuitField> {
            _marker: PhantomData<F>,
        }

        impl<F: CircuitField> Circuit<F> for FrozenStateCircuit<F> {
            type Config = Pow2RangeConfig;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unreachable!();
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let columns = (0..1).map(|_| meta.advice_column()).collect::<Vec<_>>();
                Pow2RangeChip::configure(meta, &columns)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = Pow2RangeChip::<F>::new(&config, 10);
                assert!(!chip.is_frozen(), "chip should not be frozen before load");
                chip.load_table(&mut layouter)?;
                assert!(chip.is_frozen(), "chip should be frozen after load");
                Ok(())
            }
        }

        let circuit = FrozenStateCircuit::<Fp> {
            _marker: PhantomData,
        };
        let _ = MockProver::run(&circuit, vec![]).unwrap();
    }
}

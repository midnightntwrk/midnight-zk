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

//! The P2RDecomposition chip perfoming the in-circuit operations

use std::{collections::HashMap, marker::PhantomData};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error},
};
use num_traits::Zero;

use super::{
    cpu_utils::{compute_optimal_limb_sizes, process_limb_sizes},
    instructions::CoreDecompositionInstructions,
    pow2range::{Pow2RangeChip, Pow2RangeConfig, NB_POW2RANGE_COLS},
};
use crate::{
    field::{
        decomposition::cpu_utils::{
            decompose_in_variable_limbsizes, variable_limbsize_coefficients,
        },
        NativeChip, NativeConfig,
    },
    types::AssignedNative,
    utils::{util::concat, ComposableChip},
};

#[derive(Clone, Debug)]
/// A decomposition config consists of a NativeConfig and a Pow2RangeConfig. It
/// assumes that the chips share the NB_POW2RANGE_COLS lookup enabled columns.
pub struct P2RDecompositionConfig {
    pub(crate) native_config: NativeConfig,
    pub(crate) pow2range_config: Pow2RangeConfig,
}

impl P2RDecompositionConfig {
    /// Creates the config from the configs of a native and and a pow2range
    /// chips. It assumes that
    ///  - advice_cols [0..NB_POW2RANGE_COLS] of pow2range_chip
    ///  - advice_cols [1..NB_POW2RANGE_COLS+1] of native_chip are the same
    ///
    /// # Panics
    ///
    /// This function panics when
    /// native_config advice_cols[1..NB_POW2RANGE_COLS+1]
    /// !=
    /// pow2range_config advice_cols[0..NB_POW2RANGE_COLS]
    pub fn new(native_config: &NativeConfig, pow2range_config: &Pow2RangeConfig) -> Self {
        // we assume that the *first NB_POW2RANGE_COLS columns* of the two configs are
        // shared we assume that
        //  - advice_cols [0..NB_POW2RANGE_COLS] of pow2range_chip
        //  - advice_cols [1..NB_POW2RANGE_COLS+1] of native_chip
        // are shared
        #[cfg(not(test))]
        assert!(
            native_config.value_cols[1..]
                .iter()
                .zip(pow2range_config.val_cols.iter())
                .all(|(n_col, p2r_col)| n_col == p2r_col),
            "DecompositionChip: Native and Pow2Range configs do not agree on the first {} columns",
            NB_POW2RANGE_COLS
        );
        Self {
            native_config: native_config.clone(),
            pow2range_config: pow2range_config.clone(),
        }
    }

    /// Returns the native config used for the decomposition config
    pub fn native_config(&self) -> &NativeConfig {
        &self.native_config
    }

    /// Returns the pow2range config used for the decomposition config
    pub fn pow2range_config(&self) -> &Pow2RangeConfig {
        &self.pow2range_config
    }
}

#[derive(Clone, Debug)]
/// A decomposition chip
pub struct P2RDecompositionChip<F: PrimeField> {
    // a hash map that contains the optimal (in number of rows) limb decomposition of a number
    // that is a power of two. Check
    // [compute_optimal_limb_sizes](cpu_utils::compute_optimal_limb_sizes) for more information on
    // this hash map
    opt_limbs: HashMap<i32, Vec<Vec<usize>>>,
    config: P2RDecompositionConfig,
    // the maximum limb length supported by the Pow2Range lookup
    max_bit_len: usize,
    native_chip: NativeChip<F>,
    pow2range_chip: Pow2RangeChip<F>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Chip<F> for P2RDecompositionChip<F> {
    type Config = P2RDecompositionConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> ComposableChip<F> for P2RDecompositionChip<F> {
    type SharedResources = (NativeConfig, Pow2RangeConfig);

    type InstructionDeps = usize;

    /// Creates the chips given the two sub-chips it consists of
    fn new(config: &Self::Config, &max_bit_len: &usize) -> Self {
        let mut opt_limbs = HashMap::new();
        // fill the HashMap. We do this here to avoid mutable references
        // TODO: Consider hard coding this values
        for bound in 0..=F::NUM_BITS {
            compute_optimal_limb_sizes(
                &mut opt_limbs,
                NB_POW2RANGE_COLS,
                max_bit_len,
                bound as i32,
            );
        }

        Self {
            opt_limbs,
            config: config.clone(),
            max_bit_len,
            native_chip: NativeChip::new(&config.native_config, &()),
            pow2range_chip: Pow2RangeChip::new(&config.pow2range_config, max_bit_len),
            _marker: PhantomData,
        }
    }

    fn configure(
        _meta: &mut ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config {
        Self::Config {
            native_config: shared_resources.0.clone(),
            pow2range_config: shared_resources.1.clone(),
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.pow2range_chip.load_table(layouter)
    }
}
impl<F: PrimeField> P2RDecompositionChip<F> {
    /// Gives direct access to the NativeChip
    pub fn native_chip(&self) -> &NativeChip<F> {
        &self.native_chip
    }

    /// Gives direct access to the Pow2RangeChip
    pub fn pow2range_chip(&self) -> &Pow2RangeChip<F> {
        &self.pow2range_chip
    }
}

impl<F: PrimeField> P2RDecompositionChip<F> {
    /// Takes a `Value<F>` and decomposes it in limbs according to the given
    /// `limb_sizes`. It then assigns those limbs and range-checks them.
    /// It also adds the limbs, returning an `AssignedNative<F>` encoding the
    /// initial value, but guaranteed to be range-checked in the range induced
    /// by the limbs.
    ///
    /// The assigned limbs are returned as a second argument, for testing
    /// purposes only.
    ///
    /// More concretely, it decomposes a field element in variable limbs sizes:
    /// given x in F and a slice `limb_sizes` that represents bit lengths,
    /// it returns [a_1, ..., a_m] such that:
    ///      (1) x = sum c_i a_i
    ///      (2) 0 <= a_i < 2^{limbs_size{i}}
    ///      (3) c_i = 2^{sum_{j=1}^{i-1} limb_sizes\[i\]}
    ///             if limb_sizes\[i\]>0 and 0 otherwise.
    /// This allows us to not restrict the corresponding a_i to equal 0
    ///
    ///  It assumes that the following about the limbs:
    ///  - all limbs are all smaller than or equal to self.max_bit_len
    ///  - the total number of limbs is a multiple of NB_POW2RANGE_COLS
    ///  - each NB_POW2RANGE_COLS - chunk consists of a signle limb_bit_size and
    ///    possibly zeros, the latter coming always at the end
    ///
    ///  # Panics
    ///
    ///  - if the field element cannot be represented with limb_sizes
    ///  - if the limb sizes are not correct.
    pub(crate) fn decompose_core(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Value<F>,
        limb_sizes: &[usize],
    ) -> Result<(AssignedNative<F>, Vec<AssignedNative<F>>), Error> {
        // assert limb_sizes structure is correct

        // 1. max limb length is not bigger than max_bit_length of chip
        #[cfg(not(test))]
        assert!(
            *limb_sizes.iter().max().unwrap_or(&0) <= self.max_bit_len,
            "Decomposition chip: Try to use decompose_core with limb sizes greater than the supported max limb length",
        );

        // 2. the number of given limbs is multiple of NB_POW2RANGE_COLS
        #[cfg(not(test))]
        assert!(
            limb_sizes.len() % NB_POW2RANGE_COLS == 0,
            "Decomposition chip: number of limbs passed in decompose_core is not a multiple of NB_POW2RANGE_COLS",
        );

        // 3. each NB_POW2RANGE_COLS chunk is the same number and possibly some zeros
        #[cfg(not(test))]
        {
            let limb_sizes_structure = limb_sizes.chunks(NB_POW2RANGE_COLS).all(|chunk| {
                let mut v = chunk.to_vec();
                v.sort();
                v.dedup();
                v.reverse(); // zeros at the end
                             // length at most 2 ==> two possible limb sizes per chunk
                let condition1 = v.len() <= 2;
                // should not panic if length is 1 due to short_circuiting
                let condition2 = (v.len() == 1) || (v[0] == 0) || (v[1] == 0);
                // length is less than 2 AND if length is 2 then one of the elements should be
                // zero
                condition1 && condition2
            });
            assert!(
                limb_sizes_structure,
                "Decomposition chip: malformed limb sizes in decompose_core",
            );
        }

        layouter.assign_region(
            || "decompose core",
            |mut region| {
                let mut offset = 0;

                // compute the range_check tags for each column
                let tags = limb_sizes
                    .chunks(NB_POW2RANGE_COLS)
                    .map(|x| x[0])
                    .collect::<Vec<_>>();

                // compute the linear combination terms, i.e. (coef, limb) pairs
                // by convention the coefficient of a zero sized limb is 0 so no constraint
                // needs to be imposed in the corresponding limb
                let coefficients = variable_limbsize_coefficients::<F>(limb_sizes);
                let limbs = x
                    .map(|x_value| decompose_in_variable_limbsizes(&x_value, limb_sizes))
                    .transpose_vec(limb_sizes.len());

                // we create the terms for the linear combination.
                let terms = coefficients
                    .into_iter()
                    .zip(limbs.iter().copied())
                    .collect::<Vec<_>>();

                // assign terms for linear combination
                let native_chip = self.native_chip();
                let (assigned_limbs, assigned_result) = native_chip.assign_linear_combination_aux(
                    &mut region,
                    terms.as_slice(),
                    F::ZERO,
                    &x,
                    NB_POW2RANGE_COLS,
                    &mut offset,
                )?;
                offset += 1;

                // enable the appropriate copy constraints in the rows where we assigned the
                // linear combination terms
                let pow2range_chip = self.pow2range_chip();

                // get the lookup selector and tag columns
                let range_selector_column = pow2range_chip.config().q_pow2range;
                let range_tag_column = pow2range_chip.config().tag_col;

                // we revers since we do the rangechecks from higher end to start
                for (i, tag) in tags.into_iter().rev().enumerate() {
                    let current_row = offset - (i + 1);
                    range_selector_column.enable(&mut region, current_row)?;
                    region.assign_fixed(
                        || "assign decomposition tag",
                        range_tag_column,
                        current_row,
                        || Value::known(F::from(tag as u64)),
                    )?;
                }

                // we remove the trivial coefficients, i.e. those corresponding to a zero size
                // limb, and return
                let limbs = assigned_limbs
                    .into_iter()
                    .zip(limb_sizes.iter())
                    .filter(|(_assigned_limb, limb_size)| !limb_size.is_zero())
                    .map(|(assigned_limb, _)| assigned_limb)
                    .collect::<Vec<_>>();
                Ok((assigned_result, limbs))
            },
        )
    }
}

impl<F: PrimeField> CoreDecompositionInstructions<F> for P2RDecompositionChip<F> {
    // TODO: This can be further optimized by parallelizing lookups for the
    // decomposed limbs. Perhaps using a function for optimal decomposing
    // multiple terms?
    fn decompose_fixed_limb_size(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bit_length: usize,
        limb_size: usize,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        // compute the limbs_sizes. The last limb size might be smaller than limb size
        let number_of_limbs = bit_length / limb_size;
        let last_limb_size = bit_length % limb_size;

        // limb decomposition can be supported natively by the lookup table
        if limb_size <= self.max_bit_len {
            // prepare the limb_size slice by filling with zeros to do parallel lookups
            let mut limb_sizes = vec![limb_size; number_of_limbs];
            process_limb_sizes(NB_POW2RANGE_COLS, &mut limb_sizes);
            // prepare the limb sizes for last (possibly smaller limb). This is either empty
            // or contains exactly NB_POW2RANGE_COLS elements where the last
            // NB_POW2RANGE_COLS-1 are 0s
            if last_limb_size != 0 {
                limb_sizes.push(last_limb_size);
                process_limb_sizes(NB_POW2RANGE_COLS, &mut limb_sizes);
            }

            // we call the core function to retrieve the result
            let (y, assigned_limbs) = self.decompose_core(
                &mut layouter.namespace(|| "decompose fixed"),
                x.value().copied(),
                limb_sizes.as_slice(),
            )?;

            layouter.assign_region(
                || "copy",
                |mut region| region.constrain_equal(x.cell(), y.cell()),
            )?;

            Ok(assigned_limbs)
        }
        // limbs should be further range-checked since they are larger than the supported lookup
        // bounds
        else {
            // prepare the limb_size slice by filling with zeros to do parallel lookups
            let mut limb_sizes = vec![limb_size; number_of_limbs];

            // if the last limb is non-zero sized add it to the limb sizes
            if last_limb_size != 0 {
                limb_sizes.push(last_limb_size);
            }

            let assigned_limbs = layouter.assign_region(
                || "assign limbs decompose fixed",
                |mut region| {
                    let mut offset = 0;

                    // compue the linear combination terms, i.e. (coef, limb) pairs
                    let coefficients = variable_limbsize_coefficients::<F>(limb_sizes.as_slice());
                    let limbs = x
                        .value()
                        .map(|x_value| {
                            decompose_in_variable_limbsizes(x_value, limb_sizes.as_slice())
                        })
                        .transpose_vec(limb_sizes.len());

                    // we create the terms for the linear combination
                    let terms = coefficients
                        .into_iter()
                        .zip(limbs.iter().copied())
                        .collect::<Vec<_>>();

                    // assign terms for linear combination to assert correct decomposition
                    let (assigned_limbs, assigned_result) =
                        self.native_chip().assign_linear_combination_aux(
                            &mut region,
                            terms.as_slice(),
                            F::ZERO,
                            &x.value().copied(),
                            NB_POW2RANGE_COLS,
                            &mut offset,
                        )?;

                    // copy constraint the linear combination result to equal the decomposed value
                    region.constrain_equal(assigned_result.cell(), x.cell())?;

                    Ok(assigned_limbs)
                },
            )?;

            // range check assigned limbs and return them
            assigned_limbs
                .iter()
                .zip(limb_sizes.iter())
                .try_for_each(|(x_limb, &limb_size)| {
                    self.assert_less_than_pow2(layouter, x_limb, limb_size)
                })?;

            Ok(assigned_limbs)
        }
    }

    fn assign_less_than_pow2(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        bit_length: usize,
    ) -> Result<AssignedNative<F>, Error> {
        #[cfg(not(test))]
        assert!((bit_length as u32) < F::NUM_BITS);

        // 1. get the limb sizes that minimize the number of parallel lookup rangechecks
        // should never panic since the HashMap contains all possible solutions
        let mut optimal_limb_sizes = self.opt_limbs.get(&(bit_length as i32)).unwrap().clone();

        // 2. process them by adding 0 terms in non-full rows
        optimal_limb_sizes
            .iter_mut()
            .for_each(|row| process_limb_sizes(NB_POW2RANGE_COLS, row));
        let limb_sizes = concat(optimal_limb_sizes.as_slice());

        // 3. use decompose_core to compute the result
        let (y, _) = self.decompose_core(layouter, value, limb_sizes.as_slice())?;

        Ok(y)
    }

    fn assign_many_small(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<F>],
        bit_length: usize,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert!(8 < F::NUM_BITS);
        assert!(
            bit_length <= 8,
            "assign_many_small expects a bit_length <= 8"
        );

        let mut assigned_values = Vec::with_capacity(values.len());
        for chunk in values.chunks(NB_POW2RANGE_COLS) {
            let assigned_chunk: Vec<_> = layouter.assign_region(
                || "assign_many_small",
                |mut region| {
                    let mut padded_chunk = chunk.to_vec();
                    padded_chunk.resize(NB_POW2RANGE_COLS, Value::known(F::ZERO));

                    self.pow2range_chip()
                        .assert_row_lower_than_2_pow_n(&mut region, bit_length)?;

                    padded_chunk
                        .iter()
                        .zip(self.config.pow2range_config.val_cols.iter())
                        .map(|(value, col)| {
                            region.assign_advice(|| "assign small", *col, 0, || *value)
                        })
                        .collect()
                },
            )?;
            assigned_values.extend_from_slice(&assigned_chunk[..chunk.len()]);
        }
        Ok(assigned_values)
    }
}

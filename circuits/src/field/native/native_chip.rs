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

//! A chip for efficient native arithmetic.
// `native_chip` implements several traits:
//   - ArithInstructions
//   - BinaryInstructions
//   - EqualityInstructions
//   - ControlFlowInstructions
//
// for the native field type, through a very simple identity of the form:
//
//  q_arith *
//  {
//  (sum_i coeff[i] * value[i])
//    + q_next * value[0](omega) +
//    + mul_ab * value[0] * value[1] +
//    + mul_cd * value[2] * value[3] +
//    + constant
//  }
//  = 0
//
// Here, `coeffs`, `q_next`, `mul_ab`, `mul_cd`, `constant` are stored in fixed
// columns, whereas `values` are stored in advice columns.
//
// Also, an utilitary gate for parallel affine relation is defined for
// performing parallel additions (by constant) x[omega] = x + c in one row.
// The formal identities read as:
//
// q_par_add * { value[i] + coeff[i] - value[i](omega) } = 0
//
// for all i = 0..NB_PARALLEL_ADD_COLS.

use std::{
    cell::RefCell,
    cmp::min,
    collections::HashMap,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Neg,
    rc::Rc,
};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Instance, Selector},
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::Zero;

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;
use crate::{
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, BinaryInstructions,
        CanonicityInstructions, ControlFlowInstructions, ConversionInstructions,
        EqualityInstructions, FieldInstructions, PublicInputInstructions,
        UnsafeConversionInstructions, ZeroInstructions,
    },
    types::{AssignedNative, InnerValue, Instantiable},
    utils::{
        util::{fe_to_big, modulus},
        ComposableChip,
    },
};

/// Number of columns used by the identity of the native chip.
/// This number should NOT be smaller than 5.
/// This limit is imposed by functions like [NativeChip::select].
pub const NB_ARITH_COLS: usize = 5;

/// Number of fixed columns used by the identity of the native chip.
pub const NB_ARITH_FIXED_COLS: usize = NB_ARITH_COLS + 4;

/// Number of additions (by constant) that can be performed in
/// parallel in 1 row. This number should not exceed [NB_ARITH_COLS].
///
/// The Poseidon chip requires this number to match the Poseidon
/// register width. Have that into consideration before modifying
/// this number.
const NB_PARALLEL_ADD_COLS: usize = 3;

/// Config defines fixed and witness columns of the main gate
#[derive(Clone, Debug)]
pub struct NativeConfig {
    pub(crate) q_arith: Selector,
    pub(crate) q_par_add: Selector,
    pub(crate) value_cols: [Column<Advice>; NB_ARITH_COLS],
    pub(crate) coeff_cols: [Column<Fixed>; NB_ARITH_COLS],
    pub(crate) q_next_col: Column<Fixed>,
    pub(crate) mul_ab_col: Column<Fixed>,
    pub(crate) mul_cd_col: Column<Fixed>,
    pub(crate) constant_col: Column<Fixed>,
    pub(crate) committed_instance_col: Column<Instance>,
    pub(crate) instance_col: Column<Instance>,
}

/// Chip for Native operations
#[derive(Clone, Debug)]
pub struct NativeChip<F: PrimeField> {
    config: NativeConfig,
    cached_fixed: Rc<RefCell<HashMap<BigUint, AssignedNative<F>>>>,
    committed_instance_offset: Rc<RefCell<usize>>,
    instance_offset: Rc<RefCell<usize>>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Chip<F> for NativeChip<F> {
    type Config = NativeConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> ComposableChip<F> for NativeChip<F> {
    type SharedResources = (
        [Column<Advice>; NB_ARITH_COLS],
        [Column<Fixed>; NB_ARITH_FIXED_COLS],
        [Column<Instance>; 2], // [committed, normal]
    );

    type InstructionDeps = ();
    /// Creates a new NativeChip given the corresponding configuration.
    fn new(config: &NativeConfig, _sub_chips: &()) -> Self {
        Self {
            config: config.clone(),
            cached_fixed: Default::default(),
            instance_offset: Rc::new(RefCell::new(0)),
            committed_instance_offset: Rc::new(RefCell::new(0)),
            _marker: PhantomData,
        }
    }

    /// Creates a NativeConfig given a constraint system and a set of
    /// available advice columns and fixed columns.
    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> NativeConfig {
        let value_columns = &shared_res.0;
        let fixed_columns = &shared_res.1;

        // It is important that the committed instance column was created before the
        // other instance column, since committed columns go first.
        let committed_instance_col = shared_res.2[0];
        let instance_col = shared_res.2[1];

        let q_arith = meta.selector();
        let q_par_add = meta.selector();
        let coeff_cols: [Column<Fixed>; NB_ARITH_COLS] = fixed_columns[4..].try_into().unwrap();
        let q_next_col = fixed_columns[0];
        let mul_ab_col = fixed_columns[1];
        let mul_cd_col = fixed_columns[2];
        let constant_col = fixed_columns[3];

        for col in value_columns.iter() {
            meta.enable_equality(*col);
        }
        meta.enable_equality(committed_instance_col);
        meta.enable_equality(instance_col);

        meta.create_gate("arith_gate", |meta| {
            let q = meta.query_selector(q_arith);

            let values = value_columns
                .iter()
                .map(|col| meta.query_advice(*col, Rotation::cur()))
                .collect::<Vec<_>>();

            let next_value = meta.query_advice(value_columns[0], Rotation::next());

            let coeffs = coeff_cols
                .iter()
                .map(|col| meta.query_fixed(*col, Rotation::cur()))
                .collect::<Vec<_>>();

            let q_next_coeff = meta.query_fixed(q_next_col, Rotation::cur());
            let mul_ab_coeff = meta.query_fixed(mul_ab_col, Rotation::cur());
            let mul_cd_coeff = meta.query_fixed(mul_cd_col, Rotation::cur());
            let constant = meta.query_fixed(constant_col, Rotation::cur());

            let id = values
                .iter()
                .zip(coeffs.iter())
                .fold(constant, |acc, (value, coeff)| {
                    acc + coeff.clone() * value.clone()
                })
                + q_next_coeff * next_value
                + mul_ab_coeff * values[0].clone() * values[1].clone()
                + mul_cd_coeff * values[2].clone() * values[3].clone();

            Constraints::with_selector(q, [id])
        });

        meta.create_gate("parallel_add_gate", |meta| {
            let q = meta.query_selector(q_par_add);

            let ids = (value_columns[0..NB_PARALLEL_ADD_COLS].iter())
                .zip(coeff_cols[0..NB_PARALLEL_ADD_COLS].iter())
                .map(|(val_col, const_col)| {
                    let val = meta.query_advice(*val_col, Rotation::cur());
                    let res = meta.query_advice(*val_col, Rotation::next());
                    let c = meta.query_fixed(*const_col, Rotation::cur());
                    val + c - res
                })
                .collect::<Vec<_>>();

            Constraints::with_selector(q, ids)
        });

        NativeConfig {
            q_arith,
            q_par_add,
            value_cols: *value_columns,
            coeff_cols,
            q_next_col,
            mul_ab_col,
            mul_cd_col,
            constant_col,
            committed_instance_col,
            instance_col,
        }
    }

    fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

impl<F: PrimeField> NativeChip<F> {
    /// Fills the arithmetic identity selectors with the given values at the
    /// current offset. This function does not assign values, it assumes they
    /// have already been assigned.
    fn custom(
        &self,
        region: &mut Region<'_, F>,
        coeffs: &[F; NB_ARITH_COLS],
        q_next_coeff: F,
        mul_coeffs: (F, F),
        constant: F,
        offset: usize,
    ) -> Result<(), Error> {
        self.config.q_arith.enable(region, offset)?;

        for (i, coeff) in coeffs.iter().enumerate() {
            region.assign_fixed(
                || "arith coeff",
                self.config.coeff_cols[i],
                offset,
                || Value::known(*coeff),
            )?;
        }

        region.assign_fixed(
            || "arith q_next",
            self.config.q_next_col,
            offset,
            || Value::known(q_next_coeff),
        )?;
        region.assign_fixed(
            || "arith mul_ab",
            self.config.mul_ab_col,
            offset,
            || Value::known(mul_coeffs.0),
        )?;
        region.assign_fixed(
            || "arith mul_cd",
            self.config.mul_cd_col,
            offset,
            || Value::known(mul_coeffs.1),
        )?;
        region.assign_fixed(
            || "arith const",
            self.config.constant_col,
            offset,
            || Value::known(constant),
        )?;

        Ok(())
    }

    /// Copies the given assigned value in the current row and the given column.
    fn copy_in_row(
        &self,
        region: &mut Region<'_, F>,
        x: &AssignedNative<F>,
        column: &Column<Advice>,
        offset: usize,
    ) -> Result<(), Error> {
        let y = region.assign_advice(
            || "arith copy_in_row",
            *column,
            offset,
            || x.value().copied(),
        )?;
        region.constrain_equal(x.cell(), y.cell())?;
        Ok(())
    }

    /// Computes `a*x + b*y + c*z + k + m1*x*y + m2*x*z`.
    fn add_and_double_mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a_and_x: (F, &AssignedNative<F>),
        b_and_y: (F, &AssignedNative<F>),
        c_and_z: (F, &AssignedNative<F>),
        k: F,
        m1_and_m2: (F, F),
    ) -> Result<AssignedNative<F>, Error> {
        let (a, x) = a_and_x;
        let (b, y) = b_and_y;
        let (c, z) = c_and_z;
        let (m1, m2) = m1_and_m2;
        let res_value = x
            .value()
            .zip(y.value())
            .zip(z.value())
            .map(|((x, y), z)| a * x + b * y + c * z + k + m1 * x * y + m2 * x * z);
        layouter.assign_region(
            || "add and double mul",
            |mut region| {
                self.copy_in_row(&mut region, x, &self.config.value_cols[0], 0)?;
                self.copy_in_row(&mut region, y, &self.config.value_cols[1], 0)?;
                self.copy_in_row(&mut region, z, &self.config.value_cols[2], 0)?;
                self.copy_in_row(&mut region, x, &self.config.value_cols[3], 0)?;
                let res =
                    region.assign_advice(|| "res", self.config.value_cols[4], 0, || res_value)?;
                let mut coeffs = [F::ZERO; NB_ARITH_COLS];
                coeffs[0] = a; // coeff of x
                coeffs[1] = b; // coeff of y
                coeffs[2] = c; // coeff of z
                coeffs[4] = -F::ONE; // coeff of res
                self.custom(&mut region, &coeffs, F::ZERO, (m1, m2), k, 0)?;
                Ok(res)
            },
        )
    }

    /// Assigns the given value into a variable `x`, and returns `(x, r)`, where
    /// `r` is such that `(x - shift) * r = 1`.
    ///
    /// Calling this function on `value = shift` will make the circuit
    /// unsatisfiable.
    fn assign_with_shifted_inverse(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        shift: F,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error> {
        layouter.assign_region(
            || "assign with shifted inverse",
            |mut region| {
                // x * r - shift * r - 1 = 0
                let r_value = value.map(|x| (x - shift).invert().unwrap_or(F::ZERO));
                let x = region.assign_advice(|| "x", self.config.value_cols[0], 0, || value)?;
                let r = region.assign_advice(|| "r", self.config.value_cols[1], 0, || r_value)?;
                let mut coeffs = [F::ZERO; NB_ARITH_COLS];
                coeffs[1] = -shift; // coeff of r
                self.custom(&mut region, &coeffs, F::ZERO, (F::ONE, F::ZERO), -F::ONE, 0)?;
                Ok((x, r))
            },
        )
    }

    /// Assigns the given value, introducing a constraint that guarantees that
    /// it is non-zero.
    fn assign_non_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let (x, _) = self.assign_with_shifted_inverse(layouter, value, F::ZERO)?;
        Ok(x)
    }

    /// Assigns values to verify a linear combination of the given terms.
    ///
    /// Concretely, given terms s.t. `term_i = (c_i, a_i)` and result, it
    /// asserts that `result = sum c_i a_i`.
    ///
    /// The chip uses `cols_used` columns per row to accumulate `col_used` terms
    /// in a temporary result and one column to keep this temporary result.
    ///
    /// This function is called recursively via the following relation:
    ///
    /// `res = \sum c_j a_j + \sum c_i a_i <==> (res - \sum c_j a_j) = \sum c_i
    /// a_i`
    ///
    /// - the j indices correspond to the (not more than cols_used) terms
    ///   consumed
    /// - the i indices correspond to the rest terms
    ///
    /// if the i indices are empty we directly verify the relation in a single
    /// row, otherwise we verify the relation `new_result = res + \sum c_j
    /// a_j` by using the `q_next_col` column to query the witnessed
    /// `new_result` which will always be in the first column of the next row
    ///
    /// INVARIANT: Whenever this function is called: `result = \sum terms[i].0 *
    /// terms[i].1`
    ///
    /// The function returns the assigned linear combination witness elements
    /// and the linear combination result
    pub(crate) fn assign_linear_combination_aux(
        &self,
        region: &mut Region<'_, F>,
        terms: &[(F, Value<F>)],
        constant: F,
        result: &Value<F>,
        cols_used: usize,
        offset: &mut usize,
    ) -> Result<(Vec<AssignedNative<F>>, AssignedNative<F>), Error> {
        // cols_used should be less than NB_ARITH_COLS
        assert!(cols_used < NB_ARITH_COLS);

        // If |terms| <= cols_used, we assert the relation in one row.
        // Otherwise we consume up to `cols_used` terms to reduce to a linear
        // combination of smaller size.
        let chunk_len = min(terms.len(), cols_used);

        // Initialize the coefficients vector
        let mut coeffs = [F::ZERO; NB_ARITH_COLS];

        // assign the lc result in the first advice column
        let assigned_result = region.assign_advice(
            || "assign linear combination term",
            self.config.value_cols[0],
            *offset,
            || *result,
        )?;
        coeffs[0] = -F::ONE;

        // assign the first `chunk_len` terms values in the current row
        let mut assigned_limbs = terms[0..chunk_len]
            .iter()
            .enumerate()
            .map(|(i, term)| {
                coeffs[i + 1] = term.0;
                region.assign_advice(
                    || "assign linear combination term",
                    self.config.value_cols[i + 1],
                    *offset,
                    || term.1,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // If everything fits in this row, we add the constraint in the current row and
        // finish.
        if terms.len() <= cols_used {
            self.custom(
                region,
                &coeffs,
                F::ZERO,
                (F::ZERO, F::ZERO),
                constant,
                *offset,
            )?;
            Ok((assigned_limbs, assigned_result))
        }
        // Otherwise, we recurse on the remaining terms with the new result.
        else {
            // compute the next result: `result - \sum c_j a_j` for j in the chunk
            let chunk_result = terms[..chunk_len]
                .iter()
                .fold(Value::known(constant), |acc, (coeff, x)| {
                    acc.zip(*x).map(|(acc, val)| acc + *coeff * val)
                });
            let next_result = *result - chunk_result;

            // the cells will be after the next recursive call of the following form
            // offset:      (-1, result)       | (c_1, a_1) | (c_2, a_2) | ... | (c_j, a_j)
            // offset+1:    (-1, new_result)   |    ...     |    ...     | ... |    ...
            //
            // We need to verify the constraint `result - sum c_j a_j = new_result`,
            // equivalently `new_result - result + sum c_j a_j = 0`.
            //
            // We add the terms in the current row (i.e. `sum c_j a_j - result`)
            // and use the selector q_next_coeff to also add the first advice cell of the
            // next column
            self.custom(
                region,
                &coeffs,
                F::ONE,
                (F::ZERO, F::ZERO),
                constant,
                *offset,
            )?;
            *offset += 1;
            let (new_assigned_limbs, _) = self.assign_linear_combination_aux(
                region,
                &terms[chunk_len..],
                F::ZERO,
                &next_result,
                cols_used,
                offset,
            )?;
            assigned_limbs.extend_from_slice(&new_assigned_limbs);
            Ok((assigned_limbs, assigned_result))
        }
    }

    /// The total number of public inputs (as raw scalars) that have been
    /// constrained so far by this chip.
    pub(crate) fn nb_public_inputs(&self) -> usize {
        *self.instance_offset.borrow()
    }

    /// The total number of public inputs (as raw scalars) that have been
    /// constrained (in committed form) so far by this chip.
    pub(crate) fn nb_committed_public_inputs(&self) -> usize {
        *self.committed_instance_offset.borrow()
    }
}

impl<F: PrimeField> NativeChip<F> {
    /// Performs parallel additions of `variables` and `constants` in one row,
    /// and increments the offset.
    pub(crate) fn add_constants_in_region(
        &self,
        region: &mut Region<'_, F>,
        variables: &[AssignedNative<F>; NB_PARALLEL_ADD_COLS],
        constants: &[F; NB_PARALLEL_ADD_COLS],
        offset: &mut usize,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.config.q_par_add.enable(region, *offset)?;

        (variables.iter())
            .zip(self.config.value_cols)
            .try_for_each(|(x, col)| self.copy_in_row(region, x, &col, *offset))?;

        (constants.iter())
            .zip(self.config.coeff_cols)
            .try_for_each(|(c, col)| {
                region.assign_fixed(|| "add_consts", col, *offset, || Value::known(*c))?;
                Ok::<(), Error>(())
            })?;

        *offset += 1;

        let res_values = (variables.iter())
            .zip(constants)
            .map(|(x, c)| x.value().map(|x| *x + *c));

        res_values
            .zip(self.config.value_cols)
            .map(|(val, col)| region.assign_advice(|| "add_consts", col, *offset, || val))
            .collect::<Result<Vec<_>, Error>>()
    }
}

impl<F> AssignmentInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedNative<F>, Error> {
        layouter.assign_region(
            || "Assign native value",
            |mut region| {
                region.assign_advice(|| "assign element", self.config.value_cols[0], 0, || value)
            },
        )
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        let constant_big = fe_to_big::<F>(constant);
        if let Some(assigned) = self.cached_fixed.borrow().get(&constant_big) {
            return Ok(assigned.clone());
        };

        layouter.assign_region(
            || "Assign fixed",
            |mut region| {
                // Enforce x - constant = 0.
                let x = region.assign_advice(
                    || "x",
                    self.config.value_cols[0],
                    0,
                    || Value::known(constant),
                )?;
                let mut coeffs = [F::ZERO; NB_ARITH_COLS];
                coeffs[0] = F::ONE; // coeff of x
                self.custom(
                    &mut region,
                    &coeffs,
                    F::ZERO,
                    (F::ZERO, F::ZERO),
                    -constant,
                    0,
                )?;

                // Save the assigned constant in the cache.
                self.cached_fixed
                    .borrow_mut()
                    .insert(constant_big.clone(), x.clone());

                Ok(x)
            },
        )
    }

    // This is more efficient than the blanket implementation.
    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        layouter.assign_region(
            || "assign_many (native)",
            |mut region| {
                let mut assigned = vec![];
                for (i, chunk_values) in values.chunks(NB_ARITH_COLS).enumerate() {
                    for (value, col) in chunk_values.iter().zip(self.config.value_cols.iter()) {
                        let cell = region.assign_advice(|| "assign", *col, i, || *value)?;
                        assigned.push(cell);
                    }
                }
                Ok(assigned)
            },
        )
    }
}

impl<F> PublicInputInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        assigned: &AssignedNative<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![assigned.clone()])
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedNative<F>,
    ) -> Result<(), Error> {
        let mut offset = self.instance_offset.borrow_mut();
        layouter.constrain_instance(assigned.cell(), self.config.instance_col, *offset)?;
        *offset += 1;
        Ok(())
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedNative<F>, Error> {
        // There is nothing to optimize when assigning a public native value.
        let assigned = self.assign(layouter, value)?;
        self.constrain_as_public_input(layouter, &assigned)?;
        Ok(assigned)
    }
}

impl<F: PrimeField> NativeChip<F> {
    /// Constrains the given assigned value as a public input that will be
    /// plugged-in in committed form.
    pub fn constrain_as_committed_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedNative<F>,
    ) -> Result<(), Error> {
        let mut offset = self.committed_instance_offset.borrow_mut();
        layouter.constrain_instance(
            assigned.cell(),
            self.config.committed_instance_col,
            *offset,
        )?;
        *offset += 1;
        Ok(())
    }
}

impl<F> AssignmentInstructions<F, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<bool>,
    ) -> Result<AssignedBit<F>, Error> {
        layouter.assign_region(
            || "Assign big",
            |mut region| {
                // Enforce x * x - x = 0
                let b_value = value.map(|b| if b { F::ONE } else { F::ZERO });
                let b = region.assign_advice(|| "b", self.config.value_cols[0], 0, || b_value)?;
                self.copy_in_row(&mut region, &b, &self.config.value_cols[1], 0)?;
                let mut coeffs = [F::ZERO; NB_ARITH_COLS];
                coeffs[0] = -F::ONE; // coeff of x
                self.custom(&mut region, &coeffs, F::ZERO, (F::ONE, F::ZERO), F::ZERO, 0)?;
                Ok(AssignedBit(b))
            },
        )
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: bool,
    ) -> Result<AssignedBit<F>, Error> {
        let constant = if bit { F::ONE } else { F::ZERO };
        let x = self.assign_fixed(layouter, constant)?;
        Ok(AssignedBit(x))
    }
}

impl<F> PublicInputInstructions<F, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        assigned: &AssignedBit<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![assigned.clone().into()])
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedBit<F>,
    ) -> Result<(), Error> {
        let assigned_as_native: AssignedNative<F> = assigned.clone().into();
        self.constrain_as_public_input(layouter, &assigned_as_native)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<bool>,
    ) -> Result<AssignedBit<F>, Error> {
        // We can skip the in-circuit boolean assertion as this condition will be
        // enforced through the public inputs bind anyway.
        let bit_val = value.map(|b| if b { F::ONE } else { F::ZERO });
        let assigned_native = self.assign_as_public_input(layouter, bit_val)?;
        self.convert_unsafe(layouter, &assigned_native)
    }
}

impl<F> AssertionInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Assert equal",
            |mut region| region.constrain_equal(x.cell(), y.cell()),
        )
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Assert not equal",
            |mut region| {
                // We enforce (x - y) * r = 1, for a fresh r.
                // Encoded as x * r - y * r - 1 = 0
                let r_value = (x.value().copied() - y.value().copied())
                    .map(|v| v.invert().unwrap_or(F::ZERO));
                self.copy_in_row(&mut region, x, &self.config.value_cols[0], 0)?;
                let r = region.assign_advice(|| "r", self.config.value_cols[1], 0, || r_value)?;
                self.copy_in_row(&mut region, y, &self.config.value_cols[2], 0)?;
                self.copy_in_row(&mut region, &r, &self.config.value_cols[3], 0)?;
                let coeffs = [F::ZERO; NB_ARITH_COLS];
                self.custom(&mut region, &coeffs, F::ZERO, (F::ONE, -F::ONE), -F::ONE, 0)?;
                Ok(())
            },
        )
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<(), Error> {
        let c = self.assign_fixed(layouter, constant)?;
        self.assert_equal(layouter, x, &c)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<(), Error> {
        // We show that (x != constant) by exhibiting an inverse of (x - constant),
        // which we discard.
        let (y, _) = self.assign_with_shifted_inverse(layouter, x.value().copied(), constant)?;
        self.assert_equal(layouter, x, &y)
    }
}

impl<F> AssertionInstructions<F, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.assert_equal(layouter, &x.0, &y.0)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<(), Error> {
        let diff = self.sub(layouter, &x.0, &y.0)?;
        self.assert_non_zero(layouter, &diff)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        b: bool,
    ) -> Result<(), Error> {
        let constant = if b { F::ONE } else { F::ZERO };
        self.assert_equal_to_fixed(layouter, &x.0, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        constant: bool,
    ) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, x, !constant)
    }
}

impl<F> ZeroInstructions<F, AssignedNative<F>> for NativeChip<F> where F: PrimeField {}

impl<F> ArithInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(F, AssignedNative<F>)],
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        let terms: Vec<_> = terms
            .iter()
            .filter(|(c, _)| !F::is_zero_vartime(c))
            .cloned()
            .collect();
        if terms.is_empty() {
            return self.assign_fixed(layouter, constant);
        }

        // Maybe a  &[(F, AssignedNative<F>)] (and correspondingly to the aux function.
        // Do we really need slices with references?
        let term_values = terms
            .iter()
            .cloned()
            .map(|(c, assigned_t)| (c, assigned_t.value().copied()))
            .collect::<Vec<_>>();

        let result = terms
            .iter()
            .fold(Value::known(constant), |acc, (coeff, x)| {
                acc.zip(x.value()).map(|(acc, val)| acc + *coeff * val)
            });

        layouter.assign_region(
            || "Linear combination",
            |mut region| {
                let mut offset = 0;
                let (assigned_limbs, assigned_result) = self.assign_linear_combination_aux(
                    &mut region,
                    term_values.as_slice(),
                    constant,
                    &result,
                    NB_ARITH_COLS - 1,
                    &mut offset,
                )?;

                assert_eq!(assigned_limbs.len(), terms.len());

                // assert the newly assigned values are equal to the one given as input
                assigned_limbs
                    .iter()
                    .zip(terms.iter())
                    .try_for_each(|(new_av, (_, av))| {
                        region.constrain_equal(new_av.cell(), av.cell())
                    })?;

                Ok(assigned_result)
            },
        )
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        multiplying_constant: Option<F>,
    ) -> Result<AssignedNative<F>, Error> {
        if multiplying_constant == Some(F::ZERO) {
            return self.assign_fixed(layouter, F::ZERO);
        }

        let m = multiplying_constant.unwrap_or(F::ONE);

        let one: AssignedNative<F> = self.assign_fixed(layouter, F::ONE)?;
        if m == F::ONE && x.clone() == one {
            return Ok(y.clone());
        }
        if m == F::ONE && y.clone() == one {
            return Ok(x.clone());
        }

        self.add_and_mul(
            layouter,
            (F::ZERO, x),
            (F::ZERO, y),
            (F::ZERO, x),
            F::ZERO,
            m,
        )
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let y_inv = self.inv(layouter, y)?;
        self.mul(layouter, x, &y_inv, None)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let (y, inv) = self.assign_with_shifted_inverse(layouter, x.value().copied(), F::ZERO)?;
        self.assert_equal(layouter, x, &y)?;
        Ok(inv)
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let is_zero = self.is_zero(layouter, x)?;
        let zero = self.assign_fixed(layouter, F::ZERO)?;
        let one = self.assign_fixed(layouter, F::ONE)?;
        let invertible = self.select(layouter, &is_zero, &one, x)?;
        let inverse = self.inv(layouter, &invertible)?;
        self.select(layouter, &is_zero, &zero, &inverse)
    }

    fn add_and_mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a_and_x: (F, &AssignedNative<F>),
        b_and_y: (F, &AssignedNative<F>),
        c_and_z: (F, &AssignedNative<F>),
        k: F,
        m: F,
    ) -> Result<AssignedNative<F>, Error> {
        self.add_and_double_mul(layouter, a_and_x, b_and_y, c_and_z, k, (m, F::ZERO))
    }

    fn add_constants(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: &[AssignedNative<F>],
        constants: &[F],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert_eq!(xs.len(), constants.len());

        let pairs = (xs.iter().zip(constants.iter()))
            .filter(|(_, &c)| c != F::ZERO)
            .collect::<Vec<_>>();

        let mut non_trivial_outputs = Vec::with_capacity(pairs.len());

        let mut chunks = pairs.chunks_exact(NB_PARALLEL_ADD_COLS);
        for chunk in chunks.by_ref() {
            let outputs = layouter.assign_region(
                || "add_constants",
                |mut region| {
                    let values = chunk.iter().map(|(x, _)| (*x).clone()).collect::<Vec<_>>();
                    let consts = chunk.iter().map(|(_, c)| **c).collect::<Vec<_>>();
                    self.add_constants_in_region(
                        &mut region,
                        &values.try_into().unwrap(),
                        &consts.try_into().unwrap(),
                        &mut 0,
                    )
                },
            )?;
            non_trivial_outputs.extend(outputs);
        }

        // Proecss a final chunk of length < NB_PARALLEL_ADD_COLS, "manually".
        for (x, c) in chunks.remainder() {
            non_trivial_outputs.push(self.add_constant(layouter, x, **c)?);
        }

        let mut outputs = Vec::with_capacity(xs.len());
        let mut j = 0;
        for i in 0..xs.len() {
            if constants[i] != F::ZERO {
                outputs.push(non_trivial_outputs[j].clone());
                j += 1;
            } else {
                outputs.push(xs[i].clone())
            }
        }

        Ok(outputs)
    }
}

impl<F: PrimeField> Instantiable<F> for AssignedBit<F> {
    fn as_public_input(element: &bool) -> Vec<F> {
        vec![if *element { F::ONE } else { F::ZERO }]
    }
}

/// This wrapper type on `AssignedNative<F>` is designed to enforce type safety
/// on assigned bits. It prevents the user from creating an `AssignedBit`
/// without using the designated entry points, which guarantee (with
/// constraints) that the assigned value is indeed 0 or 1.
#[derive(Clone, Debug, PartialEq, Eq)]
#[must_use]
pub struct AssignedBit<F: PrimeField>(pub(crate) AssignedNative<F>);

impl<F: PrimeField> Hash for AssignedBit<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<F: PrimeField> InnerValue for AssignedBit<F> {
    type Element = bool;

    fn value(&self) -> Value<bool> {
        self.0.value().map(|b| !F::is_zero_vartime(b))
    }
}

impl<F: PrimeField> From<AssignedBit<F>> for AssignedNative<F> {
    fn from(bit: AssignedBit<F>) -> Self {
        bit.0
    }
}

impl<F> ConversionInstructions<F, AssignedNative<F>, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn convert_value(&self, x: &F) -> Option<bool> {
        let is_zero: bool = F::is_zero(x).into();
        Some(!is_zero)
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let b_value = x.value().map(|v| !F::is_zero_vartime(v));
        let b: AssignedBit<F> = self.assign(layouter, b_value)?;
        self.assert_equal(layouter, x, &b.0)?;
        Ok(b)
    }
}

impl<F> ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn convert_value(&self, x: &bool) -> Option<F> {
        Some(if *x { F::from(1) } else { F::from(0) })
    }

    fn convert(
        &self,
        _layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
    ) -> Result<AssignedNative<F>, Error> {
        Ok(bit.clone().0)
    }
}

impl<F> UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField,
{
    /// CAUTION: use only if you know what you are doing!
    ///
    /// This function converts an `AssignedNative` to an `AssignedBit`
    /// *without* adding any constraints to guarantee the "bitness" of the
    /// assigned value.
    ///
    /// *It should be used only when the input x is already guaranteed to be a
    /// bit*
    fn convert_unsafe(
        &self,
        _layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        #[cfg(not(test))]
        x.value().map(|&x| {
            assert!(
                x == F::ZERO || x == F::ONE,
                "Trying to convert {:?} to an AssignedBit!",
                x
            );
        });
        Ok(AssignedBit(x.clone()))
    }
}

#[cfg(test)]
impl<F> UnsafeConversionInstructions<F, AssignedBit<F>, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn convert_unsafe(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.convert(layouter, x)
    }
}

impl<F> BinaryInstructions<F> for NativeChip<F>
where
    F: PrimeField,
{
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        let mut acc = bits.first().unwrap().0.clone();
        for b in bits.iter().skip(1) {
            acc = self.mul(layouter, &acc, &b.0, None)?;
        }
        Ok(AssignedBit(acc))
    }

    fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        let mut acc = bits.first().unwrap().0.clone();
        for b in bits.iter().skip(1) {
            // compute acc := acc + b - acc * b
            acc = self.add_and_mul(
                layouter,
                (F::ONE, &acc),
                (F::ONE, &b.0),
                (F::ZERO, &acc),
                F::ZERO,
                -F::ONE,
            )?;
        }
        Ok(AssignedBit(acc))
    }

    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        let mut acc = bits.first().unwrap().0.clone();
        for b in bits.iter().skip(1) {
            // compute acc := acc + b - 2 * acc * b
            acc = self.add_and_mul(
                layouter,
                (F::ONE, &acc),
                (F::ONE, &b.0),
                (F::ZERO, &acc),
                F::ZERO,
                -F::from(2),
            )?;
        }
        Ok(AssignedBit(acc))
    }

    fn not(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let neg_bit = self.linear_combination(layouter, &[(-F::ONE, bit.0.clone())], F::ONE)?;
        Ok(AssignedBit(neg_bit))
    }
}

impl<F> EqualityInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField + From<u64> + Neg<Output = F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        // We enforce (x - y) * aux = 1 - res where aux != 0 and res is a bit.
        //  * If x = y, we have 0 = 1 - res, so res must be 1.
        //  * If x != y, res is forced to be 0 as desired (because aux != 0).
        //
        // The equation is enforced as res := - aux * x + aux * y + 1
        let aux_value = x
            .value()
            .zip(y.value())
            .map(|(x, y)| (*x - *y).invert().unwrap_or(F::ONE));
        let aux = self.assign_non_zero(layouter, aux_value)?;
        // res := 0*aux + 0*x + 0*y + 1 - aux*x + aux*y
        let res = self.add_and_double_mul(
            layouter,
            (F::ZERO, &aux),
            (F::ZERO, x),
            (F::ZERO, y),
            F::ONE,
            (-F::ONE, F::ONE),
        )?;
        self.convert(layouter, &res)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<AssignedBit<F>, Error> {
        // We enforce (x - constant) * aux = 1 - res where aux != 0 and res is a bit.
        //  * If x = constant, we have 0 = 1 - res, so res must be 1.
        //  * If x != constant, res is forced to be 0 as desired (because aux != 0).
        //
        // The equation is enforced as res := - x * aux + constant * aux + 1.
        let aux_value = x
            .value()
            .map(|x| (*x - constant).invert().unwrap_or(F::ONE));
        let aux = self.assign_non_zero(layouter, aux_value)?;
        // res := 0*x + constant*aux + 1 - x*aux.
        let res = self.add_and_mul(
            layouter,
            (F::ZERO, x),
            (constant, &aux),
            (F::ZERO, x),
            F::ONE,
            -F::ONE,
        )?;
        self.convert(layouter, &res)
    }
}

impl<F> EqualityInstructions<F, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField + From<u64> + Neg<Output = F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        b1: &AssignedBit<F>,
        b2: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        // TODO: The following could be optimized to just 1 row
        let different = self.xor(layouter, &[b1.clone(), b2.clone()])?;
        self.not(layouter, &different)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        b: &AssignedBit<F>,
        constant: bool,
    ) -> Result<AssignedBit<F>, Error> {
        let assigned_constant = self.assign_fixed(layouter, constant)?;
        self.is_equal(layouter, b, &assigned_constant)
    }
}

impl<F> ControlFlowInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField + From<u64> + Neg<Output = F>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        // Return bit * x + (1 - bit) * y.

        // 0*bit + 0*x + 1*y + 0 + bit*x - bit*y
        self.add_and_double_mul(
            layouter,
            (F::ZERO, &cond.0),
            (F::ZERO, x),
            (F::ONE, y),
            F::ZERO,
            (F::ONE, -F::ONE),
        )
    }
}

impl<F> ControlFlowInstructions<F, AssignedBit<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let bit = self.select(layouter, cond, &x.0, &y.0)?;
        Ok(AssignedBit(bit))
    }
}

impl<F> FieldInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn order(&self) -> BigUint {
        modulus::<F>()
    }
}

impl<F> CanonicityInstructions<F, AssignedNative<F>> for NativeChip<F>
where
    F: PrimeField,
{
    fn le_bits_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        let geq = self.le_bits_geq_than(layouter, bits, bound)?;
        self.not(layouter, &geq)
    }

    fn le_bits_geq_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        // Any value is greater than or equal to zero.
        if bound.is_zero() {
            return self.assign_fixed(layouter, true);
        }

        // Return false if |bits| is lower than |bound|.
        if bits.len() < bound.bits() as usize {
            return self.assign_fixed(layouter, false);
        }

        // base case: bits.len() = 1. We have three cases:
        //  * bound = 0 ==>  true  (already handled)
        //  * bound > 1 ==>  false (already handled)
        //  * bound = 1 ==>  return bits[0] == 1
        if bits.len() == 1 {
            return Ok(bits[0].clone());
        }

        let msb_pos = bits.len() - 1;

        let rest_is_geq = {
            let mut rest_bound = bound.clone();
            rest_bound.set_bit(msb_pos as u64, false);
            self.le_bits_geq_than(layouter, &bits[0..msb_pos], rest_bound)?
        };

        if bound.bit(msb_pos as u64) {
            self.and(layouter, &[bits[msb_pos].clone(), rest_is_geq])
        } else {
            self.or(layouter, &[bits[msb_pos].clone(), rest_is_geq])
        }
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> FromScratch<F> for NativeChip<F> {
    type Config = NativeConfig;

    fn new_from_scratch(config: &Self::Config) -> Self {
        NativeChip::new(config, &())
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let advice_columns: [_; NB_ARITH_COLS] = core::array::from_fn(|_| meta.advice_column());
        let fixed_columns: [_; NB_ARITH_FIXED_COLS] = core::array::from_fn(|_| meta.fixed_column());
        NativeChip::configure(meta, &(advice_columns, fixed_columns, *instance_columns))
    }

    fn load_from_scratch(
        _layouter: &mut impl midnight_proofs::circuit::Layouter<F>,
        _config: &Self::Config,
    ) {
    }
}

#[cfg(test)]
mod tests {
    use blstrs::Fq as BlsScalar;
    use ff::FromUniformBytes;
    use halo2curves::pasta::{Fp as VestaScalar, Fq as PallasScalar};

    use super::*;
    use crate::instructions::{
        arithmetic, assertions, binary, canonicity, control_flow,
        conversions::{
            self,
            tests::Operation::{Convert, UnsafeConvert},
        },
        equality, public_input, zero,
    };

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                $mod::tests::$op::<PallasScalar, AssignedNative<PallasScalar>, NativeChip<PallasScalar>>(
                    "",
                );
                $mod::tests::$op::<VestaScalar, AssignedNative<VestaScalar>, NativeChip<VestaScalar>>(
                    "",
                );
                $mod::tests::$op::<BlsScalar, AssignedNative<BlsScalar>, NativeChip<BlsScalar>>("native_chip", );
            }
        };
    }
    test!(assertions, test_assertions);

    test!(public_input, test_public_inputs);

    test!(arithmetic, test_add);
    test!(arithmetic, test_sub);
    test!(arithmetic, test_mul);
    test!(arithmetic, test_div);
    test!(arithmetic, test_neg);
    test!(arithmetic, test_inv);
    test!(arithmetic, test_pow);
    test!(arithmetic, test_linear_combination);
    test!(arithmetic, test_add_and_mul);

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);

    test!(control_flow, test_select);
    test!(control_flow, test_cond_assert_equal);

    test!(canonicity, test_canonical);
    test!(canonicity, test_le_bits_lower_and_geq);

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                $mod::tests::$op::<PallasScalar, NativeChip<PallasScalar>>("");
                $mod::tests::$op::<VestaScalar, NativeChip<VestaScalar>>("");
                $mod::tests::$op::<BlsScalar, NativeChip<BlsScalar>>("native_chip");
            }
        };
    }

    test!(binary, test_and);
    test!(binary, test_or);
    test!(binary, test_xor);
    test!(binary, test_not);

    fn test_generic_conversion_to_bit<F>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        [
            (
                F::ZERO,
                Some(false),
                Convert,
                true,
                true,
                name,
                "convert_to_bit",
            ),
            (F::ZERO, Some(true), Convert, false, false, "", ""),
            (F::ONE, Some(true), Convert, true, false, "", ""),
            (F::ONE, Some(false), Convert, false, false, "", ""),
            (F::from(2), None, Convert, false, false, "", ""),
            (
                F::from(2),
                None,
                UnsafeConvert,
                true,
                true,
                name,
                "unsafe_convert_to_bit",
            ),
        ]
        .into_iter()
        .for_each(
            |(x, expected, operation, must_pass, cost_model, chip_name, op_name)| {
                conversions::tests::run::<F, AssignedNative<F>, AssignedBit<F>, NativeChip<F>>(
                    x, expected, operation, must_pass, cost_model, chip_name, op_name,
                )
            },
        );
    }

    #[test]
    fn test_conversion_to_bit() {
        test_generic_conversion_to_bit::<PallasScalar>("");
        test_generic_conversion_to_bit::<VestaScalar>("");
        test_generic_conversion_to_bit::<BlsScalar>("native_chip")
    }

    fn test_generic_conversion_from_bit<F>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        [
            (
                false,
                Some(F::ZERO),
                Convert,
                true,
                true,
                name,
                "convert_from_bit",
            ),
            (false, Some(F::ONE), Convert, false, false, "", ""),
            (true, Some(F::ONE), Convert, true, false, "", ""),
            (true, Some(F::ZERO), Convert, false, false, "", ""),
            (
                false,
                None,
                UnsafeConvert,
                true,
                true,
                name,
                "unsafe_convert_from_bit",
            ),
            (true, None, UnsafeConvert, true, false, "", ""),
        ]
        .into_iter()
        .for_each(
            |(x, expected, operation, must_pass, cost_model, chip_name, op_name)| {
                conversions::tests::run::<F, AssignedBit<F>, AssignedNative<F>, NativeChip<F>>(
                    x, expected, operation, must_pass, cost_model, chip_name, op_name,
                )
            },
        );
    }

    #[test]
    fn test_conversion_from_bit() {
        test_generic_conversion_from_bit::<PallasScalar>("");
        test_generic_conversion_from_bit::<VestaScalar>("");
        test_generic_conversion_from_bit::<BlsScalar>("native_chip");
    }
}

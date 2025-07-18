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

//! `field_chip` is a chip for performing arithmetic over emulated fields.
//!  See [here](https://github.com/midnightntwrk/midnight-circuits/wiki/Foreign-Field-Arithmetic)
//!  for a description of the techniques that we use in this implementation.

use std::{
    cmp::{max, min},
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use num_bigint::{BigInt as BI, BigUint, ToBigInt};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::{FromScratch, Sampleable},
    midnight_proofs::plonk::Instance,
    rand::RngCore,
};

use super::gates::{
    mul::{self, MulConfig},
    norm::{self, NormConfig},
};
use crate::{
    field::foreign::{
        params::{check_params, FieldEmulationParams},
        util::{bi_from_limbs, bi_to_limbs},
    },
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, CanonicityInstructions,
        ControlFlowInstructions, ConversionInstructions, DecompositionInstructions,
        EqualityInstructions, FieldInstructions, NativeInstructions, PublicInputInstructions,
        ScalarFieldInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, InnerConstants, InnerValue, Instantiable},
    utils::util::{bigint_to_fe, fe_to_bigint, modulus},
};

/// Type for assigned emulated field elements of K over native field F.
//  - `limb_values` is a vector of assigned cells representing the emulated element in base `base`.
//  - `limb_bounds` is a vector of BigInt pairs containing a lower bound and an upper bound on the
//    values of every limb in `limb_values`. Both bounds are inclusive. The lower bound can be
//    negative; if that is the case, the limb value may have wrapped-around the native modulus below
//    zero, this will be corrected later in the identities.
//
// The integer x represented by limbs [x0, ..., x_{n-1}] is defined as
//   x := 1 + sum_i base^i xi
//
// The +1 shift is introduced so that integer 0 has a unique representation in
// limbs form, this greatly simplifies comparisons with zero.
//
// An AssignedField is well-formed if limb_bounds = (0, base-1).
//
// We will perform additions or subtractions with AssignedField even if they
// are not well-formed, by operating limb-wise and updating the bounds
// accordingly.
//
// However, for multiplication, well-formedness of inputs is a requirement.
// We can use the `normalize` function to make a AssignedField well-formed as long as the
// `limb_bounds` have a moderate size.
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    limb_values: Vec<AssignedNative<F>>,
    limb_bounds: Vec<(BI, BI)>,
    _marker: PhantomData<(K, P)>,
}

impl<F, K, P> PartialEq for AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    fn eq(&self, other: &Self) -> bool {
        self.limb_values
            .iter()
            .zip(other.limb_values.iter())
            .all(|(s, o)| s.cell() == o.cell())
    }
}

impl<F: PrimeField, K: PrimeField, P: FieldEmulationParams<F, K>> Eq for AssignedField<F, K, P> {}

impl<F, K, P> Hash for AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.limb_values.iter().for_each(|elem| elem.hash(state));
    }
}

impl<F, K, P> Instantiable<F> for AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    fn as_public_input(element: &K) -> Vec<F> {
        // We shift the value of x by 1 for the unique-zero representation.
        let element_as_bi = fe_to_bigint(&(*element - K::ONE));
        let base = BI::from(2).pow(P::LOG2_BASE);
        bi_to_limbs(P::NB_LIMBS, &base, &element_as_bi)
            .iter()
            .map(|x| bigint_to_fe::<F>(x))
            .collect()
    }
}

impl<F, K, P> InnerValue for AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    type Element = K;

    fn value(&self) -> Value<K> {
        let bi_limbs = self
            .limb_values
            .iter()
            .zip(self.limb_bounds.iter())
            .map(|(xi, (lower_bound, _))| {
                // We add a shift of |lbound| to correct possible wrap-arounds below 0, and
                // shift back after the conversion from F to BigInt
                let shift = BI::abs(lower_bound);
                let fe_shift = bigint_to_fe::<F>(&shift);
                xi.value()
                    .map(|xv| fe_to_bigint::<F>(&(*xv + fe_shift)) - &shift)
            })
            .collect::<Vec<_>>();
        let bi_limbs: Value<Vec<BI>> = Value::from_iter(bi_limbs);
        let base = BI::from(2).pow(P::LOG2_BASE);
        bi_limbs.map(|limbs| bigint_to_fe::<K>(&(BI::one() + bi_from_limbs(&base, &limbs))))
    }
}

impl<F: PrimeField, K: PrimeField, P> InnerConstants for AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    fn inner_zero() -> K {
        K::ZERO
    }

    fn inner_one() -> K {
        K::ONE
    }
}

impl<F, K, P> AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    /// Create an assigned value with well-formed bounds given its limbs.
    /// This function does not guarantee that the limbs actually meet the
    /// claimed bounds, it is the responsibility of the caller to make sure
    /// that was asserted elsewhere.
    /// DO NOT use this function unless you know what you are doing.
    pub(crate) fn from_limbs_unsafe(limb_values: Vec<AssignedNative<F>>) -> Self {
        debug_assert!(limb_values.len() as u32 == P::NB_LIMBS);
        Self {
            limb_values,
            limb_bounds: well_formed_bounds::<F, K, P>(),
            _marker: PhantomData,
        }
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, K, P> Sampleable for AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    fn sample_inner(rng: impl RngCore) -> K {
        K::random(rng)
    }
}

/// Number of columns required by this chip.
pub fn nb_field_chip_columns<F, K, P>() -> usize
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    P::NB_LIMBS as usize + max(P::NB_LIMBS as usize, 1 + P::moduli().len())
}

/// Creates a vector of upper-bounds (one per limb), specifiying the maximum
/// size (log2) that each limb should take for the emulated field element to be
/// considered well-formed.
/// All such bounds will be equal to the base, except possibly the bound for
/// the most significant limb, which may be smaller in order to guarantee that
/// 0 has a unique representation.
pub fn well_formed_log2_bounds<F, K, P>() -> Vec<u32>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    // Let m be the emulated modulus.
    // We want that m <= base^(nb_limbs - 1) * msl_bound < 2m,
    // therefore msl_bound must be the first power of 2 higher than or equal to
    // m / base^(nb_limbs - 1).
    let m = &modulus::<K>().to_bigint().unwrap();
    let log2_msl_bound = m.bits() as u32 - (P::NB_LIMBS - 1) * P::LOG2_BASE;
    let mut bounds = vec![log2_msl_bound];
    bounds.resize(P::NB_LIMBS as usize, P::LOG2_BASE);
    bounds.into_iter().rev().collect::<Vec<_>>()
}

/// Foreign Field Chip configuration.
// - q_mul is the se to enable the emulated multiplication gate.
// - q_norm is the selector to enable the normalization gate.
// - x and y are the inputs (in limbs form).
// - z is the output (in limbs form).
// - u, u_mul_bounds, u_norm_bounds, v, vs_mul_bounds and vs_norm_bounds parameters involved in the
//   identities, refer to [mul_bounds] and [normalization_bounds] for more details.
#[derive(Clone, Debug)]
pub struct FieldChipConfig {
    mul_config: mul::MulConfig,
    norm_config: norm::NormConfig,
    /// Column for input x
    pub x_cols: Vec<Column<Advice>>,
    /// Column for input y
    pub y_cols: Vec<Column<Advice>>,
    /// Column for input/output z
    pub z_cols: Vec<Column<Advice>>,
    /// Column for auxiliary value u (quotient by the emulated modulus)
    pub u_col: Column<Advice>,
    /// Column for auxiliary values vj (quotients by the auxiliary moduli)
    pub v_cols: Vec<Column<Advice>>,
}

/// ['FieldChip'] for operations on field K emulated over native field F.
#[derive(Clone, Debug)]
pub struct FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    config: FieldChipConfig,
    pub(crate) native_gadget: N,
    _marker: PhantomData<(F, K, P, N)>,
}

impl<F, K, P> AssignedField<F, K, P>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    /// The modulus defining the domain of this emulated field element.
    pub fn modulus(&self) -> BI {
        modulus::<K>().to_bigint().unwrap().clone()
    }

    /// Tells whether the given emulated field element is well-formed, i.e., the
    /// limb_bounds match expected range.
    ///
    /// AssignedField whose range is more restricted but included in the
    /// expected one are also considered well-formed.
    pub fn is_well_formed(&self) -> bool {
        self.limb_bounds
            .iter()
            .zip(well_formed_log2_bounds::<F, K, P>())
            .all(|((lower, upper), expected_upper)| {
                assert!(lower <= upper);
                !BI::is_negative(lower) && upper.bits() <= expected_upper as u64
            })
    }

    /// The limb values associated to the given AssignedField.
    /// Recall that the integer represented by limbs [x0, ..., x_{n-1}] is
    /// x := 1 + sum_i base^i xi
    pub fn limb_values(&self) -> Vec<AssignedNative<F>> {
        self.limb_values.clone()
    }

    /// The limb values (in BigInt form) associated to the given AssignedField.
    pub fn bigint_limbs(&self) -> Value<Vec<BI>> {
        let limbs = self
            .limb_values
            .iter()
            .zip(self.limb_bounds.iter())
            .map(|(xi, (lbound, _))| {
                // We add a shift of |lbound| to correct possible wrap-arounds below 0, and
                // shift back after the conversion from F to BigInt
                let shift = BI::abs(lbound);
                let fe_shift = bigint_to_fe::<F>(&shift);
                xi.value()
                    .map(|xv| fe_to_bigint::<F>(&(*xv + fe_shift)) - &shift)
            })
            .collect::<Vec<_>>();
        Value::from_iter(limbs)
    }
}

/// A vector of `NB_LIMBS` bounds of the form [0, base), except for possibly the
/// most significant limb, which may be of the form [0, 2^k) with 2^k <= base.
/// This is so that there exist emulated field elements with a unique
/// representation (even if some of them have two representations).
fn well_formed_bounds<F, K, P>() -> Vec<(BI, BI)>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    well_formed_log2_bounds::<F, K, P>()
        .into_iter()
        .map(|log2_base| (BI::zero(), BI::from(2).pow(log2_base) - BI::one()))
        .collect()
}

// The limbs of emulated zero.
fn limbs_of_zero<F, K, P>() -> Vec<BI>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    bi_to_limbs(
        P::NB_LIMBS,
        &BI::from(2).pow(P::LOG2_BASE),
        &(modulus::<K>().to_bigint().unwrap() - BI::one()),
    )
}

impl<F, K, P, N> Chip<F> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    type Config = FieldChipConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F, K, P, N> AssignmentInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Value<K>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let base = BI::from(2).pow(P::LOG2_BASE);
        // We shift the value of x by 1, remember that limbs {xi}_i represent integer
        //   1 + sum_i base^i xi
        let x = x.map(|v| {
            let bi = fe_to_bigint(&(v - K::ONE));
            bi_to_limbs(P::NB_LIMBS, &base, &bi)
        });

        // Range-check the cells in the range [0, base)
        let x_cells = (0..P::NB_LIMBS)
            .map(|i| x.clone().map(|limbs| bigint_to_fe::<F>(&limbs[i as usize])))
            .zip(well_formed_log2_bounds::<F, K, P>().iter())
            .map(|(xi_value, log2_bound)| {
                self.native_gadget.assign_lower_than_fixed(
                    layouter,
                    xi_value,
                    &(BigUint::one() << *log2_bound),
                )
            })
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(AssignedField::<F, K, P> {
            limb_values: x_cells,
            limb_bounds: well_formed_bounds::<F, K, P>(),
            _marker: PhantomData,
        })
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: K,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let base = BI::from(2).pow(P::LOG2_BASE);
        // We shift the value of x by 1, remember that limbs {xi}_i represent integer
        //   1 + sum_i base^i xi
        let constant = fe_to_bigint(&(constant - K::ONE));
        let constant_limbs = bi_to_limbs(P::NB_LIMBS, &base, &constant);
        let constant_cells = constant_limbs
            .iter()
            .map(|x| {
                self.native_gadget
                    .assign_fixed(layouter, bigint_to_fe::<F>(x))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // All limbs will be in the range [0, base) by construction, no range-checks are
        // needed.
        // WARNING: We use "loose" bounds (`well_formed_bounds::<F, K, P>()`) here even
        // if we know for certain that the cells contain a constant. This is to
        // avoid a potential completeness issue when calling `assert_equal`.
        // (Using tight bounds could result in an unsatisfiable equal assertion between
        // two equal field elements: one in canonical form and the other one in the
        // non-canonical (but well-formed) form, making the assertion fail when it
        // should not.)
        Ok(AssignedField::<F, K, P> {
            limb_values: constant_cells,
            limb_bounds: well_formed_bounds::<F, K, P>(),
            _marker: PhantomData,
        })
    }
}

// This conversion should be treated as opaque, it is useful for dealing with
// public inputs.
impl<F, K, P> From<AssignedField<F, K, P>> for Vec<AssignedNative<F>>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    fn from(x: AssignedField<F, K, P>) -> Self {
        x.limb_values()
    }
}

impl<F, K, P, N> PublicInputInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedField<F, K, P>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        let assigned = self.normalize(layouter, assigned)?;
        Ok(assigned.limb_values)
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedField<F, K, P>,
    ) -> Result<(), Error> {
        self.as_public_input(layouter, assigned)?
            .iter()
            .try_for_each(|c| self.native_gadget.constrain_as_public_input(layouter, c))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<K>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let base = BI::from(2).pow(P::LOG2_BASE);
        // We subtract one due to the unique-zero representation.
        let x = value.map(|v| bi_to_limbs(P::NB_LIMBS, &base, &fe_to_bigint(&(v - K::ONE))));
        let limbs = (0..P::NB_LIMBS)
            .map(|i| x.clone().map(|limbs| bigint_to_fe::<F>(&limbs[i as usize])))
            .collect::<Vec<_>>();
        // We can skip all range-checks given that the assigned field element will be
        // constrained with public inputs, thus that structure will be enforced anyway.
        let assigned_limbs = self.native_gadget.assign_many(layouter, &limbs)?;
        let assigned_field = AssignedField::<F, K, P> {
            limb_values: assigned_limbs,
            limb_bounds: well_formed_bounds::<F, K, P>(),
            _marker: PhantomData,
        };
        self.constrain_as_public_input(layouter, &assigned_field)?;
        Ok(assigned_field)
    }
}

impl<F, K, P, N> AssertionInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<(), Error> {
        // We normalize the x and y before comparing them.
        // Even though field elements may admit several representations in
        // well-formed limbs form, an honest prover will use the canonical one,
        // which allows them to always pass the following equality assertion if the two
        // emulated field elements are indeed equal.
        let x = self.normalize(layouter, x)?;
        let y = self.normalize(layouter, y)?;
        x.limb_values
            .iter()
            .zip(y.limb_values.iter())
            .map(|(xi, yi)| self.native_gadget.assert_equal(layouter, xi, yi))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<(), Error> {
        let diff = self.sub(layouter, x, y)?;
        self.assert_non_zero(layouter, &diff)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        constant: K,
    ) -> Result<(), Error> {
        // We normalize x before comparing it to the constant.
        // Even though field elements may admit several representations in
        // well-formed limbs form, an honest prover will use the canonical one,
        // which allows them to always pass the following equality assertion if the x
        // is indeed equal to the given constant.
        let x = self.normalize(layouter, x)?;
        let constant_limbs = {
            let constant = fe_to_bigint(&(constant - K::ONE));
            let base = BI::from(2).pow(P::LOG2_BASE);
            bi_to_limbs(P::NB_LIMBS, &base, &constant)
        };
        x.limb_values
            .iter()
            .zip(constant_limbs.iter())
            .map(|(xi, ki)| {
                self.native_gadget
                    .assert_equal_to_fixed(layouter, xi, bigint_to_fe::<F>(ki))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        constant: K,
    ) -> Result<(), Error> {
        let diff = self.add_constant(layouter, x, -constant)?;
        self.assert_non_zero(layouter, &diff)
    }
}

impl<F, K, P, N> EqualityInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<AssignedBit<F>, Error> {
        let diff = self.sub(layouter, x, y)?;
        self.is_zero(layouter, &diff)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        constant: <AssignedField<F, K, P> as InnerValue>::Element,
    ) -> Result<AssignedBit<F>, Error> {
        let diff = self.add_constant(layouter, x, -constant)?;
        self.is_zero(layouter, &diff)
    }
}

impl<F, K, P, N> ZeroInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn assert_non_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<(), Error> {
        let b = self.is_zero(layouter, x)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &b, false)
    }

    fn is_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedBit<F>, Error> {
        // Zero has a unique representation in limbs form, we can simply make sure that
        // the limbs of x are all equal to the limbs of zero.
        let x = self.normalize(layouter, x)?;
        let bs = x
            .limb_values
            .iter()
            .zip(limbs_of_zero::<F, K, P>().iter())
            .map(|(xi, ci)| {
                self.native_gadget
                    .is_equal_to_fixed(layouter, xi, bigint_to_fe::<F>(ci))
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.native_gadget.and(layouter, &bs)
    }
}

impl<F, K, P, N> ControlFlowInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let z_limb_values = x
            .limb_values
            .iter()
            .zip(y.limb_values.iter())
            .map(|(xi, yi)| self.native_gadget.select(layouter, cond, xi, yi))
            .collect::<Result<Vec<_>, _>>()?;
        let z_limb_bounds = x
            .limb_bounds
            .iter()
            .zip(y.limb_bounds.iter())
            .map(|(xi_bounds, yi_bounds)| {
                (
                    min(&xi_bounds.0, &yi_bounds.0).clone(),
                    max(&xi_bounds.1, &yi_bounds.1).clone(),
                )
            })
            .collect::<Vec<_>>();
        Ok(AssignedField::<F, K, P> {
            limb_values: z_limb_values,
            limb_bounds: z_limb_bounds,
            _marker: PhantomData,
        })
    }
}

impl<F, K, P, N> ArithInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(K, AssignedField<F, K, P>)],
        constant: K,
    ) -> Result<AssignedField<F, K, P>, Error> {
        // We fold over mul_by_constant and add and only normalize at the end.
        let init: AssignedField<F, K, P> = self.assign_fixed(layouter, constant)?;
        let res = terms.iter().try_fold(init, |acc, (c, x)| {
            let prod = self.mul_by_constant(layouter, x, *c)?;
            self.add(layouter, &acc, &prod)
        })?;
        self.normalize_if_approaching_limit(layouter, &res)
    }

    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let zero: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ZERO)?;

        if x == &zero {
            return Ok(y.clone());
        }

        if y == &zero {
            return Ok(x.clone());
        }

        // Note that x := 1 + sum_i base^i xi and y := 1 + sum_i base^i yi.
        // Thus z = (x + y) is equal to 2 + sum_i base^i (xi + yi).
        // Observe there is a 2 instead of the implicit 1, thus we cannot simply add the
        // limbs of x and y pair-wise. We also need to add a factor of +1 to the
        // least-significant limb to account for this difference.

        let mut constants = vec![BI::one()];
        constants.resize(P::NB_LIMBS as usize, BI::zero());

        let z_limb_values = x
            .limb_values
            .iter()
            .zip(y.limb_values.iter())
            .zip(constants.iter().map(|ci| bigint_to_fe::<F>(ci)))
            .map(|((xi, yi), ci)| {
                self.native_gadget.linear_combination(
                    layouter,
                    &[(F::ONE, xi.clone()), (F::ONE, yi.clone())],
                    ci,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let z = AssignedField::<F, K, P> {
            limb_values: z_limb_values,
            limb_bounds: x
                .limb_bounds
                .iter()
                .zip(y.limb_bounds.iter())
                .zip(constants.iter())
                .map(|((xi_bounds, yi_bounds), ci)| {
                    (
                        &xi_bounds.0 + &yi_bounds.0 + ci,
                        &xi_bounds.1 + &yi_bounds.1 + ci,
                    )
                })
                .collect(),
            _marker: PhantomData,
        };
        self.normalize_if_approaching_limit(layouter, &z)
    }

    fn sub(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let zero: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ZERO)?;

        if y == &zero {
            return Ok(x.clone());
        }

        // Note that x := 1 + sum_i base^i xi and y := 1 + sum_i base^i yi.
        // Thus z = (x - y) is equal to 0 + sum_i base^i (xi + yi).
        // Observe there is a 0 instead of the implicit 1, thus we cannot simply
        // subtract the limbs of x and y pair-wise. We also need to add a factor
        // of -1 to the least-significant limb to account for this difference.

        let mut constants = vec![BI::from(-1)];
        constants.resize(P::NB_LIMBS as usize, BI::zero());

        let z_limb_values = x
            .limb_values
            .iter()
            .zip(y.limb_values.iter())
            .zip(constants.iter().map(|ci| bigint_to_fe::<F>(ci)))
            .map(|((xi, yi), ci)| {
                self.native_gadget.linear_combination(
                    layouter,
                    &[(F::ONE, xi.clone()), (-F::ONE, yi.clone())],
                    ci,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let z = AssignedField::<F, K, P> {
            limb_values: z_limb_values,
            limb_bounds: x
                .limb_bounds
                .iter()
                .zip(y.limb_bounds.iter())
                .zip(constants.iter())
                .map(|((xi_bounds, yi_bounds), ci)| {
                    (
                        &xi_bounds.0 - &yi_bounds.1 + ci,
                        &xi_bounds.1 - &yi_bounds.0 + ci,
                    )
                })
                .collect(),
            _marker: PhantomData,
        };
        self.normalize_if_approaching_limit(layouter, &z)
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
        multiplying_constant: Option<K>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let zero: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ZERO)?;
        let one: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ONE)?;

        if x == &zero || y == &zero {
            return Ok(zero);
        }

        if x == &one {
            return Ok(y.clone());
        }

        if y == &one {
            return Ok(x.clone());
        }

        let y = match multiplying_constant {
            None => y.clone(),
            Some(k) => self.mul_by_constant(layouter, y, k)?,
        };
        self.assign_mul(layouter, x, &y, false)
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let one: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ONE)?;
        if y == &one {
            return Ok(x.clone());
        }

        let y = self.normalize(layouter, y)?;
        self.assert_non_zero(layouter, &y)?;
        self.assign_mul(layouter, x, &y, true)
    }

    fn neg(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let zero: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ZERO)?;

        if x == &zero {
            return Ok(zero);
        }

        // Note that x := 1 + sum_i base^i xi.
        // Thus z = -x is equal to -1 + sum_i base^i (xi + yi).
        // Observe there is a -1 instead of the implicit 1, thus we cannot simply negate
        // the limbs of x. We also need to add a factor of -2 to the least-significant
        // limb to account for this difference.

        let mut constants = vec![BI::from(-2)];
        constants.resize(P::NB_LIMBS as usize, BI::zero());

        let z_limb_values = x
            .limb_values
            .iter()
            .zip(constants.iter().map(|ci| bigint_to_fe::<F>(ci)))
            .map(|(xi, ci)| {
                self.native_gadget
                    .linear_combination(layouter, &[(-F::ONE, xi.clone())], ci)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let z = AssignedField::<F, K, P> {
            limb_values: z_limb_values,
            limb_bounds: x
                .limb_bounds
                .iter()
                .zip(constants.iter())
                .map(|(xi_bounds, ci)| (-&xi_bounds.1 + ci, -&xi_bounds.0 + ci))
                .collect(),
            _marker: PhantomData,
        };
        self.normalize_if_approaching_limit(layouter, &z)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let one: AssignedField<F, K, P> = self.assign_fixed(layouter, K::ZERO)?;

        if x == &one {
            return Ok(one);
        }

        // We do not need to assert that x != 0 because the equation enforced by
        // [assign_mul] will be 1 = z * x, which is unsatisfiable if x = 0.
        let one = self.assign_fixed(layouter, K::ONE)?;
        self.assign_mul(layouter, &one, x, true)
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let is_zero = self.is_zero(layouter, x)?;
        let zero = self.assign_fixed(layouter, K::ZERO)?;
        let one = self.assign_fixed(layouter, K::ONE)?;
        let invertible = self.select(layouter, &is_zero, &one, x)?;
        let inverse = self.assign_mul(layouter, &one, &invertible, true)?;
        self.select(layouter, &is_zero, &zero, &inverse)
    }

    fn add_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        k: K,
    ) -> Result<AssignedField<F, K, P>, Error> {
        // The following is more efficient than simply:
        //
        //   let constant = self.assign_fixed(layouter, k)?;
        //   self.add(layouter, x, &assign_fixed)
        //
        // as we do not create cells for the constant limbs.

        if k.is_zero().into() {
            return Ok(x.clone());
        }

        let base = BI::from(2).pow(P::LOG2_BASE);
        let k_limbs = bi_to_limbs(P::NB_LIMBS, &base, &fe_to_bigint(&k));

        let z_limb_values = {
            self.native_gadget.add_constants(
                layouter,
                &x.limb_values,
                &k_limbs.iter().map(bigint_to_fe::<F>).collect::<Vec<_>>(),
            )?
        };

        let z = AssignedField::<F, K, P> {
            limb_values: z_limb_values,
            limb_bounds: x
                .limb_bounds
                .iter()
                .zip(k_limbs.iter())
                .map(|(xi_bound, ki)| (&xi_bound.0 + ki, &xi_bound.1 + ki))
                .collect(),
            _marker: PhantomData,
        };
        self.normalize_if_approaching_limit(layouter, &z)
    }

    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        k: K,
    ) -> Result<AssignedField<F, K, P>, Error> {
        if k.is_zero().into() {
            return self.assign_fixed(layouter, K::ZERO);
        }

        if k == K::ONE {
            return Ok(x.clone());
        }

        // If the constant is too big, we should multiply normally instead.
        // This threshold is just a heuristic, it will allow us to perform about 1000
        // sums after this multiplication without normalization.
        // We will get an error when compiling the circuit if the max_limb_bound is
        // violated, so the choice of this threshold is not critical for soundness.
        let threshold =
            P::max_limb_bound().div_floor(&(BI::from(1000) * BI::from(2).pow(P::LOG2_BASE)));
        if fe_to_bigint(&k) > threshold {
            let assigned_k = self.assign_fixed(layouter, k)?;
            return self.assign_mul(layouter, x, &assigned_k, false);
        }

        // At this point we know that k is small enough (k <= threshold) thus we can
        // proceed by multiplying the constant by every limb.

        // Note that x := 1 + sum_i base^i xi.
        // Thus z = k * x is equal to k + sum_i base^i (k * xi).
        // Observe there is a k instead of the implicit 1, thus we cannot simply
        // multiply the limbs of x by k. We also need to add a factor of (k-1)
        // to the least-significant limb to account for this difference.

        // Yes, we convert it to F (the wrong - but native - field), but this is fine
        // because the constant has been verified to be small.
        let k_as_bigint = fe_to_bigint(&k);
        let kv = bigint_to_fe::<F>(&k_as_bigint);
        // We've also checked k != 0 and k != 1, so it is fine to subtract one here.
        // (for the unique-zero representation).
        let mut constants = vec![k_as_bigint.clone() - BI::one()];
        constants.resize(P::NB_LIMBS as usize, BI::zero());

        let z_limb_values = x
            .limb_values
            .iter()
            .zip(constants.iter().map(|ci| bigint_to_fe::<F>(ci)))
            .map(|(xi, ci)| {
                self.native_gadget
                    .linear_combination(layouter, &[(kv, xi.clone())], ci)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let limb_bounds = x
            .limb_bounds
            .iter()
            .zip(constants.iter())
            .map(|(xi_bounds, ci)| {
                (
                    &xi_bounds.0 * k_as_bigint.clone() + ci,
                    &xi_bounds.1 * k_as_bigint.clone() + ci,
                )
            })
            .collect();

        let z = AssignedField::<F, K, P> {
            limb_values: z_limb_values,
            limb_bounds,
            _marker: PhantomData,
        };
        self.normalize_if_approaching_limit(layouter, &z)
    }
}

impl<F, K, P, N> FieldInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn order(&self) -> BigUint {
        modulus::<K>()
    }
}

impl<F, K, P, N> ScalarFieldInstructions<F> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    type Scalar = AssignedField<F, K, P>;
}

impl<F, K, P, N> DecompositionInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn assigned_to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        // Add one to account for the extra +1 in the unique-zero representation.
        let mut x = self.add_constant(layouter, x, K::ONE)?;
        if enforce_canonical {
            x = self.make_canonical(layouter, &x)?;
        };
        let mut bits = vec![];
        x.limb_values
            .iter()
            .zip(well_formed_log2_bounds::<F, K, P>().iter())
            .map(|(cell, log2_bound)| {
                self.native_gadget.assigned_to_le_bits(
                    layouter,
                    cell,
                    Some(*log2_bound as usize),
                    true,
                )
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .for_each(|new_bits| bits.extend(new_bits));

        // Drop the most significant bits up to the desired length, but make sure
        // they encode 0.
        let nb_bits = nb_bits.unwrap_or(K::NUM_BITS as usize);
        bits[nb_bits..].iter().try_for_each(|byte| {
            self.native_gadget
                .assert_equal_to_fixed(layouter, byte, false)
        })?;
        let bits = bits[0..nb_bits].to_vec();
        if enforce_canonical && nb_bits >= K::NUM_BITS as usize {
            let canonical = self.is_canonical(layouter, &bits)?;
            self.assert_equal_to_fixed(layouter, &canonical, true)?;
        }
        Ok(bits)
    }

    fn assigned_to_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let nb_bytes = nb_bytes.unwrap_or(K::NUM_BITS.div_ceil(8) as usize);
        // The following could be further optimzed when 8 divides LOG2_BASE.
        let bits = self.assigned_to_le_bits(layouter, x, Some(nb_bytes * 8), true)?;
        let bytes = bits
            .chunks(8)
            .map(|chunk| {
                let terms = chunk
                    .iter()
                    .enumerate()
                    .map(|(i, bit)| (F::from(1 << i), bit.clone().into()))
                    .collect::<Vec<_>>();
                let byte = self
                    .native_gadget
                    .linear_combination(layouter, &terms, F::ZERO)?;
                self.native_gadget.convert_unsafe(layouter, &byte)
            })
            .collect::<Result<Vec<AssignedByte<F>>, Error>>()?;

        // Drop the most significant bytes up to the desired length, but make sure
        // they encode 0.
        bytes[nb_bytes..].iter().try_for_each(|byte| {
            self.native_gadget
                .assert_equal_to_fixed(layouter, byte, 0u8)
        })?;
        Ok(bytes[0..nb_bytes].to_vec())
    }

    fn assigned_from_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedField<F, K, P>, Error> {
        let mut coeff = K::ONE;
        let mut terms = vec![];
        for chunk in bits.chunks(P::LOG2_BASE as usize) {
            let mut native_coeff = F::ONE;
            let mut native_terms = vec![];
            for b in chunk.iter() {
                let bit: AssignedNative<F> = b.clone().into();
                native_terms.push((native_coeff, bit));
                native_coeff = native_coeff + native_coeff;
            }
            let term = {
                let limb =
                    self.native_gadget
                        .linear_combination(layouter, &native_terms, F::ZERO)?;
                self.assigned_field_from_limb(layouter, &limb)?
            };
            terms.push((coeff, term));
            coeff = bigint_to_fe::<K>(&BI::from(2).pow(P::LOG2_BASE)) * coeff;
        }
        let x = self.linear_combination(layouter, &terms, K::ZERO)?;
        self.normalize(layouter, &x)
    }

    fn assigned_from_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<AssignedField<F, K, P>, Error> {
        let mut coeff = K::ONE;
        let mut terms = vec![];
        let nb_bytes_per_chunk = P::LOG2_BASE / 8;
        for chunk in bytes.chunks(nb_bytes_per_chunk as usize) {
            let mut native_coeff = F::ONE;
            let mut native_terms = vec![];
            for b in chunk.iter() {
                let byte: AssignedNative<F> = b.clone().into();
                native_terms.push((native_coeff, byte));
                native_coeff = F::from(256) * native_coeff;
            }
            let term = {
                let limb =
                    self.native_gadget
                        .linear_combination(layouter, &native_terms, F::ZERO)?;
                self.assigned_field_from_limb(layouter, &limb)?
            };
            terms.push((coeff, term));
            coeff = bigint_to_fe::<K>(&BI::from(2).pow(8 * nb_bytes_per_chunk)) * coeff;
        }
        let x = self.linear_combination(layouter, &terms, K::ZERO)?;
        self.normalize(layouter, &x)
    }

    fn assigned_to_le_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        nb_bits_per_chunk: usize,
        nb_chunks: Option<usize>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert!(nb_bits_per_chunk < F::NUM_BITS as usize);
        if P::LOG2_BASE % (nb_bits_per_chunk as u32) == 0 {
            let nb_chunks_per_limb = (P::LOG2_BASE / (nb_bits_per_chunk as u32)) as usize;
            let mut nb_missing_chunks =
                nb_chunks.unwrap_or(nb_chunks_per_limb * P::NB_LIMBS as usize);
            // Add one to account for the extra +1 in the unique-zero representation.
            let x = self.add_constant(layouter, x, K::ONE)?;
            let x = self.normalize(layouter, &x)?;
            let chunks = x
                .limb_values
                .iter()
                .map(|limb| {
                    let nb_chunks_on_this_limb = min(nb_missing_chunks, nb_chunks_per_limb);
                    nb_missing_chunks -= nb_chunks_on_this_limb;
                    self.native_gadget.assigned_to_le_chunks(
                        layouter,
                        limb,
                        nb_bits_per_chunk,
                        Some(nb_chunks_on_this_limb),
                    )
                })
                .collect::<Result<Vec<_>, Error>>()?
                .concat();
            assert_eq!(nb_missing_chunks, 0);
            Ok(chunks)
        }
        // When nb_bits_per_chunk does not divide P::LOG2_BASE we cannot proceed as above,
        // let's split in bits and then aggregate chunks, this is a bit less efficient.
        else {
            let bits = self.assigned_to_le_bits(layouter, x, None, false)?;
            bits.chunks(nb_bits_per_chunk)
                .map(|bits_of_chunk| {
                    self.native_gadget
                        .assigned_from_le_bits(layouter, bits_of_chunk)
                })
                .collect::<Result<Vec<_>, Error>>()
        }
    }
}

impl<F, K, P, N> FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    /// Given config creates new emulated field chip.
    pub fn new(config: &FieldChipConfig, native_gadget: &N) -> Self {
        Self {
            config: config.clone(),
            native_gadget: native_gadget.clone(),
            _marker: PhantomData,
        }
    }

    /// Configures the emulated field chip.
    /// `advice_columns` should contain at least as many columns as this chip
    /// requires, namely `nb_field_chip_columns::<P>()`.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice_columns: &[Column<Advice>],
    ) -> FieldChipConfig {
        check_params::<F, K, P>();

        let nb_limbs = P::NB_LIMBS;
        let x_cols = advice_columns[..(nb_limbs as usize)].to_vec();
        let y_cols = x_cols.clone();
        let z_cols = advice_columns[(nb_limbs as usize)..(2 * nb_limbs as usize)].to_vec();

        x_cols
            .iter()
            .chain(z_cols.iter())
            .for_each(|&col| meta.enable_equality(col));

        let u_col = advice_columns[nb_limbs as usize];
        let v_cols = advice_columns
            [(nb_limbs as usize + 1)..(nb_limbs as usize + 1 + P::moduli().len())]
            .to_vec();

        let mul_config = MulConfig::configure::<F, K, P>(meta, &x_cols, &z_cols);
        let norm_config = NormConfig::configure::<F, K, P>(meta, &x_cols, &z_cols);

        FieldChipConfig {
            mul_config,
            norm_config,
            x_cols,
            y_cols,
            z_cols,
            u_col,
            v_cols,
        }
    }

    // Creates a new AssignedField z, asserted to be well-formed and satisfy
    // the emulated field relation x * y = z.
    // If the [division] flag is set, the relation becomes z * y = x, in order to
    // model the division (z = x / y).
    // WARNING: When used for division, we must independently assert that y != 0
    // (note that when y = 0, any value for z would satisfy the relation if x = 0).
    fn assign_mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
        y: &AssignedField<F, K, P>,
        division: bool,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let base = BI::from(2).pow(P::LOG2_BASE);
        let nb_limbs = P::NB_LIMBS;

        let x = self.normalize(layouter, x)?;
        let y = self.normalize(layouter, y)?;

        y.value()
            .error_if_known_and(|yv| division && K::is_zero(yv).into())?;

        let zv = x
            .value()
            .zip(y.value())
            .map(|(xv, yv)| {
                if division {
                    xv * yv.invert().unwrap()
                } else {
                    xv * yv
                }
            })
            .map(|z| bi_to_limbs(nb_limbs, &base, &fe_to_bigint(&(z - K::ONE))));
        let z_values = (0..nb_limbs)
            .map(|i| zv.clone().map(|zs| bigint_to_fe::<F>(&zs[i as usize])))
            .collect::<Vec<_>>();

        // Assign and range-check the z limbs
        let z_limbs = z_values
            .iter()
            .zip(well_formed_log2_bounds::<F, K, P>().iter())
            .map(|(&z_value, &log2_bound)| {
                self.native_gadget.assign_lower_than_fixed(
                    layouter,
                    z_value,
                    &(BigUint::one() << log2_bound),
                )
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let z = AssignedField::<F, K, P> {
            limb_values: z_limbs,
            limb_bounds: well_formed_bounds::<F, K, P>(),
            _marker: PhantomData,
        };

        // Divisions z = x / y are modeled as multiplications z * y = x.
        // We swap x and z when division = true.
        let (l, r) = if !division { (&x, &z) } else { (&z, &x) };
        mul::assert_mul::<F, K, P, N>(
            layouter,
            l,
            &y,
            r,
            &self.config.mul_config,
            &self.native_gadget,
        )?;

        Ok(z)
    }
}

impl<F, K, P, N> FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    /// Normalizes the given assigned field element, but only if its bounds
    /// exceed the limits of the well-formed bounds.
    pub(crate) fn normalize(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        if x.is_well_formed() {
            Ok(x.clone())
        } else {
            self.make_canonical(layouter, x)
        }
    }

    /// Normalizes the given assigned field element, but only if its bounds
    /// are approaching the limits of the well-formed bounds.
    pub(crate) fn normalize_if_approaching_limit(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        // This threshold was chosen empirically.
        let threshold: BI = P::max_limb_bound() / 10;
        let dangerous_lower_bounds = x.limb_bounds.iter().any(|b| b.0 < -threshold.clone());
        let dangerous_upper_bounds = x.limb_bounds.iter().any(|b| b.1 > threshold);
        if dangerous_lower_bounds || dangerous_upper_bounds {
            self.make_canonical(layouter, x)
        } else {
            Ok(x.clone())
        }
    }

    /// Converts the given assigned field element into an equivalent one
    /// represented in canonical form, through the normalization procedure.
    fn make_canonical(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedField<F, K, P>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let max_limb_bound = P::max_limb_bound();
        x.limb_bounds.iter().for_each(|(lower, upper)| {
            if lower < &(-&max_limb_bound) || upper > &max_limb_bound {
                panic!(
                    "make_canonical: the limb bounds of the input: [{}, {}] exceed the
                     maximum limb bound value {}; consider applying a normalization
                     earlier, when the bounds are still within the permited range;
                     increasing the [max_limb_bound] of your FieldEmulationParams could also
                     help, if possible.",
                    lower, upper, max_limb_bound
                );
            }
        });
        let z_limbs = norm::normalize::<F, K, P, N>(
            layouter,
            x,
            &self.config.norm_config,
            &self.native_gadget,
        )?;
        let z = AssignedField::<F, K, P> {
            limb_values: z_limbs,
            limb_bounds: well_formed_bounds::<F, K, P>(),
            _marker: PhantomData,
        };
        Ok(z)
    }

    /// This function should only be called once the limb has been asserted to
    /// be in the range [0, base).
    fn assigned_field_from_limb(
        &self,
        layouter: &mut impl Layouter<F>,
        limb: &AssignedNative<F>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        // Subtract one for the unique-zero representation.
        let least_significant_limb = self.native_gadget.add_constant(layouter, limb, -F::ONE)?;
        let mut limb_values = vec![least_significant_limb];
        let mut limb_bounds = well_formed_bounds::<F, K, P>();
        let zero = self.native_gadget.assign_fixed(layouter, F::ZERO)?;
        limb_values.resize(P::NB_LIMBS as usize, zero);
        limb_bounds[0] = (limb_bounds[0].clone().0 - 1, limb_bounds[0].clone().1 - 1);
        Ok(AssignedField::<F, K, P> {
            limb_values,
            limb_bounds,
            _marker: PhantomData,
        })
    }
}

// Inherit Bit Assignment Instructions from NativeGadget.
impl<F, K, P, N> AssignmentInstructions<F, AssignedBit<F>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<bool>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: bool,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.assign_fixed(layouter, constant)
    }
}

// Inherit Bit Assertion Instructions from NativeGadget.
impl<F, K, P, N> AssertionInstructions<F, AssignedBit<F>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_gadget.assert_equal(layouter, x, y)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_gadget.assert_not_equal(layouter, x, y)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        constant: bool,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_equal_to_fixed(layouter, x, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        constant: bool,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_not_equal_to_fixed(layouter, x, constant)
    }
}

impl<F, K, P, N> ConversionInstructions<F, AssignedBit<F>, AssignedField<F, K, P>>
    for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn convert_value(&self, x: &bool) -> Option<K> {
        Some(if *x { K::ONE } else { K::ZERO })
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let x: AssignedNative<F> = x.clone().into();
        self.assigned_field_from_limb(layouter, &x)
    }
}

impl<F, K, P, N> ConversionInstructions<F, AssignedByte<F>, AssignedField<F, K, P>>
    for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn convert_value(&self, x: &u8) -> Option<K> {
        Some(K::from(*x as u64))
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedByte<F>,
    ) -> Result<AssignedField<F, K, P>, Error> {
        let x: AssignedNative<F> = x.clone().into();
        self.assigned_field_from_limb(layouter, &x)
    }
}

// Inherit Canonicity Instructions from NativeGadget.
impl<F, K, P, N> CanonicityInstructions<F, AssignedField<F, K, P>> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F>,
{
    fn le_bits_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.le_bits_lower_than(layouter, bits, bound)
    }

    fn le_bits_geq_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.le_bits_geq_than(layouter, bits, bound)
    }
}

#[derive(Clone, Debug)]
#[cfg(any(test, feature = "testing"))]
/// Configuration used to implement `FromScratch` for the Foreign field chip.
/// This should only be used for testing.
pub struct FieldChipConfigForTests<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F> + FromScratch<F>,
{
    native_gadget_config: <N as FromScratch<F>>::Config,
    field_chip_config: FieldChipConfig,
}

#[cfg(any(test, feature = "testing"))]
impl<F, K, P, N> FromScratch<F> for FieldChip<F, K, P, N>
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
    N: NativeInstructions<F> + FromScratch<F>,
{
    type Config = FieldChipConfigForTests<F, N>;

    fn new_from_scratch(config: &FieldChipConfigForTests<F, N>) -> Self {
        let native_gadget = <N as FromScratch<F>>::new_from_scratch(&config.native_gadget_config);
        FieldChip::new(&config.field_chip_config, &native_gadget)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &FieldChipConfigForTests<F, N>) {
        <N as FromScratch<F>>::load_from_scratch(layouter, &config.native_gadget_config)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> FieldChipConfigForTests<F, N> {
        let native_gadget_config =
            <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let field_chip_config = {
            let advice_cols = (0..nb_field_chip_columns::<F, K, P>())
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>();
            FieldChip::<F, K, P, N>::configure(meta, &advice_cols)
        };
        FieldChipConfigForTests {
            native_gadget_config,
            field_chip_config,
        }
    }
}

#[cfg(test)]
mod tests {
    use halo2curves::{
        pasta::{Fp as VestaScalar, Fq as PallasScalar},
        secp256k1::{Fp as secp256k1Base, Fq as secp256k1Scalar},
    };
    use midnight_curves::Fq as BlsScalar;

    use super::*;
    use crate::{
        field::{
            decomposition::chip::P2RDecompositionChip, foreign::params::MultiEmulationParams,
            NativeChip, NativeGadget,
        },
        instructions::{
            arithmetic, assertions, control_flow, decomposition, equality, public_input, zero,
        },
    };

    macro_rules! test_generic {
        ($mod:ident, $op:ident, $native:ident, $emulated:ident, $name:expr) => {
            $mod::tests::$op::<
                $native,
                AssignedField<$native, $emulated, MultiEmulationParams>,
                FieldChip<
                    $native,
                    $emulated,
                    MultiEmulationParams,
                    NativeGadget<$native, P2RDecompositionChip<$native>, NativeChip<$native>>,
                >,
            >($name);
        };
    }

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                test_generic!($mod, $op, PallasScalar, secp256k1Base, "");
                test_generic!($mod, $op, PallasScalar, secp256k1Scalar, "");
                test_generic!($mod, $op, VestaScalar, secp256k1Base, "");
                test_generic!($mod, $op, VestaScalar, secp256k1Scalar, "");
                test_generic!($mod, $op, BlsScalar, secp256k1Base, "field_chip_secp_base");
                test_generic!(
                    $mod,
                    $op,
                    BlsScalar,
                    secp256k1Scalar,
                    "field_chip_secp_scalar"
                );
            }
        };
    }

    test!(assertions, test_assertions);

    test!(public_input, test_public_inputs);

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);

    test!(control_flow, test_select);
    test!(control_flow, test_cond_assert_equal);

    test!(arithmetic, test_add);
    test!(arithmetic, test_sub);
    test!(arithmetic, test_mul);
    test!(arithmetic, test_div);
    test!(arithmetic, test_neg);
    test!(arithmetic, test_inv);
    test!(arithmetic, test_pow);
    test!(arithmetic, test_linear_combination);
    test!(arithmetic, test_add_and_mul);

    macro_rules! test_generic {
        ($mod:ident, $op:ident, $native:ident, $emulated:ident, $name:expr) => {
            $mod::tests::$op::<
                $native,
                AssignedField<$native, $emulated, MultiEmulationParams>,
                FieldChip<
                    $native,
                    $emulated,
                    MultiEmulationParams,
                    NativeGadget<$native, P2RDecompositionChip<$native>, NativeChip<$native>>,
                >,
                NativeGadget<$native, P2RDecompositionChip<$native>, NativeChip<$native>>,
            >($name);
        };
    }

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                test_generic!($mod, $op, PallasScalar, secp256k1Base, "");
                test_generic!($mod, $op, PallasScalar, secp256k1Scalar, "");
                test_generic!($mod, $op, VestaScalar, secp256k1Base, "");
                test_generic!($mod, $op, VestaScalar, secp256k1Scalar, "");
                test_generic!($mod, $op, BlsScalar, secp256k1Base, "field_chip_secp_base");
                test_generic!(
                    $mod,
                    $op,
                    BlsScalar,
                    secp256k1Scalar,
                    "field_chip_secp_scalar"
                );
            }
        };
    }

    test!(decomposition, test_bit_decomposition);
    test!(decomposition, test_byte_decomposition);
}

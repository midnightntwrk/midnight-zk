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

//! A gadget that implement all basic basic operations in the native field, i.e.
//! basic field operations, decompositions and comparisons

use std::marker::PhantomData;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;
use num_traits::Zero;
#[cfg(any(test, feature = "testing"))]
use {
    crate::field::decomposition::chip::P2RDecompositionConfig,
    crate::field::decomposition::pow2range::{Pow2RangeChip, NB_POW2RANGE_COLS},
    crate::field::native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
    crate::testing_utils::FromScratch,
    crate::testing_utils::Sampleable,
    crate::utils::ComposableChip,
    midnight_proofs::plonk::{Column, ConstraintSystem, Instance},
    rand::Rng,
    rand::RngCore,
};

use crate::{
    field::{
        decomposition::{chip::P2RDecompositionChip, instructions::CoreDecompositionInstructions},
        NativeChip,
    },
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, BinaryInstructions,
        BitwiseInstructions, CanonicityInstructions, ComparisonInstructions,
        ControlFlowInstructions, ConversionInstructions, DecompositionInstructions,
        EqualityInstructions, FieldInstructions, NativeInstructions, PublicInputInstructions,
        RangeCheckInstructions, ScalarFieldInstructions, UnsafeConversionInstructions,
        ZeroInstructions,
    },
    types::{AssignedBit, AssignedNative, InnerValue, Instantiable},
    utils::util::{big_to_fe, fe_to_big, modulus},
};

#[derive(Debug, Clone)]
/// A gadget that implements all basic operations on the Native field:
/// - Assignments
/// - Assertions
/// - Arithmetic
/// - Binary
/// - Comparison
/// - ControlFlow
/// - Conversions
/// - Decomposition
/// - Equality
pub struct NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    core_decomposition_chip: CoreDecomposition,
    pub(crate) native_chip: NativeArith,
    _marker: PhantomData<F>,
}

impl<F, CoreDecomposition, NativeArith> NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    /// Create a new gadget.
    pub fn new(core_decomposition_chip: CoreDecomposition, native_chip: NativeArith) -> Self {
        Self {
            core_decomposition_chip,
            native_chip,
            _marker: PhantomData,
        }
    }
}

impl<F: PrimeField> Instantiable<F> for AssignedByte<F> {
    fn as_public_input(element: &u8) -> Vec<F> {
        vec![F::from(*element as u64)]
    }
}

/// This wrapper type on `AssignedNative<F>` is designed to enforce type safety
/// on assigned bytes. It prevents the user from creating an `AssignedByte`
/// without using the designated entry points, which guarantee (with
/// constraints) that the assigned value is indeed in the range [0, 256).
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedByte<F: PrimeField>(AssignedNative<F>);

impl<F: PrimeField> InnerValue for AssignedByte<F> {
    type Element = u8;

    fn value(&self) -> Value<u8> {
        self.0.value().map(|v| {
            let bi_v = fe_to_big(*v);
            #[cfg(not(test))]
            assert!(bi_v <= BigUint::from(255u8));
            bi_v.to_bytes_le().first().copied().unwrap_or(0u8)
        })
    }
}

impl<F: PrimeField> From<AssignedByte<F>> for AssignedNative<F> {
    fn from(value: AssignedByte<F>) -> Self {
        value.0
    }
}

impl<F: PrimeField> From<&AssignedByte<F>> for AssignedNative<F> {
    fn from(value: &AssignedByte<F>) -> Self {
        value.clone().0
    }
}

impl<F: PrimeField> From<AssignedBit<F>> for AssignedByte<F> {
    fn from(value: AssignedBit<F>) -> Self {
        AssignedByte(value.0)
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> Sampleable for AssignedByte<F> {
    fn sample_inner(mut rng: impl RngCore) -> Self::Element {
        rng.gen()
    }
}

/// Struct representing bounded elements, i.e. 0 <= value < 2^bound.
#[derive(Clone, Debug)]
pub struct BoundedElement<F: PrimeField> {
    value: F,
    bound: u32,
}

impl<F: PrimeField> BoundedElement<F> {
    /// Creates a new bounded element
    pub fn new(value: F, bound: u32) -> Self {
        #[cfg(not(test))]
        {
            use num_traits::One;

            let v_as_bint = fe_to_big(value);
            let bound_as_bint = BigUint::one() << bound;
            assert!(
                v_as_bint < bound_as_bint,
                "Trying to convert {:?} to an AssignedBounded less than 2^{:?}!",
                value,
                bound
            );
        }
        BoundedElement { value, bound }
    }

    /// gets the field value of a BoundedElement
    pub fn field_value(&self) -> F {
        self.value
    }

    /// gets the bound of a BoundedElement
    pub fn bound(&self) -> u32 {
        self.bound
    }
}

/// This type is designed to enforce type safety on assigned "small" values.
/// It prevents the user from creating an `AssignedBounded` without using the
/// designated entry points, which guarantee (with constraints) that the
/// assigned value is in the desired range, `[0, 2^bound)`.
#[derive(Clone, Debug)]
pub struct AssignedBounded<F: PrimeField> {
    value: AssignedNative<F>,
    bound: u32,
}

impl<F: PrimeField> AssignedBounded<F> {
    /// CAUTION: use only if you know what you are doing!
    ///
    /// This function converts an `AssignedNative` to an `AssignedBounded`
    /// *without* adding any constraint to guarantee the number respects the
    /// bound.
    ///
    /// *It should be used only when the input x is already rangechecked
    pub(crate) fn to_assigned_bounded_unsafe(x: &AssignedNative<F>, bound: u32) -> Self {
        // we create the element to enforce the runtime assertions
        let _new = x.value().map(|&x| BoundedElement::new(x, bound));
        AssignedBounded {
            value: x.clone(),
            bound,
        }
    }

    /// gets the bound of an AssignedBounded
    pub fn bound(&self) -> u32 {
        self.bound
    }
}

impl<F: PrimeField> InnerValue for AssignedBounded<F> {
    type Element = BoundedElement<F>;

    fn value(&self) -> Value<BoundedElement<F>> {
        let (assigned_value, bound) = (self.value.clone(), self.bound());
        assigned_value
            .value()
            .map(|&value| BoundedElement { value, bound })
    }
}

impl<F, CoreDecomposition, NativeArith> RangeCheckInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + BinaryInstructions<F>
        + EqualityInstructions<F, AssignedNative<F>>
        + ControlFlowInstructions<F, AssignedNative<F>>,
{
    fn assign_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        bound: &BigUint,
    ) -> Result<AssignedNative<F>, Error> {
        if bound.is_zero() {
            return self.assign_fixed(layouter, F::ZERO);
        }

        // compute largest k such that 2^k <= bound
        let k = (bound.bits() - 1) as usize;
        if *bound == BigUint::from(1u8) << k {
            return self
                .core_decomposition_chip
                .assign_less_than_pow2(layouter, value, k);
        }
        let x = self.assign(layouter, value)?;
        self.assert_lower_than_fixed(layouter, &x, bound)?;
        Ok(x)
    }

    fn assert_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bound: &BigUint,
    ) -> Result<(), Error> {
        // compute largest k such that 2^k <= bound
        let k = (bound.bits() - 1) as usize;
        let two_pow_k = BigUint::from(1u8) << k; // 2^k

        // if the bound is a power of 2, the check is easier
        if two_pow_k == *bound {
            return self
                .core_decomposition_chip
                .assert_less_than_pow2(layouter, x, k);
        }

        // b := x in [0, 2^k)
        let b_value = x.value().map(|x| fe_to_big(*x) < two_pow_k);
        let b: AssignedBit<F> = self.assign(layouter, b_value)?;

        let diff: F = big_to_fe(bound - two_pow_k);

        // x in [0, bound) <=> x in [0, 2^k) or (x - diff) in [0, 2^k)
        let shifted_x = self.add_constant(layouter, x, -diff)?;
        let y = self.select(layouter, &b, x, &shifted_x)?;
        self.core_decomposition_chip
            .assert_less_than_pow2(layouter, &y, k)
    }
}

impl<F, CoreDecomposition, NativeArith> ComparisonInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + BinaryInstructions<F>
        + EqualityInstructions<F, AssignedNative<F>>
        + ControlFlowInstructions<F, AssignedNative<F>>,
{
    // This constant must not exceed F::NUM_BITS - 2. This restriction derives from
    // the assumption that the following condition holds true:
    //
    //     x <  y    ==> 0 < y - x < 2^MAX_BOUND_IN_BITS
    //
    // This implies that the difference x - y should not wrap around in the field,
    // ensuring it remains less than 2^MAX_BOUND_IN_BITS.
    const MAX_BOUND_IN_BITS: u32 = F::NUM_BITS - 2;

    fn bounded_of_element(
        &self,
        layouter: &mut impl Layouter<F>,
        n: usize,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBounded<F>, Error> {
        #[cfg(not(test))]
        assert!(
            n <= Self::MAX_BOUND_IN_BITS as usize,
            "Cannot bound an element with a bound {} > {} = MAX_BOUND",
            n,
            Self::MAX_BOUND_IN_BITS,
        );

        let assigned_bounded = {
            let assigned_element = self.assign(layouter, x.value().copied())?;
            self.core_decomposition_chip
                .assert_less_than_pow2(layouter, &assigned_element, n)?;
            AssignedBounded::to_assigned_bounded_unsafe(&assigned_element, n as u32)
        };
        self.assert_equal(layouter, x, &assigned_bounded.value)?;
        Ok(assigned_bounded)
    }

    fn element_of_bounded(
        &self,
        _layouter: &mut impl Layouter<F>,
        bounded: &AssignedBounded<F>,
    ) -> Result<AssignedNative<F>, Error> {
        Ok(bounded.value.clone())
    }

    /// Returns `true` iff the given assigned element is strictly lower than the
    /// given bound.
    fn lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: F,
    ) -> Result<AssignedBit<F>, Error> {
        let x_as_bint = x.value.value().map(|&x| fe_to_big(x));
        let y_as_bint = fe_to_big(y);

        // check that we try to make a meaningful comparison, i.e. y < 2^p-1
        #[cfg(not(test))]
        assert!(y_as_bint < BigUint::from(1u8) << Self::MAX_BOUND_IN_BITS);

        // x is already bounded by the type system so x < bound for some fixed bound.
        // If we want to show that x < bound <= y this relation automatically holds
        if y_as_bint >= (BigUint::from(1u8) << x.bound()) {
            return self.assign_fixed(layouter, true);
        }

        // we will now assert the equation
        // we know 0 <= x,y < 2^bound. There are two cases:
        //  1. x <  y    ==>    0 < y - x < 2^bound    ==>    0 <= y - x - 1 < 2^bound
        //  2. x >= y    ==>                                  0 <=  x - y < 2^bound

        // define z = b(2y-1) + x + bx(-2) - y
        //   - if b = 0 ==> z = x - y
        //   - if b = 1 ==> z = 2y-1 + x -2x - y =  y - 1 - x

        // assign b
        let result_bit = x_as_bint.map(|x_as_bint| x_as_bint < y_as_bint);
        let assigned_result = self.assign(layouter, result_bit)?;

        // assign z: z is of the form "f1 a1 + f2 a2 + f a_1 a_2 + c"
        // TODO: This can be done in a single row but the interface prevents it...
        // Expose some more complex function maybe?
        let b_el: AssignedNative<F> = self.convert(layouter, &assigned_result)?;
        let x_el = self.element_of_bounded(layouter, x)?;
        let bx = self.mul(layouter, &x_el, &b_el, None)?;
        let terms = vec![
            (F::from(2) * y - F::ONE, b_el),
            (F::ONE, x_el),
            (-F::from(2), bx),
        ];
        let z = self.linear_combination(layouter, terms.as_slice(), -y)?;

        self.core_decomposition_chip
            .assert_less_than_pow2(layouter, &z, x.bound() as usize)?;
        Ok(assigned_result)
    }

    fn lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let x_as_bint = x.value.value().map(|&x| fe_to_big(x));
        let y_as_bint = y.value.value().map(|&x| fe_to_big(x));

        // we will now assert the equation
        // we know 0 <= x,y < 2^bound. There are two cases:
        //  1. x <  y    ==>    0 < y - x < 2^bound    ==>    0 <= y - x - 1 < 2^bound
        //  2. x >= y    ==>                                  0 <=  x - y < 2^bound

        // define z = 2by - b + x + bx(-2) - y
        //   - if b = 0 ==> z = x - y
        //   - if b = 1 ==> z = 2y-1 + x -2x - y =  y - 1 - x

        // assign b
        let result_bit = x_as_bint
            .zip(y_as_bint)
            .map(|(x_as_bint, y_as_bint)| x_as_bint < y_as_bint);
        let assigned_result = self.assign(layouter, result_bit)?;

        // assign z: z is of the form "f1 a1 + f2 a2 + f a_1 a_2 + c"
        let b_el: AssignedNative<F> = self.convert(layouter, &assigned_result)?;
        let x_el = self.element_of_bounded(layouter, x)?;
        let y_el = self.element_of_bounded(layouter, y)?;

        let bx = self.mul(layouter, &x_el, &b_el, None)?;
        let by = self.mul(layouter, &y_el, &b_el, None)?;
        let terms = vec![
            (F::from(2), by),
            (-F::ONE, b_el),
            (F::ONE, x_el),
            (-F::from(2), bx),
            (-F::ONE, y_el),
        ];
        let z = self.linear_combination(layouter, terms.as_slice(), F::ZERO)?;

        let max_bound = x.bound().max(y.bound());
        self.core_decomposition_chip
            .assert_less_than_pow2(layouter, &z, max_bound as usize)?;
        Ok(assigned_result)
    }

    fn leq(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error> {
        // This is reimplemented this way because doing x < y + 1 might break things in
        // some weird edge case
        let b1 = self.lower_than(layouter, x, y)?;
        let x_el = self.element_of_bounded(layouter, x)?;
        let y_el = self.element_of_bounded(layouter, y)?;
        let b2 = self.is_equal(layouter, &x_el, &y_el)?;
        self.or(layouter, &[b1, b2])
    }

    /// Returns `true` iff the given assigned element is greater than or equal
    /// to the given bound.
    fn geq(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let b = self.lower_than(layouter, x, y)?;
        self.not(layouter, &b)
    }
}

/// Instructions for constraining bytes as public inputs.
impl<F, CoreDecomposition, NativeArith> PublicInputInstructions<F, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        PublicInputInstructions<F, AssignedNative<F>> + ArithInstructions<F, AssignedNative<F>>,
{
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        assigned: &AssignedByte<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![assigned.clone().into()])
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedByte<F>,
    ) -> Result<(), Error> {
        let assigned_as_native: AssignedNative<F> = assigned.clone().into();
        self.constrain_as_public_input(layouter, &assigned_as_native)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<u8>,
    ) -> Result<AssignedByte<F>, Error> {
        // We can skip the in-circuit [0, 7]-range-check as this condition will
        // be enforced through the public inputs bind anyway.
        let assigned_native = self
            .native_chip
            .assign_as_public_input(layouter, value.map(|byte| F::from(byte as u64)))?;
        self.convert_unsafe(layouter, &assigned_native)
    }
}

/// The set of circuit instructions for assignment of bytes.
impl<F, CoreDecomposition, NativeArith> AssignmentInstructions<F, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        byte: Value<u8>,
    ) -> Result<AssignedByte<F>, Error> {
        let byte_as_f = byte.map(|b| F::from(b as u64));
        let assigned = self
            .core_decomposition_chip
            .assign_less_than_pow2(layouter, byte_as_f, 8)?;
        Ok(AssignedByte(assigned))
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: u8,
    ) -> Result<AssignedByte<F>, Error> {
        let assigned = self.assign_fixed(layouter, F::from(constant as u64))?;
        Ok(AssignedByte(assigned))
    }

    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<u8>],
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let values_as_f: Vec<_> = values
            .iter()
            .map(|v| v.map(|b| F::from(b as u64)))
            .collect();

        self.core_decomposition_chip
            .assign_many_small(layouter, &values_as_f, 8)?
            .iter()
            .map(|assigned_native| self.convert_unsafe(layouter, assigned_native))
            .collect()
    }
}

/// The set of AssertionInstructions for bytes.
impl<F, CoreDecomposition, NativeArith> AssertionInstructions<F, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        byte1: &AssignedByte<F>,
        byte2: &AssignedByte<F>,
    ) -> Result<(), Error> {
        let x1: AssignedNative<F> = self.convert(layouter, byte1)?;
        let x2: AssignedNative<F> = self.convert(layouter, byte2)?;
        self.assert_equal(layouter, &x1, &x2)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        byte1: &AssignedByte<F>,
        byte2: &AssignedByte<F>,
    ) -> Result<(), Error> {
        let x1: AssignedNative<F> = self.convert(layouter, byte1)?;
        let x2: AssignedNative<F> = self.convert(layouter, byte2)?;
        self.assert_not_equal(layouter, &x1, &x2)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        byte: &AssignedByte<F>,
        constant: u8,
    ) -> Result<(), Error> {
        let x: AssignedNative<F> = self.convert(layouter, byte)?;
        self.assert_equal_to_fixed(layouter, &x, F::from(constant as u64))
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        byte: &AssignedByte<F>,
        constant: u8,
    ) -> Result<(), Error> {
        let x: AssignedNative<F> = self.convert(layouter, byte)?;
        self.assert_not_equal_to_fixed(layouter, &x, F::from(constant as u64))
    }
}

/// The set of EqualityInstructions for bytes.
impl<F, CoreDecomposition, NativeArith> EqualityInstructions<F, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        ArithInstructions<F, AssignedNative<F>> + EqualityInstructions<F, AssignedNative<F>>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        byte1: &AssignedByte<F>,
        byte2: &AssignedByte<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let x1: AssignedNative<F> = self.convert(layouter, byte1)?;
        let x2: AssignedNative<F> = self.convert(layouter, byte2)?;
        self.native_chip.is_equal(layouter, &x1, &x2)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        byte: &AssignedByte<F>,
        constant: u8,
    ) -> Result<AssignedBit<F>, Error> {
        let x: AssignedNative<F> = self.convert(layouter, byte)?;
        self.native_chip
            .is_equal_to_fixed(layouter, &x, F::from(constant as u64))
    }
}

impl<F: PrimeField> AssertionInstructions<F, [AssignedByte<F>; 32]>
    for NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &[AssignedByte<F>; 32],
        y: &[AssignedByte<F>; 32],
    ) -> Result<(), Error> {
        x.iter()
            .zip(y.iter())
            .try_for_each(|(x, y)| self.assert_equal(layouter, x, y))
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &[AssignedByte<F>; 32],
        y: &[AssignedByte<F>; 32],
    ) -> Result<(), Error> {
        // TODO: This can be optimized by first aggregating as many bytes as possible in
        // a single AssignedNative and only then comparing chunk-wise.
        let xi_eq_yi = (x.iter())
            .zip(y.iter())
            .map(|(x, y)| self.is_equal(layouter, x, y))
            .collect::<Result<Vec<_>, Error>>()?;
        let all_equal = self.and(layouter, &xi_eq_yi)?;
        self.assert_equal_to_fixed(layouter, &all_equal, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &[AssignedByte<F>; 32],
        constant: [u8; 32],
    ) -> Result<(), Error> {
        x.iter()
            .zip(constant.iter())
            .try_for_each(|(x, y)| self.assert_equal_to_fixed(layouter, x, *y))
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &[AssignedByte<F>; 32],
        constant: [u8; 32],
    ) -> Result<(), Error> {
        // TODO: This can be optimized by first aggregating as many bytes as possible in
        // a single AssignedNative and only then comparing chunk-wise.
        let xi_eq_ci = (x.iter())
            .zip(constant.iter())
            .map(|(x, c)| self.is_equal_to_fixed(layouter, x, *c))
            .collect::<Result<Vec<_>, Error>>()?;
        let all_equal = self.and(layouter, &xi_eq_ci)?;
        self.assert_equal_to_fixed(layouter, &all_equal, false)
    }
}

/// Conversion from AssignedNative to AssignedByte.
impl<F, CoreDecomposition, NativeArith>
    ConversionInstructions<F, AssignedNative<F>, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn convert_value(&self, x: &F) -> Option<u8> {
        let b_as_bn = fe_to_big(*x);
        #[cfg(not(test))]
        assert!(
            b_as_bn <= BigUint::from(255u8),
            "Trying to convert {:?} to AssignedByte in-circuit",
            x
        );
        b_as_bn.to_bytes_le().first().cloned()
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedByte<F>, Error> {
        let b_value = x.value().map(|x| {
            <Self as ConversionInstructions<_, _, AssignedByte<F>>>::convert_value(self, x)
                .unwrap_or(0u8)
        });
        let b: AssignedByte<F> = self.assign(layouter, b_value)?;
        self.assert_equal(layouter, x, &b.0)?;
        Ok(b)
    }
}

/// Conversion from AssignedByte to AssignedNative.
impl<F, CoreDecomposition, NativeArith>
    ConversionInstructions<F, AssignedByte<F>, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn convert_value(&self, x: &u8) -> Option<F> {
        Some(F::from(*x as u64))
    }

    fn convert(
        &self,
        _layouter: &mut impl Layouter<F>,
        byte: &AssignedByte<F>,
    ) -> Result<AssignedNative<F>, Error> {
        Ok(byte.0.clone())
    }
}

/// Unsafe conversion from AssignedNative to AssignedByte.
impl<F, CoreDecomposition, NativeArith>
    UnsafeConversionInstructions<F, AssignedNative<F>, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    /// CAUTION: use only if you know what you are doing!
    ///
    /// This function converts an `AssignedNative` to an `AssignedByte`
    /// *without* adding any constraint to guarantee the "byteness" of the
    /// assigned value.
    ///
    /// *It should be used only when the input x is already guaranteed to be a
    /// byte*
    fn convert_unsafe(
        &self,
        _layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedByte<F>, Error> {
        #[cfg(not(test))]
        x.value().map(|&x| {
            let x = fe_to_big(x);
            assert!(
                x <= BigUint::from(255u8),
                "Trying to convert {:?} to an AssignedByte!",
                x
            );
        });
        Ok(AssignedByte(x.clone()))
    }
}

/// The set of circuit instructions for decomposition operations.
impl<F, CoreDecomposition, NativeArith> DecompositionInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + BinaryInstructions<F>
        + EqualityInstructions<F, AssignedNative<F>>
        + ControlFlowInstructions<F, AssignedNative<F>>,
    NativeGadget<F, CoreDecomposition, NativeArith>: CanonicityInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + BinaryInstructions<F>
        + EqualityInstructions<F, AssignedNative<F>>
        + ControlFlowInstructions<F, AssignedNative<F>>,
{
    fn assigned_to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        let nb_bits = nb_bits.unwrap_or(F::NUM_BITS as usize);
        if nb_bits > F::NUM_BITS as usize {
            panic!(
                "assigned_to_le_bits: why do you need the output to have more bits than necessary?"
            );
        }
        let limbs = self
            .core_decomposition_chip
            .decompose_fixed_limb_size(layouter, x, nb_bits, 1)?;
        let bits = limbs
            .iter()
            .map(|x| self.native_chip.convert_unsafe(layouter, x))
            .collect::<Result<Vec<_>, Error>>()?;
        if enforce_canonical && nb_bits >= F::NUM_BITS as usize {
            let canonical = self.is_canonical(layouter, &bits)?;
            self.assert_equal_to_fixed(layouter, &canonical, true)?;
        }
        Ok(bits)
    }

    fn assigned_to_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let f_num_bytes = F::NUM_BITS.div_ceil(8);
        let nb_bytes = nb_bytes.unwrap_or(f_num_bytes as usize);
        if nb_bytes > f_num_bytes as usize {
            panic!("assigned_to_le_bytes: why do you need the output to have more bytes than necessary?");
        }
        // If nb_bytes equals ⌈F::NUM_BITS / 8⌉, we need extra care to
        // guarantee that the output is canonical: we split in bits enforcing canonicity
        // and then group the bits in bytes.
        if nb_bytes == f_num_bytes as usize {
            let bits = self.assigned_to_le_bits(layouter, x, Some(F::NUM_BITS as usize), true)?;
            bits.chunks(8)
                .map(|chunk| {
                    let terms = chunk
                        .iter()
                        .enumerate()
                        .map(|(i, bit)| (F::from(1 << i), bit.clone().into()))
                        .collect::<Vec<_>>();
                    let byte = self.linear_combination(layouter, &terms, F::ZERO)?;
                    self.convert_unsafe(layouter, &byte)
                })
                .collect::<Result<Vec<AssignedByte<F>>, Error>>()
        }
        // If nb_bytes < ⌈F::NUM_BITS / 8⌉, wrap-arounds are not possible, so canonicity is always
        // guaranteed. In this case we can split in bytes more efficiently.
        else {
            let limbs = self.core_decomposition_chip.decompose_fixed_limb_size(
                layouter,
                x,
                8 * nb_bytes,
                8,
            )?;
            limbs
                .iter()
                .map(|x| self.convert_unsafe(layouter, x))
                .collect::<Result<Vec<_>, Error>>()
        }
    }

    fn assigned_to_le_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits_per_chunk: usize,
        nb_chunks: Option<usize>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert!(nb_bits_per_chunk < F::NUM_BITS as usize);
        let nb_chunks = nb_chunks.unwrap_or((F::NUM_BITS as usize).div_ceil(nb_bits_per_chunk));
        self.core_decomposition_chip.decompose_fixed_limb_size(
            layouter,
            x,
            nb_bits_per_chunk * nb_chunks,
            nb_bits_per_chunk,
        )
    }

    fn sgn0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        // Any element in Zp can be uniquely represented as 2 * w + e, where
        // w in [0, (p-1)/2] and e in {0, 1}, with the exception of zero, which
        // admits two representations: (w = 0, e = 0) and (w = (p-1)/2, e = 1).
        let x_val = x.value().copied().map(fe_to_big);
        let w_val = x_val.clone().map(|x| &x / BigUint::from(2u8));
        let e_val = x_val.clone().map(|x| x.bit(0));

        let e: AssignedBit<F> = self.assign(layouter, e_val)?;
        let w = self.assign_lower_than_fixed(
            layouter,
            w_val.map(big_to_fe::<F>),
            &(&(modulus::<F>() + BigUint::from(1u8)) / BigUint::from(2u8)),
        )?;
        let must_be_x = self.linear_combination(
            layouter,
            &[(F::ONE, e.clone().into()), (F::from(2), w.clone())],
            F::ZERO,
        )?;
        self.assert_equal(layouter, x, &must_be_x)?;
        // The edge case x = 0 is no problem because `x_is_not_zero` is false in that
        // case and we will still assign sgn0(0) = 0.
        let x_is_zero: AssignedBit<F> = self.is_zero(layouter, x)?;
        let x_is_not_zero: AssignedBit<F> = self.not(layouter, &x_is_zero)?;
        let sgn0 = self.and(layouter, &[x_is_not_zero, e])?;

        Ok(sgn0)
    }
}

// Inherit F Public Input Instructions.
impl<F, CoreDecomposition, NativeArith> PublicInputInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        PublicInputInstructions<F, AssignedNative<F>> + ArithInstructions<F, AssignedNative<F>>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedNative<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_chip.as_public_input(layouter, assigned)
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedNative<F>,
    ) -> Result<(), Error> {
        self.native_chip
            .constrain_as_public_input(layouter, assigned)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.assign_as_public_input(layouter, value)
    }
}

// Inherit F Public Input Instructions.
impl<F, CoreDecomposition> NativeGadget<F, CoreDecomposition, NativeChip<F>>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
{
    /// Constrains the given assigned value as a public input that will be
    /// plugged-in in committed form.
    pub fn constrain_as_committed_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedNative<F>,
    ) -> Result<(), Error> {
        self.native_chip
            .constrain_as_committed_public_input(layouter, assigned)
    }
}

// Inherit F Assignment Instructions.
impl<F, CoreDecomposition, NativeArith> AssignmentInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.assign_fixed(layouter, constant)
    }

    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        value: &[Value<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_chip.assign_many(layouter, value)
    }
}

// Inherit Bit Public Input Instructions.
impl<F, CoreDecomposition, NativeArith> PublicInputInstructions<F, AssignedBit<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        PublicInputInstructions<F, AssignedBit<F>> + ArithInstructions<F, AssignedNative<F>>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedBit<F>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_chip.as_public_input(layouter, assigned)
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_chip
            .constrain_as_public_input(layouter, assigned)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<bool>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.assign_as_public_input(layouter, value)
    }
}

// Inherit Bit Assignment Instructions.
impl<F, CoreDecomposition, NativeArith> AssignmentInstructions<F, AssignedBit<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<bool>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: bool,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.assign_fixed(layouter, constant)
    }

    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<bool>],
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        let values_as_f: Vec<_> = values
            .iter()
            .map(|v| v.map(|b| F::from(b as u64)))
            .collect();

        self.core_decomposition_chip
            .assign_many_small(layouter, &values_as_f, 1)?
            .iter()
            .map(|assigned_native| self.native_chip.convert_unsafe(layouter, assigned_native))
            .collect()
    }
}

// Inherit F Assertion Instructions.
impl<F, CoreDecomposition, NativeArith> AssertionInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        self.native_chip.assert_equal(layouter, x, y)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        self.native_chip.assert_not_equal(layouter, x, y)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<(), Error> {
        self.native_chip
            .assert_equal_to_fixed(layouter, x, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<(), Error> {
        self.native_chip
            .assert_not_equal_to_fixed(layouter, x, constant)
    }
}

// Inherit Bit Assertion Instructions.
impl<F, CoreDecomposition, NativeArith> AssertionInstructions<F, AssignedBit<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>> + AssertionInstructions<F, AssignedBit<F>>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_chip.assert_equal(layouter, x, y)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_chip.assert_not_equal(layouter, x, y)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        constant: bool,
    ) -> Result<(), Error> {
        self.native_chip
            .assert_equal_to_fixed(layouter, x, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        constant: bool,
    ) -> Result<(), Error> {
        self.native_chip
            .assert_not_equal_to_fixed(layouter, x, constant)
    }
}

// Inherit Arith Instructions.
impl<F, CoreDecomposition, NativeArith> ArithInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
{
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(F, AssignedNative<F>)],
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip
            .linear_combination(layouter, terms, constant)
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        multiplying_constant: Option<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.mul(layouter, x, y, multiplying_constant)
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.div(layouter, x, y)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.inv(layouter, x)
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.inv0(layouter, x)
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
        self.native_chip
            .add_and_mul(layouter, a_and_x, b_and_y, c_and_z, k, m)
    }

    fn add_constants(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: &[AssignedNative<F>],
        constants: &[F],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_chip.add_constants(layouter, xs, constants)
    }
}

// Inherit Conversion Instructions to AssignedBit.
impl<F, CoreDecomposition, NativeArith> ConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + ConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>,
{
    fn convert_value(&self, x: &F) -> Option<bool> {
        self.native_chip.convert_value(x)
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.convert(layouter, x)
    }
}

// Inherit Conversion Instructions from AssignedBit.
impl<F, CoreDecomposition, NativeArith> ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>,
{
    fn convert_value(&self, x: &bool) -> Option<F> {
        self.native_chip.convert_value(x)
    }

    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.convert(layouter, x)
    }
}

// Inherit Binary Instructions.
impl<F, CoreDecomposition, NativeArith> BinaryInstructions<F>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>> + BinaryInstructions<F>,
{
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.and(layouter, bits)
    }

    fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.or(layouter, bits)
    }

    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.xor(layouter, bits)
    }

    fn not(
        &self,
        layouter: &mut impl Layouter<F>,
        b: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.not(layouter, b)
    }
}

// Inherit F Equality Instructions.
impl<F, CoreDecomposition, NativeArith> EqualityInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        ArithInstructions<F, AssignedNative<F>> + EqualityInstructions<F, AssignedNative<F>>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.is_equal(layouter, x, y)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        constant: F,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.is_equal_to_fixed(layouter, x, constant)
    }
}

// Implement Bit Equality Instructions.
impl<F, CoreDecomposition, NativeArith> EqualityInstructions<F, AssignedBit<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>> + EqualityInstructions<F, AssignedBit<F>>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.is_equal(layouter, x, y)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBit<F>,
        constant: bool,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.is_equal_to_fixed(layouter, x, constant)
    }
}

// Inherit Zero Instructions.
impl<F, CoreDecomposition, NativeArith> ZeroInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedNative<F>>
        + EqualityInstructions<F, AssignedNative<F>>,
{
}

// Inherit F ControlFlow Instructions.
impl<F, CoreDecomposition, NativeArith> ControlFlowInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        ArithInstructions<F, AssignedNative<F>> + ControlFlowInstructions<F, AssignedNative<F>>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_chip.select(layouter, bit, x, y)
    }
}

// Inherit Bit ControlFlow Instructions.
impl<F, CoreDecomposition, NativeArith> ControlFlowInstructions<F, AssignedBit<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        ArithInstructions<F, AssignedNative<F>> + ControlFlowInstructions<F, AssignedBit<F>>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
        x: &AssignedBit<F>,
        y: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.select(layouter, bit, x, y)
    }
}

// Implement Byte ControlFlow Instructions.
impl<F, CoreDecomposition, NativeArith> ControlFlowInstructions<F, AssignedByte<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith:
        ArithInstructions<F, AssignedNative<F>> + ControlFlowInstructions<F, AssignedNative<F>>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
        x: &AssignedByte<F>,
        y: &AssignedByte<F>,
    ) -> Result<AssignedByte<F>, Error> {
        let byte = (self.native_chip).select(layouter, bit, &x.into(), &y.into())?;
        self.convert_unsafe(layouter, &byte)
    }
}

// Inherit Field Instructions.
impl<F, CoreDecomposition, NativeArith> FieldInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: FieldInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + EqualityInstructions<F, AssignedBit<F>>,
{
    fn order(&self) -> BigUint {
        self.native_chip.order()
    }
}

// Implement Scalar Field Instructions.
impl<F, CoreDecomposition, NativeArith> ScalarFieldInstructions<F>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: CanonicityInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + EqualityInstructions<F, AssignedBit<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + BinaryInstructions<F>,
{
    type Scalar = AssignedNative<F>;
}

// Inherit Canonicity Instructions.
impl<F, CoreDecomposition, NativeArith> CanonicityInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: CanonicityInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + EqualityInstructions<F, AssignedBit<F>>,
{
    fn le_bits_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.le_bits_lower_than(layouter, bits, bound)
    }

    fn le_bits_geq_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_chip.le_bits_geq_than(layouter, bits, bound)
    }
}

// Implement Native Instructions.
impl<F, CoreDecomposition, NativeArith> NativeInstructions<F>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: CanonicityInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + EqualityInstructions<F, AssignedBit<F>>
        + ControlFlowInstructions<F, AssignedBit<F>>
        + BinaryInstructions<F>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>,
{
}

// Implement Bitwise Instructions.
impl<F, CoreDecomposition, NativeArith> BitwiseInstructions<F, AssignedNative<F>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: CanonicityInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + EqualityInstructions<F, AssignedBit<F>>
        + ControlFlowInstructions<F, AssignedBit<F>>
        + BinaryInstructions<F>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>,
{
}

// Circuit implementation for NativeGadget based on the
// P2RDecompositionChip and the NativeChip
#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> FromScratch<F> for NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>> {
    // The circuit config is simply the P2RDecompositionConfig since this contains a
    // NativeConfig as well
    type Config = P2RDecompositionConfig;

    fn new_from_scratch(config: &Self::Config) -> Self {
        let max_bit_len = 8;
        let native_chip = NativeChip::new_from_scratch(&config.native_config);
        let core_decomposition_chip = P2RDecompositionChip::new(config, &max_bit_len);
        NativeGadget::new(core_decomposition_chip, native_chip)
    }

    // This simply loads the pow2range chip's look up table
    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        let max_bit_len = 8;
        let pow2range_config = config.clone().pow2range_config;
        let pow2range_chip = Pow2RangeChip::new(&pow2range_config, max_bit_len);
        let _ = pow2range_chip.load_table(layouter);
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let advice_columns: [_; NB_ARITH_COLS] = core::array::from_fn(|_| meta.advice_column());
        let fixed_columns: [_; NB_ARITH_FIXED_COLS] = core::array::from_fn(|_| meta.fixed_column());

        let native_config =
            NativeChip::configure(meta, &(advice_columns, fixed_columns, *instance_columns));
        let pow2range_config =
            Pow2RangeChip::configure(meta, &advice_columns[1..=NB_POW2RANGE_COLS]);

        P2RDecompositionConfig {
            native_config,
            pow2range_config,
        }
    }
}

#[cfg(test)]
mod tests {
    use blstrs::Fq as BlsScalar;

    use super::*;
    use crate::instructions::{bitwise, comparison, decomposition, range_check};

    macro_rules! test {
        ($module:ident, $operation:ident) => {
            #[test]
            fn $operation() {
                $module::tests::$operation::<
                    BlsScalar,
                    AssignedNative<BlsScalar>,
                    NativeGadget<BlsScalar, P2RDecompositionChip<BlsScalar>, NativeChip<BlsScalar>>,
                    NativeGadget<BlsScalar, P2RDecompositionChip<BlsScalar>, NativeChip<BlsScalar>>,
                >("native_gadget_bls");
            }
        };
    }

    test!(decomposition, test_bit_decomposition);
    test!(decomposition, test_byte_decomposition);
    test!(decomposition, test_sgn0);

    macro_rules! test {
        ($module:ident, $operation:ident) => {
            #[test]
            fn $operation() {
                $module::tests::$operation::<
                    BlsScalar,
                    AssignedNative<BlsScalar>,
                    NativeGadget<BlsScalar, P2RDecompositionChip<BlsScalar>, NativeChip<BlsScalar>>,
                >("native_gadget_bls");
            }
        };
    }

    test!(comparison, test_lower_and_greater);
    test!(comparison, test_assert_bounded_element);
    test!(range_check, test_assert_lower_than_fixed);

    test!(bitwise, test_band);
    test!(bitwise, test_bor);
    test!(bitwise, test_bxor);
    test!(bitwise, test_bnot);
}

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

//! Instructions implemented over ZkStdLib.

use ff::PrimeField;
use midnight_circuits::{
    instructions::{public_input::CommittedInstanceInstructions, vector::VectorBounds, *},
    types::{AssignedBit, AssignedByte, AssignedNative, InnerValue, Instantiable},
    vec::{AssignedVector, Vectorizable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;

use crate::{ZkStdLib, F, NG};

impl<T> AssignmentInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    T::Element: Clone,
    NG: AssignmentInstructions<F, T>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<T::Element>,
    ) -> Result<T, Error> {
        self.native_gadget.assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: T::Element,
    ) -> Result<T, Error> {
        self.native_gadget.assign_fixed(layouter, constant)
    }

    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<T::Element>],
    ) -> Result<Vec<T>, Error> {
        self.native_gadget.assign_many(layouter, values)
    }
}

impl<T> PublicInputInstructions<F, T> for ZkStdLib
where
    T: Instantiable<F>,
    T::Element: Clone,
    NG: PublicInputInstructions<F, T>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_gadget.as_public_input(layouter, assigned)
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<(), Error> {
        self.native_gadget.constrain_as_public_input(layouter, assigned)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<<T>::Element>,
    ) -> Result<T, Error> {
        self.native_gadget.assign_as_public_input(layouter, value)
    }
}

impl<T> CommittedInstanceInstructions<F, T> for ZkStdLib
where
    F: PrimeField,
    T: Instantiable<F>,
    NG: CommittedInstanceInstructions<F, T>,
{
    fn constrain_as_committed_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<(), Error> {
        self.native_gadget.constrain_as_committed_public_input(layouter, assigned)
    }
}

impl<T> AssertionInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    NG: AssertionInstructions<F, T>,
{
    fn assert_equal(&self, layouter: &mut impl Layouter<F>, x: &T, y: &T) -> Result<(), Error> {
        self.native_gadget.assert_equal(layouter, x, y)
    }

    fn assert_not_equal(&self, layouter: &mut impl Layouter<F>, x: &T, y: &T) -> Result<(), Error> {
        self.native_gadget.assert_not_equal(layouter, x, y)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<(), Error> {
        self.native_gadget.assert_equal_to_fixed(layouter, x, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<(), Error> {
        self.native_gadget.assert_not_equal_to_fixed(layouter, x, constant)
    }
}

impl<T> EqualityInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    NG: EqualityInstructions<F, T>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        y: &T,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_equal(layouter, x, y)
    }

    fn is_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        y: &T,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_not_equal(layouter, x, y)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_equal_to_fixed(layouter, x, constant)
    }

    fn is_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_not_equal_to_fixed(layouter, x, constant)
    }
}

impl<T1, T2> ConversionInstructions<F, T1, T2> for ZkStdLib
where
    T1: InnerValue,
    T2: InnerValue,
    NG: ConversionInstructions<F, T1, T2>,
{
    fn convert_value(&self, x: &T1::Element) -> Option<T2::Element> {
        ConversionInstructions::<_, T1, T2>::convert_value(&self.native_gadget, x)
    }

    fn convert(&self, layouter: &mut impl Layouter<F>, x: &T1) -> Result<T2, Error> {
        self.native_gadget.convert(layouter, x)
    }
}

impl CanonicityInstructions<F, AssignedNative<F>> for ZkStdLib {
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

impl DecompositionInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn assigned_to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        self.native_gadget.assigned_to_le_bits(layouter, x, nb_bits, enforce_canonical)
    }

    fn assigned_to_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        self.native_gadget.assigned_to_le_bytes(layouter, x, nb_bytes)
    }

    fn assigned_to_le_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits_per_chunk: usize,
        nb_chunks: Option<usize>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_gadget
            .assigned_to_le_chunks(layouter, x, nb_bits_per_chunk, nb_chunks)
    }

    fn sgn0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.sgn0(layouter, x)
    }
}

impl ArithInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(F, AssignedNative<F>)],
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.linear_combination(layouter, terms, constant)
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        multiplying_constant: Option<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.mul(layouter, x, y, multiplying_constant)
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.div(layouter, x, y)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.inv(layouter, x)
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.inv0(layouter, x)
    }
}

impl ZeroInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl<Assigned> ControlFlowInstructions<F, Assigned> for ZkStdLib
where
    Assigned: InnerValue,
    NG: ControlFlowInstructions<F, Assigned>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error> {
        self.native_gadget.select(layouter, cond, x, y)
    }

    fn cond_swap(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(Assigned, Assigned), Error> {
        self.native_gadget.cond_swap(layouter, cond, x, y)
    }
}

impl FieldInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn order(&self) -> BigUint {
        self.native_gadget.order()
    }
}

impl RangeCheckInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn assign_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        bound: &BigUint,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.assign_lower_than_fixed(layouter, value, bound)
    }

    fn assert_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bound: &BigUint,
    ) -> Result<(), Error> {
        self.native_gadget.assert_lower_than_fixed(layouter, x, bound)
    }
}

impl DivisionInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl BinaryInstructions<F> for ZkStdLib {
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.and(layouter, bits)
    }

    fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.or(layouter, bits)
    }

    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.xor(layouter, bits)
    }

    fn not(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.not(layouter, bit)
    }
}

impl BitwiseInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl<const M: usize, const A: usize, T> VectorInstructions<F, T, M, A> for ZkStdLib
where
    T: Vectorizable,
    T::Element: Copy,
    NG: AssignmentInstructions<F, T> + ControlFlowInstructions<F, T>,
{
    fn trim_beginning(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
        n_elems: usize,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        self.vector_gadget.trim_beginning(layouter, input, n_elems)
    }

    fn padding_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<(Box<[AssignedBit<F>; M]>, VectorBounds<F>), Error> {
        self.vector_gadget.padding_flag(layouter, input)
    }

    fn get_limits(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<VectorBounds<F>, Error> {
        self.vector_gadget.get_limits(layouter, input)
    }

    fn resize<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedVector<F, T, M, A>,
    ) -> Result<AssignedVector<F, T, L, A>, Error> {
        self.vector_gadget.resize(layouter, input)
    }

    fn assign_with_filler(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<<T>::Element>>,
        filler: Option<<T>::Element>,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        self.vector_gadget.assign_with_filler(layouter, value, filler)
    }
}

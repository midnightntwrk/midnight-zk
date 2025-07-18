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

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use num_bigint::BigUint;

use crate::{
    field::{
        decomposition::chip::P2RDecompositionChip, AssignedBounded, AssignedNative, NativeChip,
        NativeGadget,
    },
    instructions::{
        divmod::DivisionInstructions, vector::VectorInstructions, ArithInstructions,
        AssertionInstructions, AssignmentInstructions, BinaryInstructions, ComparisonInstructions,
        ControlFlowInstructions, EqualityInstructions, RangeCheckInstructions,
    },
    types::{AssignedBit, AssignedVector, InnerValue, Vectorizable},
    vec::get_lims,
};

type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

#[derive(Clone, Debug)]
/// A gadget for vector operations of elements that are or fit within a native
/// field element:
pub struct VectorGadget<F: PrimeField> {
    native_gadget: NG<F>,
}

impl<F> VectorGadget<F>
where
    F: PrimeField,
{
    /// Create a new vector gadgets.
    pub fn new(native_gadget: &NG<F>) -> Self {
        Self {
            native_gadget: native_gadget.clone(),
        }
    }
}

impl<F, T, const M: usize, const A: usize> VectorInstructions<F, T, M, A> for VectorGadget<F>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    NG<F>: RangeCheckInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, T>
        + AssignmentInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + EqualityInstructions<F, AssignedNative<F>>
        + BinaryInstructions<F>
        + ControlFlowInstructions<F, AssignedNative<F>>
        + ControlFlowInstructions<F, T>
        + DivisionInstructions<F>
        + AssertionInstructions<F, AssignedBit<F>>
        + ArithInstructions<F, AssignedNative<F>>,
{
    fn resize<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedVector<F, T, M, A>,
    ) -> Result<AssignedVector<F, T, L, A>, Error> {
        assert_eq!(L % A, 0);
        assert!(L > M);

        let extra_pad = self
            .native_gadget
            .assign_many(layouter, &vec![Value::known(T::FILLER); L - M])?;

        let buffer: [T; L] = [extra_pad.as_slice(), input.buffer.as_slice()]
            .concat()
            .try_into()
            .unwrap();

        Ok(AssignedVector {
            buffer,
            len: input.len.clone(),
        })
    }

    fn assign_with_filler(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<T::Element>>,
        filler: Option<T::Element>,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        let ng = &self.native_gadget;
        let filler = filler.unwrap_or(T::FILLER);
        let (data_val, len_val) = value
            .map(|v| {
                assert!(v.len() <= M);
                let len = F::from(v.len() as u64);
                let mut buffer = [filler; M];
                buffer[get_lims::<M, A>(v.len())].copy_from_slice(v.as_slice());
                (buffer, len)
            })
            .unzip();

        let data = ng
            .assign_many(layouter, &data_val.transpose_array())?
            .try_into()
            .expect("Length mismatch in AssignedVector.");
        let len = ng.assign_lower_than_fixed(layouter, len_val, &(M + 1).into())?;
        Ok(AssignedVector { buffer: data, len })
    }

    fn padding_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<[AssignedBit<F>; M], Error> {
        let ng = &self.native_gadget;
        let (start, end) = self.get_limits(layouter, input)?;
        let mut is_data: AssignedBit<F> = ng.assign_fixed(layouter, true)?;

        let result = (0..M - A)
            .map(|i| {
                let is_start = ng.is_equal_to_fixed(layouter, &start, F::from(i as u64))?;
                is_data = ng.xor(layouter, &[is_data.clone(), is_start])?;
                Ok(is_data.clone())
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let last_chunk = (M - A..M)
            .map(|i| {
                let is_end = ng.is_equal_to_fixed(layouter, &end, F::from(i as u64))?;
                is_data = ng.xor(layouter, &[is_data.clone(), is_end])?;
                Ok(is_data.clone())
            })
            .collect::<Result<Vec<_>, Error>>()?;

        Ok([result, last_chunk]
            .concat()
            .try_into()
            .expect("Mismatch in vector lengths"))
    }

    fn get_limits(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error> {
        let ng = &self.native_gadget;
        let end: AssignedNative<F> = {
            // The last data position within the last chunk. Value in [0, A);
            // 0 means the last chunk is full, all its positions are data.
            let offset = ng.modulus(layouter, &input.len, M as u32, A as u32)?;

            // if offset != 0.  End = M - (A - offset).
            let end1 = ng.add_constant(layouter, &offset, F::from(M as u64 - A as u64))?;
            // if offset == 0.  End = M - (A - offset) + A = M.
            let end2 = ng.add_constant(layouter, &end1, F::from(A as u64))?;
            let is_zero = ng.is_equal_to_fixed(layouter, &offset, F::ZERO)?;
            ng.select(layouter, &is_zero, &end2, &end1)
        }?;

        // The index where the data starts.
        let start: AssignedNative<F> = ng.sub(layouter, &end, &input.len)?;

        Ok((start, end))
    }

    fn trim_beginning(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
        n_elems: usize,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        let ng = &self.native_gadget;
        let a_max_bits = (usize::BITS - A.leading_zeros()) as usize;

        // Assert input.len >= n_elems.
        let len_complement =
            ng.linear_combination(layouter, &[(-F::ONE, input.len.clone())], F::from(M as u64))?;
        ng.assert_lower_than_fixed(layouter, &len_complement, &BigUint::from(M + 1 - n_elems))?;

        // We divide the number of elements to be trimmed in 2 parts.
        // The A-sized whole chunks, one last <A sized piece.
        // (1) The A-sized chunks won't modify the alignment, so modifying the value
        // the vector length is enough to have them trimmed. They will remain
        // in the buffer but they will be considered padding.
        // (2) Trimming this last piece may require some realignment of the vector
        // that ensures the padding at the end remains in [0, A).

        let last_trim = n_elems % A;

        // Length of last chunk ( or 0 if it is full ).
        let last_len = ng.modulus(layouter, &input.len, M as u32, A as u32)?;

        // `modulus` already ensures last_len is in [0, A), so unsafe conversion can be
        // used here.
        let bounded_last_len =
            AssignedBounded::to_assigned_bounded_unsafe(&last_len, a_max_bits as u32);

        // We need to shift right by A if the padding at the end after the left shift is
        // >= A.
        let needs_adjust = {
            let leq_shift = ng.leq_fixed(layouter, &bounded_last_len, F::from(last_trim as u64))?;
            let full_last = ng.is_equal_to_fixed(layouter, &last_len, F::ZERO)?;

            // Since full_last = 1 => leq_shift = 1:
            //     let not_full_last = ng.not(layouter, &full_last)?;
            //     ng.and(layouter, &[not_full_last, leq_shift])
            // A XOR operation is equivalent to the commented code above.
            ng.xor(layouter, &[full_last, leq_shift])
        }?;

        // Shift the original buffer `last_trim` positions to the left.
        // Then, add A filler elements to the left, in case we need to shift A to the
        // right to adjust the padding at the end.
        let buffer = {
            let filler = ng.assign_many_fixed(layouter, &vec![T::FILLER; A + last_trim])?;
            [&filler[..A], &input.buffer[last_trim..], &filler[A..]].concat()
        };
        debug_assert_eq!(buffer.len(), M + A);

        let buffer: [_; M] = (0..M)
            .map(|i| ng.select(layouter, &needs_adjust, &buffer[i], &buffer[A + i]))
            .collect::<Result<Vec<_>, Error>>()?
            .try_into()
            .unwrap();

        // Compute final length.
        let len = ng.add_constant(layouter, &input.len, -F::from(n_elems as u64))?;

        Ok(AssignedVector { buffer, len })
    }
}

impl<F, const M: usize, T, const A: usize> AssignmentInstructions<F, AssignedVector<F, T, M, A>>
    for VectorGadget<F>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    Self: VectorInstructions<F, T, M, A>,
{
    fn assign_fixed(
        &self,
        _layouter: &mut impl Layouter<F>,
        _constant: <AssignedVector<F, T, M, A> as InnerValue>::Element,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        unimplemented!("You should not be assigining a fixed `AssignedVector`")
    }

    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<<AssignedVector<F, T, M, A> as InnerValue>::Element>,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        self.assign_with_filler(layouter, value, None)
    }
}

impl<F, const M: usize, T, const A: usize> EqualityInstructions<F, AssignedVector<F, T, M, A>>
    for VectorGadget<F>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    Self: VectorInstructions<F, T, M, A>,
    NG<F>: ArithInstructions<F, AssignedNative<F>>
        + EqualityInstructions<F, T>
        + EqualityInstructions<F, AssignedNative<F>>
        + BinaryInstructions<F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        y: &AssignedVector<F, T, M, A>,
    ) -> Result<AssignedBit<F>, Error> {
        let ng = &self.native_gadget;
        // Check all data values are equal.
        let val_checks = self
            .padding_flag(layouter, x)?
            .into_iter()
            .zip(x.buffer.iter().zip(y.buffer.iter()))
            .map(|(is_padding, (a, b))| {
                let a_eq_b = ng.is_equal(layouter, a, b)?;
                ng.or(layouter, &[is_padding, a_eq_b])
            })
            .collect::<Result<Vec<_>, Error>>()?;

        // Check lengths are equal.
        let len_check = ng.is_equal(layouter, &x.len, &y.len)?;

        ng.and(layouter, &[val_checks.as_slice(), &[len_check]].concat())
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        constant: Vec<T::Element>,
    ) -> Result<AssignedBit<F>, Error> {
        let ng = &self.native_gadget;
        let ct_len = constant.len();

        let eq_len = ng.is_equal_to_fixed(layouter, &x.len, F::from(ct_len as u64))?;

        let mut element_checks = x.buffer[get_lims::<M, A>(ct_len)]
            .iter()
            .zip(constant.iter())
            .map(|(a, c)| ng.is_equal_to_fixed(layouter, a, *c))
            .collect::<Result<Vec<_>, Error>>()?;
        element_checks.push(eq_len);

        ng.and(layouter, &element_checks)
    }
}

impl<F, T, const M: usize, const A: usize> AssertionInstructions<F, AssignedVector<F, T, M, A>>
    for VectorGadget<F>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    Self: VectorInstructions<F, T, M, A> + EqualityInstructions<F, AssignedVector<F, T, M, A>>,
    NG<F>: ArithInstructions<F, AssignedNative<F>>
        + EqualityInstructions<F, T>
        + EqualityInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedBit<F>>
        + AssertionInstructions<F, T>
        + BinaryInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        y: &AssignedVector<F, T, M, A>,
    ) -> Result<(), Error> {
        let is_equal = self.is_equal(layouter, x, y)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &is_equal, true)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        y: &AssignedVector<F, T, M, A>,
    ) -> Result<(), Error> {
        let x_eq_y = self.is_equal(layouter, x, y)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &x_eq_y, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        constant: <AssignedVector<F, T, M, A> as InnerValue>::Element,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;
        let ct_len = constant.len();
        ng.assert_equal_to_fixed(layouter, &x.len, F::from(ct_len as u64))?;

        x.buffer[get_lims::<M, A>(ct_len)]
            .iter()
            .zip(constant.iter())
            .map(|(a, c)| ng.assert_equal_to_fixed(layouter, a, *c))
            .collect::<Result<Vec<()>, Error>>()?;
        Ok(())
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        constant: <AssignedVector<F, T, M, A> as InnerValue>::Element,
    ) -> Result<(), Error> {
        let is_equal = self.is_equal_to_fixed(layouter, x, constant)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &is_equal, false)
    }
}

#[cfg(test)]
mod tests {
    use ff::{Field, FromUniformBytes, PrimeField};
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand_chacha::{rand_core::SeedableRng, ChaCha12Rng};

    use super::*;
    use crate::{
        field::{
            decomposition::chip::{P2RDecompositionChip, P2RDecompositionConfig},
            AssignedNative, NativeChip, NativeGadget,
        },
        testing_utils::FromScratch,
        utils::{circuit_modeling::circuit_to_json, util::fe_to_big},
    };

    struct TestCircuit<F: PrimeField, const M: usize, const A: usize> {
        input_1: Value<Vec<F>>,
        input_2: Vec<F>, // We don't use value here in order to easily mutate the padding.
        opts: TestOpts,
    }

    enum TestOpts {
        // Tests vector equality.
        Eq { mutate_padding: bool, equal: bool },
        // Test data limit (indices) on a vector.
        Limits,
        // Test padding_flag instruction.
        Padding,
        // Test trim.
        Trim { trim_size: usize },
    }

    type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
    impl<F: PrimeField, const M: usize, const A: usize> Circuit<F> for TestCircuit<F, M, A> {
        type Config = P2RDecompositionConfig;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!();
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let comm_ic = meta.instance_column();
            let instance_column = meta.instance_column();
            NativeGadget::configure_from_scratch(meta, &[comm_ic, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let ng = NG::<F>::new_from_scratch(&config);
            let vg = VectorGadget::new(&ng);
            NG::<F>::load_from_scratch(&mut layouter, &config);

            match self.opts {
                TestOpts::Eq {
                    mutate_padding,
                    equal,
                } => {
                    let vec_1: AssignedVector<F, AssignedNative<F>, M, A> =
                        vg.assign(&mut layouter, self.input_1.clone())?;

                    let mut vec_2: AssignedVector<F, AssignedNative<F>, M, A> =
                        vg.assign(&mut layouter, Value::known(self.input_2.clone()))?;

                    // Mutate padding
                    if mutate_padding {
                        let range = get_lims::<M, A>(self.input_2.len());
                        for i in 0..range.start {
                            vec_2.buffer[i] =
                                ng.add_constant(&mut layouter, &vec_2.buffer[i], F::ONE)?;
                        }
                        for i in range.end..M {
                            vec_2.buffer[i] =
                                ng.add_constant(&mut layouter, &vec_2.buffer[i], F::ONE)?;
                        }
                    }

                    let check = vg.is_equal(&mut layouter, &vec_1, &vec_2)?;

                    ng.assert_equal_to_fixed(&mut layouter, &check, equal)?;
                }
                TestOpts::Limits => {
                    let vec_1: AssignedVector<F, AssignedNative<F>, M, A> =
                        vg.assign(&mut layouter, self.input_1.clone())?;

                    let limits = vg.get_limits(&mut layouter, &vec_1)?;
                    let (start, end) = vec_1
                        .len
                        .value()
                        .map(|l| {
                            let len: usize = fe_to_big(*l).try_into().unwrap();
                            let range = get_lims::<M, A>(len);
                            (F::from(range.start as u64), F::from(range.end as u64))
                        })
                        .unzip();
                    let start = ng.assign(&mut layouter, start)?;
                    let end = ng.assign(&mut layouter, end)?;
                    ng.assert_equal(&mut layouter, &limits.0, &start)?;
                    ng.assert_equal(&mut layouter, &limits.1, &end)?;
                }

                TestOpts::Padding => {
                    let vec_1: AssignedVector<F, AssignedNative<F>, M, A> =
                        vg.assign(&mut layouter, self.input_1.clone())?;

                    let expected: [Value<bool>; M] = vec_1
                        .len
                        .value()
                        .map(|l| {
                            let len: usize = fe_to_big(*l).try_into().unwrap();
                            let range = get_lims::<M, A>(len);
                            let mut result = vec![true; M];
                            result[range].iter_mut().for_each(|r| {
                                *r = false;
                            });
                            result.try_into().unwrap()
                        })
                        .transpose_array();

                    let result = vg.padding_flag(&mut layouter, &vec_1)?;

                    for (r, e) in result.iter().zip(expected.iter()) {
                        let e: AssignedBit<F> = ng.assign(&mut layouter, *e)?;
                        ng.assert_equal(&mut layouter, &e, r)?;
                    }
                }

                TestOpts::Trim { trim_size: n_elems } => {
                    let vec_1: AssignedVector<F, AssignedNative<F>, M, A> =
                        vg.assign(&mut layouter, self.input_1.clone())?;

                    let result = vg.trim_beginning(&mut layouter, &vec_1, n_elems)?;

                    vg.assert_equal_to_fixed(&mut layouter, &result, self.input_2.clone())?;
                }
            }

            Ok(())
        }
    }

    fn run_eq_vec_test<F, const M: usize, const A: usize>(
        input_1: &[F],
        input_2: &[F],
        equal: bool,
        mutate_padding: bool,
        cost_model: bool,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, M, A> {
            input_1: Value::known(input_1.to_vec()),
            input_2: input_2.to_vec(),
            opts: TestOpts::Eq {
                equal,
                mutate_padding,
            },
        };

        let k = 14;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(
                k,
                "Vector equality",
                format!("Vector equality check with M={M}").as_str(),
                0,
                circuit,
            );
        }
    }

    fn run_limit_vec_test<F, const M: usize, const A: usize>(input_1: &[F], cost_model: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, M, A> {
            input_1: Value::known(input_1.to_vec()),
            input_2: vec![],
            opts: TestOpts::Limits,
        };

        let k = 14;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(
                k,
                "Vector limits check",
                format!("Vector limit check with M={M}").as_str(),
                0,
                circuit,
            );
        }
    }

    fn run_padding_flags_test<F, const M: usize, const A: usize>(input_1: &[F], cost_model: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, M, A> {
            input_1: Value::known(input_1.to_vec()),
            input_2: vec![],
            opts: TestOpts::Padding,
        };

        let k = 14;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(
                k,
                "Vector padding flags.",
                format!("Vector padding flags with M={M}").as_str(),
                0,
                circuit,
            );
        }
    }

    fn run_trim_vec_test<F, const M: usize, const A: usize>(
        input_1: &[F],
        trim_size: usize,
        cost_model: bool,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let input = input_1.to_vec();
        assert!(trim_size <= input.len());
        let circuit = TestCircuit::<F, M, A> {
            input_1: Value::known(input.clone()),
            input_2: input[trim_size..].to_vec(),
            opts: TestOpts::Trim { trim_size },
        };

        let k = 14;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(
                k,
                "Vector trim beginning.",
                format!("Vector trim_beginning with M={M}").as_str(),
                0,
                circuit,
            );
        }
    }

    #[test]
    fn vector_eq() {
        type F = midnight_curves::Fq;

        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xdeadcafe);
        let inputs = (0..100).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        // Equal vectors, different padding.
        run_eq_vec_test::<_, 128, 2>(&inputs, &inputs, true, true, true);
        run_eq_vec_test::<_, 128, 3>(&inputs, &inputs, true, true, false);

        // Equal vectors, equal padding.
        run_eq_vec_test::<_, 128, 2>(&inputs, &inputs, true, false, false);

        // Equal data, different length.
        run_eq_vec_test::<_, 128, 2>(&inputs[..80], &inputs[..81], false, false, false);

        // Different data.
        run_eq_vec_test::<_, 128, 2>(
            &[&[F::ZERO], &inputs[..80]].concat(),
            &[&[F::ONE], &inputs[..80]].concat(),
            false,
            false,
            false,
        );
    }

    #[test]
    fn vector_lims() {
        type F = midnight_curves::Fq;

        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xdeadcafe);
        let inputs = (0..100).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        // Test different alignments.
        run_limit_vec_test::<_, 128, 1>(&inputs, true);
        run_limit_vec_test::<_, 128, 2>(&inputs, false);
        run_limit_vec_test::<_, 128, 3>(&inputs, false);
        run_limit_vec_test::<_, 128, 4>(&inputs, false);
        run_limit_vec_test::<_, 128, 5>(&inputs, false);

        // Test edge cases.
        run_limit_vec_test::<_, 64, 2>(&inputs[..64], false);
        run_limit_vec_test::<F, 64, 2>(&[], false);
    }

    #[test]
    fn vector_padding_flags() {
        type F = midnight_curves::Fq;

        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xdeadcafe);
        let inputs = (0..100).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        run_padding_flags_test::<_, 128, 1>(&inputs, true);
        run_padding_flags_test::<_, 128, 2>(&inputs, false);
        run_padding_flags_test::<_, 128, 3>(&inputs, false);
        run_padding_flags_test::<_, 128, 64>(&inputs, false);
        run_padding_flags_test::<F, 128, 64>(&[], false);
        run_padding_flags_test::<F, 64, 16>(&inputs[..64], false);
    }

    #[test]
    fn vector_trim_beginning() {
        type F = midnight_curves::Fq;

        // Create a random number generator
        let mut rng = ChaCha12Rng::seed_from_u64(0xdeadcafe);
        let inputs = (0..100).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        // Test different alignments (under A).
        run_trim_vec_test::<_, 128, 64>(&[F::ONE, F::ONE], 1, true);
        run_trim_vec_test::<_, 128, 32>(&inputs, 0, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 1, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 2, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 3, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 4, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 5, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 30, false);
        run_trim_vec_test::<_, 128, 32>(&inputs, 31, false);

        // Above or equal to A.
        run_trim_vec_test::<_, 128, 3>(&inputs, 3, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 4, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 5, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 6, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 10, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 20, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 30, false);
        run_trim_vec_test::<_, 128, 3>(&inputs, 40, false);

        // Edge case: offset of original vector = 0;
        run_trim_vec_test::<_, 128, 32>(&inputs[..96], 23, false);

        // Edge case: full vector;
        run_trim_vec_test::<_, 64, 32>(&inputs[..64], 20, false);

        // Edge case: full vector, trim all elements.
        run_trim_vec_test::<_, 64, 32>(&inputs[..64], 64, false);

        // The particular case of the credentials:
        run_trim_vec_test::<_, 128, 64>(&inputs, 39, false);
    }
}

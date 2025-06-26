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

use std::ops::Range;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use super::types::InnerValue;
use crate::{
    field::{
        decomposition::instructions::CoreDecompositionInstructions, AssignedNative, NativeGadget,
    },
    instructions::{
        divmod::DivisionInstructions, ArithInstructions, AssertionInstructions,
        AssignmentInstructions, BinaryInstructions, ControlFlowInstructions, EqualityInstructions,
        RangeCheckInstructions,
    },
    types::{AssignedBit, AssignedByte},
};

/// A variable-length vector of elements of type T, with size bound M.
/// - `len` is the (potentially secret) effective length of the vector, its
///   value is guaranteed to be in the range `[0, M]`.
/// - `buffer` is the padded payload of this vector; it contains the effective
///   data of the vector as well as filler values, which are UNCONSTRAINED.
///
/// The effective payload in the data is aligned in A sized chunks. This
/// enables more efficient implementations of instructions like hashing
/// over this type. As a result of this alignment, the data may contain filler
/// values before and after the effective payload. The padding in front of of
/// the payload will always be 0 mod A, so that the payload begins aligned in A
/// sized chunks. The padding at the end of the payload will be have a size in
/// [0, A) such that | front_pad | + | payload | + | back_pad | = M
#[derive(Clone, Debug)]
pub struct AssignedVector<F: PrimeField, T: Vectorizable, const M: usize, const A: usize> {
    /// Padded payload of the vector.
    pub(crate) buffer: [T; M],

    /// Effective length of the vector.
    pub(crate) len: AssignedNative<F>,
}

/// Returns the range where the data should be placed in the buffer.
fn get_lims<const M: usize, const A: usize>(len: usize) -> Range<usize> {
    let final_pad_len = (A - (len % A)) % A;
    M - len - final_pad_len..M - final_pad_len
}

impl<F: PrimeField, const M: usize, T: Vectorizable, const A: usize> InnerValue
    for AssignedVector<F, T, M, A>
{
    type Element = Vec<T::Element>;

    fn value(&self) -> Value<Self::Element> {
        let data = Value::<Vec<T::Element>>::from_iter(self.buffer.iter().map(|v| v.value()));
        let idxs: Value<_> = self.len.value().map(|len| {
            let len: usize = super::util::fe_to_big(*len).try_into().unwrap();

            let end_pad = (A - (len % A)) % A;
            (M - len - end_pad, M - end_pad)
        });
        data.zip(idxs)
            .map(|(data, idxs)| data[idxs.0..idxs.1].to_vec())
    }
}

/// Trait for the individual elements of an AssignedVector.
pub trait Vectorizable: InnerValue {
    /// Value to fill the space in the buffer that is not occupied with vector
    /// data.
    const FILLER: Self::Element;
}

impl<F: PrimeField> Vectorizable for AssignedNative<F> {
    const FILLER: F = F::ZERO;
}

impl<F: PrimeField> Vectorizable for AssignedByte<F> {
    const FILLER: u8 = 0u8;
}

/// Instruction set for transforming vectors.
pub trait VectorInstructions<F, T, const M: usize, const A: usize>:
    AssignmentInstructions<F, T>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    Self: RangeCheckInstructions<F, AssignedNative<F>> + AssignmentInstructions<F, T>,
{
    /// Changes the size of an AssignedVector from M to L.
    ///
    /// # Panics
    ///
    /// If `L <= M` or `A` does not divide `L`.
    fn resize<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedVector<F, T, M, A>,
    ) -> Result<AssignedVector<F, T, L, A>, Error> {
        assert_eq!(L % A, 0);
        assert!(L > M);

        let extra_pad = self.assign_many(layouter, &vec![Value::known(T::FILLER); L - M])?;

        let buffer: [T; L] = [extra_pad.as_slice(), input.buffer.as_slice()]
            .concat()
            .try_into()
            .unwrap();

        Ok(AssignedVector {
            buffer,
            len: input.len.clone(),
        })
    }

    /// Assigns vector with a chosen filler value.
    ///
    /// # Panics
    ///
    /// If |value| > M.
    fn assign_with_filler(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<T::Element>>,
        filler: Option<T::Element>,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
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

        let data = self
            .assign_many(layouter, &data_val.transpose_array())?
            .try_into()
            .expect("Length mismatch in AssignedVector.");
        let len = self.assign_lower_than_fixed(layouter, len_val, &(M + 1).into())?;
        Ok(AssignedVector { buffer: data, len })
    }

    /// Returns a vector of AssignedBits signaling the cells that represent
    /// padding with a 1, and the ones that represent payload data with a 0.
    fn padding_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<[AssignedBit<F>; M], Error>;

    /// Returns the first and last positions of data in the buffer.
    fn get_limits(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error>;
}

impl<F, CD, NA, T, const M: usize, const A: usize> VectorInstructions<F, T, M, A>
    for NativeGadget<F, CD, NA>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    CD: CoreDecompositionInstructions<F>,
    Self: RangeCheckInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, T>
        + AssignmentInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + EqualityInstructions<F, AssignedNative<F>>
        + BinaryInstructions<F>
        + ControlFlowInstructions<F, AssignedNative<F>>
        + DivisionInstructions<F>,
    NA: ArithInstructions<F, AssignedNative<F>>,
{
    fn padding_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<[AssignedBit<F>; M], Error> {
        let (start, end) = self.get_limits(layouter, input)?;
        let mut is_data: AssignedBit<F> = self.assign_fixed(layouter, true)?;

        let result = (0..M - A)
            .map(|i| {
                let is_start = self.is_equal_to_fixed(layouter, &start, F::from(i as u64))?;
                is_data = self.xor(layouter, &[is_data.clone(), is_start])?;
                Ok(is_data.clone())
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let last_chunk = (M - A..M)
            .map(|i| {
                let is_end = self.is_equal_to_fixed(layouter, &end, F::from(i as u64))?;
                is_data = self.xor(layouter, &[is_data.clone(), is_end])?;
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
        let end: AssignedNative<F> = {
            // The last data position within the last chunk. Value in [0, A);
            // 0 means the last chunk is full, all its positions are data.
            let (_, offset) = self.div_rem(layouter, &input.len, M as u32, A as u32)?;

            // if offset != 0.  End = M - (A - offset).
            let end1 = self.add_constant(layouter, &offset, F::from(M as u64 - A as u64))?;
            // if offset == 0.  End = M - (A - offset) + A = M.
            let end2 = self.add_constant(layouter, &end1, F::from(A as u64))?;
            let is_zero = self.is_equal_to_fixed(layouter, &offset, F::ZERO)?;
            self.select(layouter, &is_zero, &end2, &end1)
        }?;

        // The index where the data starts.
        let start: AssignedNative<F> = self.sub(layouter, &end, &input.len)?;

        Ok((start, end))
    }
}

impl<F, CoreDecomposition, NativeArith, const M: usize, T, const A: usize>
    EqualityInstructions<F, AssignedVector<F, T, M, A>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
    Self: EqualityInstructions<F, T>
        + EqualityInstructions<F, AssignedNative<F>>
        + VectorInstructions<F, T, M, A>
        + BinaryInstructions<F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        y: &AssignedVector<F, T, M, A>,
    ) -> Result<AssignedBit<F>, Error> {
        // Check all data values are equal.
        let val_checks = self
            .padding_flag(layouter, x)?
            .into_iter()
            .zip(x.buffer.iter().zip(y.buffer.iter()))
            .map(|(is_padding, (a, b))| {
                let a_eq_b = self.is_equal(layouter, a, b)?;
                self.or(layouter, &[is_padding, a_eq_b])
            })
            .collect::<Result<Vec<_>, Error>>()?;

        // Check lengths are equal.
        let len_check = self.is_equal(layouter, &x.len, &y.len)?;

        self.and(layouter, &[val_checks.as_slice(), &[len_check]].concat())
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        constant: Vec<T::Element>,
    ) -> Result<AssignedBit<F>, Error> {
        let ct_len = constant.len();

        let eq_len = self.is_equal_to_fixed(layouter, &x.len, F::from(ct_len as u64))?;

        let mut element_checks = x.buffer[get_lims::<M, A>(ct_len)]
            .iter()
            .zip(constant.iter())
            .map(|(a, c)| self.is_equal_to_fixed(layouter, a, *c))
            .collect::<Result<Vec<_>, Error>>()?;
        element_checks.push(eq_len);

        self.and(layouter, &element_checks)
    }
}

impl<F, CoreDecomposition, NativeArith, const M: usize, T, const A: usize>
    AssertionInstructions<F, AssignedVector<F, T, M, A>>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    T: Vectorizable,
    T::Element: Copy,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>,
    Self: EqualityInstructions<F, T>
        + EqualityInstructions<F, AssignedNative<F>>
        + EqualityInstructions<F, AssignedVector<F, T, M, A>>
        + AssertionInstructions<F, AssignedBit<F>>
        + AssertionInstructions<F, T>
        + VectorInstructions<F, T, M, A>
        + BinaryInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        y: &AssignedVector<F, T, M, A>,
    ) -> Result<(), Error> {
        let is_equal = self.is_equal(layouter, x, y)?;
        self.assert_equal_to_fixed(layouter, &is_equal, true)
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        y: &AssignedVector<F, T, M, A>,
    ) -> Result<(), Error> {
        let x_eq_y = self.is_equal(layouter, x, y)?;
        self.assert_equal_to_fixed(layouter, &x_eq_y, false)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedVector<F, T, M, A>,
        constant: <AssignedVector<F, T, M, A> as InnerValue>::Element,
    ) -> Result<(), Error> {
        let ct_len = constant.len();
        self.assert_equal_to_fixed(layouter, &x.len, F::from(ct_len as u64))?;

        x.buffer[get_lims::<M, A>(ct_len)]
            .iter()
            .zip(constant.iter())
            .map(|(a, c)| self.assert_equal_to_fixed(layouter, a, *c))
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
        self.assert_equal_to_fixed(layouter, &is_equal, false)
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
            NG::<F>::load_from_scratch(&mut layouter, &config);

            match self.opts {
                TestOpts::Eq {
                    mutate_padding,
                    equal,
                } => {
                    let vec_1: AssignedVector<F, AssignedNative<F>, M, A> =
                        ng.assign(&mut layouter, self.input_1.clone())?;

                    let mut vec_2: AssignedVector<F, AssignedNative<F>, M, A> =
                        ng.assign(&mut layouter, Value::known(self.input_2.clone()))?;

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

                    let check = ng.is_equal(&mut layouter, &vec_1, &vec_2)?;

                    ng.assert_equal_to_fixed(&mut layouter, &check, equal)?;
                }
                TestOpts::Limits => {
                    let vec_1: AssignedVector<F, AssignedNative<F>, M, A> =
                        ng.assign(&mut layouter, self.input_1.clone())?;

                    let limits = ng.get_limits(&mut layouter, &vec_1)?;
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
                        ng.assign(&mut layouter, self.input_1.clone())?;

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

                    let result = ng.padding_flag(&mut layouter, &vec_1)?;

                    for (r, e) in result.iter().zip(expected.iter()) {
                        let e: AssignedBit<F> = ng.assign(&mut layouter, *e)?;
                        ng.assert_equal(&mut layouter, &e, r)?;
                    }
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

    #[test]
    fn vector_eq() {
        type F = blstrs::Fq;

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
        type F = blstrs::Fq;

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
        type F = blstrs::Fq;

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
}

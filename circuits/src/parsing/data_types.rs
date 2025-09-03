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
use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use super::ParserGadget;
use crate::{field::AssignedNative, instructions::NativeInstructions, types::AssignedByte};

/// Order of day, month and year in the date string.
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Copy, Debug)]
pub enum DateFormat {
    /// Year, month, day.
    YYYYMMDD,
    /// Day, month, year.
    DDMMYYYY,
}

/// Date strings may have 1 character separating year, month and day
/// or no separator.
#[derive(Clone, Copy, Debug)]
pub enum Separator {
    /// No separator between day, month and year.
    NoSep,
    /// Day, month and year separated by the specified character.
    Sep(char),
}

impl<F, N> ParserGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    /// Given an assigned byte as a character represented in ASCII,
    /// returns its numeric value as an assigned native.
    ///
    /// # Unsatisfiable
    ///  - The input byte is constrained to be an ASCII digit.
    fn ascii_to_digit(
        &self,
        layouter: &mut impl Layouter<F>,
        byte: &AssignedByte<F>,
    ) -> Result<AssignedNative<F>, Error> {
        // Digits in ascii are represented by the values [48-58].
        // So substracting 48 gives the represented value.
        let val = self
            .native_gadget
            .add_constant(layouter, &byte.into(), -F::from(48u64))?;
        self.native_gadget
            .assert_lower_than_fixed(layouter, &val, &BigUint::from(10u64))?;
        Ok(val)
    }

    /// Given a string of ASCII digits as assigned bytes, returns the
    /// represented integer as an assigned native.
    /// Leading 0s are allowed.
    ///
    /// # Unsatisfiable
    ///  - The input bytes are not valid ascii digits. That is, are outside the
    ///    [48-58] range.
    ///
    /// # Panics
    ///  - The input length exceeds the number of digits that can fit in the
    ///    native field.
    pub fn ascii_to_int(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<AssignedNative<F>, Error> {
        let native = &self.native_gadget;
        let digit_capacity = (F::CAPACITY as f64 / 10f64.log2()) as usize;
        let n = input.len();
        assert!(
            n < digit_capacity,
            "Cannot parse intgers with more than {digit_capacity} digits"
        );

        let mut terms = Vec::with_capacity(n);
        let mut base = F::ONE;
        for byte in input.iter().rev() {
            let val = self.ascii_to_digit(layouter, byte)?;
            terms.push((base, val));
            base *= F::from(10u64);
        }

        let res = native.linear_combination(layouter, terms.as_slice(), F::ZERO)?;

        Ok(res)
    }

    /// Given an ASCII string of assigned bytes, representing a date in the
    /// specified format, returns  DD + 100 * MM + 10_000 * YYYY as an assigned
    /// native value. This function does not check the validity of the date,
    /// i.e. (in DDMMYYYY, NoSep) format, "32011990" will be accepted as 32
    /// January 1990. Concretely, no range check is performed on the values,
    /// so implicitly all *dates* in the range [0-99] / [0-99] / [0-9999]
    /// are accepted.
    pub fn date_to_int(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
        format: (DateFormat, Separator),
    ) -> Result<AssignedNative<F>, Error> {
        let native = &self.native_gadget;
        let n = input.len();

        // Indices for day, month, year bytes in the input.
        let indices: (_, _, _) = match format {
            (DateFormat::DDMMYYYY, Separator::NoSep) => {
                assert_eq!(n, 8, "Date format must be 8 characters long: DDMMYYYY");
                ((0..2), (2..4), (4..8))
            }

            (DateFormat::DDMMYYYY, Separator::Sep(sep)) => {
                assert_eq!(
                    n, 10,
                    "Date format must be 10 characters long: DD{sep}MM{sep}YYYY"
                );

                native.assert_equal_to_fixed(layouter, &input[2], sep as u8)?;
                native.assert_equal_to_fixed(layouter, &input[5], sep as u8)?;
                ((0..2), (3..5), (6..10))
            }

            (DateFormat::YYYYMMDD, Separator::NoSep) => {
                assert_eq!(n, 8, "Date format must be 8 characters long: YYYYMMDD");
                ((6..8), (4..6), (0..4))
            }

            (DateFormat::YYYYMMDD, Separator::Sep(sep)) => {
                assert_eq!(
                    n, 10,
                    "Date format must be 10 characters long: YYYY{sep}MM{sep}DD"
                );

                native.assert_equal_to_fixed(layouter, &input[4], sep as u8)?;
                native.assert_equal_to_fixed(layouter, &input[7], sep as u8)?;

                ((8..10), (5..7), (0..4))
            }
        };

        let bytes = [&input[indices.2], &input[indices.1], &input[indices.0]].concat();

        self.ascii_to_int(layouter, &bytes)
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;
    use crate::{
        field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
        testing_utils::FromScratch,
    };

    #[derive(Clone, Copy, Debug)]
    enum Operation {
        ParseInt,
        ParseDate((DateFormat, Separator)),
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, N> {
        string: Vec<Value<F>>,
        expected: F,
        operation: Operation,
        _marker: PhantomData<N>,
    }

    impl<F, N> Circuit<F> for TestCircuit<F, N>
    where
        F: PrimeField,
        N: NativeInstructions<F> + FromScratch<F>,
    {
        type Config = <N as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            <N as FromScratch<F>>::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = <N as FromScratch<F>>::new_from_scratch(&config);
            let parser_gadget = ParserGadget::<F, N>::new(&native_gadget);
            <N as FromScratch<F>>::load_from_scratch(&mut layouter, &config);

            let string = native_gadget.assign_many(&mut layouter, &self.string)?;
            let bytes = string
                .iter()
                .map(|x| native_gadget.convert(&mut layouter, x))
                .collect::<Result<Vec<AssignedByte<F>>, Error>>()?;

            let res = match self.operation {
                Operation::ParseInt => parser_gadget.ascii_to_int(&mut layouter, &bytes),
                Operation::ParseDate(format) => {
                    parser_gadget.date_to_int(&mut layouter, &bytes, format)
                }
            }?;

            native_gadget.assert_equal_to_fixed(&mut layouter, &res, self.expected)?;

            Ok(())
        }
    }

    fn run<F>(string: &[u8], expected: u64, operation: Operation, must_pass: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        const K: u32 = 10;
        let circuit = TestCircuit::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>> {
            string: string
                .iter()
                .map(|x| F::from(*x as u64))
                .map(Value::known)
                .collect(),
            expected: F::from(expected),
            operation,
            _marker: PhantomData,
        };
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }
    }

    #[test]
    fn test_parse_int() {
        type F = midnight_curves::Fq;
        let test_vecs: Vec<(&[u8], u64, bool)> = vec![
            (b"987654321", 987654321, true),
            (b"123456", 123456, true),
            (b"123", 123, true),
            (b"0123", 123, true),
            (b"00123", 123, true),
            (b"0", 0, true),
            (b"54321", 54320, false),
            (b"54321", 54322, false),
            (b"54321", 0, false),
        ];
        test_vecs.iter().for_each(|(input, expected, must_pass)| {
            run::<F>(input, *expected, Operation::ParseInt, *must_pass)
        });
    }

    #[test]
    fn test_parse_date() {
        type F = midnight_curves::Fq;
        let format1 = (DateFormat::DDMMYYYY, Separator::NoSep);
        let format2 = (DateFormat::DDMMYYYY, Separator::Sep('-'));
        let format3 = (DateFormat::YYYYMMDD, Separator::Sep('-'));
        let format4 = (DateFormat::YYYYMMDD, Separator::NoSep);

        let test_vecs: Vec<(&[u8], _, _, _)> = vec![
            (b"40052025", format1, 20250540, true),
            (b"01011970", format1, 19700101, true),
            (b"12121970", format1, 19701212, true),
            (b"40121970", format1, 19701240, true),
            (b"01011970", format1, 19700102, false),
            (b"40-05-2025", format2, 20250540, true),
            (b"01-01-1970", format2, 19700101, true),
            (b"12-12-1970", format2, 19701212, true),
            (b"40-12-1970", format2, 19701240, true),
            (b"01-01-1970", format2, 19700102, false),
            (b"02-01-1970", format2, 19700201, false),
            (b"01/01/1970", format2, 19700102, false),
            (b"2025-05-40", format3, 20250540, true),
            (b"1970-01-01", format3, 19700101, true),
            (b"1970-12-12", format3, 19701212, true),
            (b"20250540", format4, 20250540, true),
            (b"19700101", format4, 19700101, true),
            (b"19701225", format4, 19701225, true),
        ];
        test_vecs
            .iter()
            .for_each(|(input, format, expected, must_pass)| {
                run::<F>(input, *expected, Operation::ParseDate(*format), *must_pass)
            });
    }
}

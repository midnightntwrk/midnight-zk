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

use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use super::ParserGadget;
use crate::{
    field::{native::AssignedBit, AssignedNative},
    instructions::NativeInstructions,
    types::{AssignedByte, InnerValue},
    CircuitField,
};

/// Order of day, month and year in the date string.
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Copy, Debug)]
pub enum DateFormat {
    /// Four-digit year, month, day.
    YYYYMMDD,
    /// Day, month, four-digit year.
    DDMMYYYY,
    /// Two-digit year, month, day. Requires a `century_base` parameter
    /// in [`ParserGadget::date_to_int`] to resolve the century.
    YYMMDD,
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
    F: CircuitField,
    N: NativeInstructions<F>,
{
    /// Given an assigned byte as a character represented in ASCII,
    /// returns its numeric value as an assigned native.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If the input byte is not an ASCII digit, i.e. in the range \[48, 57\].
    fn ascii_to_digit(
        &self,
        layouter: &mut impl Layouter<F>,
        byte: &AssignedByte<F>,
    ) -> Result<AssignedNative<F>, Error> {
        // Digits in ascii are represented by the values in [48, 57].
        // So substracting 48 gives the represented value.
        let val = self.native_gadget.add_constant(layouter, &byte.into(), -F::from(48u64))?;
        self.native_gadget
            .assert_lower_than_fixed(layouter, &val, &BigUint::from(10u64))?;
        Ok(val)
    }

    /// Given a string of ASCII digits as assigned bytes, returns the
    /// represented integer as an assigned native.
    /// Leading 0s are allowed.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If the input bytes are not valid ASCII digits, i.e. in the range
    /// \[48, 57\].
    ///
    /// # Panics
    ///
    /// If |input| exceeds the maximum number of digits that can be reliably
    /// stored in an `F` element.
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
    /// specified format, returns `DD + 100 * MM + 10_000 * YYYY` as an
    /// assigned native value. This function does not check the validity of
    /// the date (e.g. `"32011990"` in DDMMYYYY is accepted as 32 January
    /// 1990).
    ///
    /// For two-digit year formats ([`DateFormat::YYMMDD`]), `century_base`
    /// must be `Some(N)` where N is an assigned value in [0, 99]. The year
    /// is then resolved as `1900 + YY + (if YY < N { 100 } else { 0 })`,
    /// i.e. the 100-year window is [1900+N, 2000+N). The caller is
    /// responsible for constraining N < 100.
    ///
    /// For four-digit year formats, `century_base` must be `None`.
    pub fn date_to_int(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
        format: (DateFormat, Separator),
        century_base: Option<&AssignedNative<F>>,
    ) -> Result<AssignedNative<F>, Error> {
        let native = &self.native_gadget;
        let n = input.len();

        match format {
            (DateFormat::YYMMDD, Separator::NoSep) => {
                assert_eq!(n, 6, "Date format must be 6 characters long: YYMMDD");
                let century_base =
                    century_base.expect("YYMMDD format requires a century_base parameter");
                self.date_to_int_short_year(layouter, input, century_base)
            }
            (DateFormat::YYMMDD, Separator::Sep(_)) => {
                panic!("YYMMDD with separator is not supported")
            }
            _ => {
                assert!(
                    century_base.is_none(),
                    "century_base is only used with YYMMDD format"
                );
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
                    (DateFormat::YYMMDD, _) => unreachable!(),
                };
                let bytes = [&input[indices.2], &input[indices.1], &input[indices.0]].concat();
                self.ascii_to_int(layouter, &bytes)
            }
        }
    }

    /// Resolves a 6-byte YYMMDD date into a YYYYMMDD integer using the
    /// century base N. The year is `1900 + YY + (if YY < N { 100 } else { 0
    /// })`.
    fn date_to_int_short_year(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
        century_base: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let native = &self.native_gadget;

        let yy = self.ascii_to_int(layouter, &input[0..2])?;
        let mmdd = self.ascii_to_int(layouter, &input[2..6])?;

        // Off-circuit: compute is_20xx = (YY < N).
        let yy_val = input[0]
            .value()
            .zip(input[1].value())
            .map(|(d0, d1)| (d0 - 48) as u64 * 10 + (d1 - 48) as u64);
        let n_val =
            InnerValue::value(century_base).map(|be| u64::try_from(be.to_biguint()).unwrap());
        let is_20xx_val = yy_val.zip(n_val).map(|(yy, n)| yy < n);

        // Assign is_20xx as a bit (constrains it to {0, 1}).
        let is_20xx: AssignedBit<F> = native.assign(layouter, is_20xx_val)?;
        let is_20xx_native: AssignedNative<F> = is_20xx.into();

        // Constrain: yy - century_base + is_20xx * 100 ∈ [0, 128).
        // This enforces the correct relationship between is_20xx, yy, and N.
        let check = native.linear_combination(
            layouter,
            &[
                (F::ONE, yy.clone()),
                (-F::ONE, century_base.clone()),
                (F::from(100u64), is_20xx_native.clone()),
            ],
            F::ZERO,
        )?;
        native.assert_lower_than_fixed(layouter, &check, &BigUint::from(128u64))?;

        // Result: (1900 + YY + is_20xx * 100) * 10_000 + MMDD
        native.linear_combination(
            layouter,
            &[
                (F::from(10_000u64), yy),
                (F::from(1_000_000u64), is_20xx_native),
                (F::ONE, mmdd),
            ],
            F::from(19_000_000u64),
        )
    }
}

/// A calendar date with a full 4-digit year.
#[derive(Clone, Copy, Debug)]
pub struct Date {
    /// Day of the month (1-31).
    pub day: u8,
    /// Month (1-12).
    pub month: u8,
    /// Four-digit year.
    pub year: u16,
}

impl Date {
    /// Encodes as YYYYMMDD integer: `year * 10_000 + month * 100 + day`.
    pub fn as_yyyymmdd(&self) -> u64 {
        self.year as u64 * 10_000 + self.month as u64 * 100 + self.day as u64
    }
}

impl From<Date> for BigUint {
    fn from(value: Date) -> Self {
        value.as_yyyymmdd().into()
    }
}

impl<F, N> ParserGadget<F, N>
where
    F: CircuitField,
    N: NativeInstructions<F>,
{
    /// Asserts that a date (as assigned bytes in the given format) is
    /// strictly before `limit_date`. Convenience wrapper around
    /// [`date_to_int`](Self::date_to_int) + a range check.
    pub fn assert_date_before_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        date_bytes: &[AssignedByte<F>],
        format: (DateFormat, Separator),
        limit_date: Date,
    ) -> Result<(), Error> {
        let date = self.date_to_int(layouter, date_bytes, format, None)?;
        self.native_gadget.assert_lower_than_fixed(layouter, &date, &limit_date.into())
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
    enum ParseTarget {
        Int,
        Date((DateFormat, Separator)),
        /// Parse a short-year date with `century_base`.
        DateShortYear((DateFormat, Separator), u64),
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, N> {
        string: Vec<Value<F>>,
        expected: F,
        operation: ParseTarget,
        _marker: PhantomData<N>,
    }

    impl<F, N> Circuit<F> for TestCircuit<F, N>
    where
        F: CircuitField,
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

            let string = native_gadget.assign_many(&mut layouter, &self.string)?;
            let bytes = string
                .iter()
                .map(|x| native_gadget.convert(&mut layouter, x))
                .collect::<Result<Vec<AssignedByte<F>>, Error>>()?;

            let res = match self.operation {
                ParseTarget::Int => parser_gadget.ascii_to_int(&mut layouter, &bytes),
                ParseTarget::Date(format) => {
                    parser_gadget.date_to_int(&mut layouter, &bytes, format, None)
                }
                ParseTarget::DateShortYear(format, n) => {
                    let century_base =
                        native_gadget.assign(&mut layouter, Value::known(F::from(n)))?;
                    parser_gadget.date_to_int(&mut layouter, &bytes, format, Some(&century_base))
                }
            }?;

            native_gadget.assert_equal_to_fixed(&mut layouter, &res, self.expected)?;

            native_gadget.load_from_scratch(&mut layouter)
        }
    }

    fn run<F>(string: &[u8], expected: u64, operation: ParseTarget, must_pass: bool)
    where
        F: CircuitField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>> {
            string: string.iter().map(|x| F::from(*x as u64)).map(Value::known).collect(),
            expected: F::from(expected),
            operation,
            _marker: PhantomData,
        };
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(&circuit, public_inputs) {
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
            run::<F>(input, *expected, ParseTarget::Int, *must_pass)
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
        test_vecs.iter().for_each(|(input, format, expected, must_pass)| {
            run::<F>(input, *expected, ParseTarget::Date(*format), *must_pass)
        });
    }

    #[test]
    fn test_parse_date_short_year() {
        type F = midnight_curves::Fq;
        let yymmdd = (DateFormat::YYMMDD, Separator::NoSep);

        // N = 26: window [1926, 2026). YY >= 26 → 19xx, YY < 26 → 20xx.
        let test_vecs: Vec<(&[u8], _, u64, _, _)> = vec![
            (b"000101", yymmdd, 26, 20000101, true),  // YY=0 < 26 → 2000
            (b"251231", yymmdd, 26, 20251231, true),  // YY=25 < 26 → 2025
            (b"260101", yymmdd, 26, 19260101, true),  // YY=26 >= 26 → 1926
            (b"911214", yymmdd, 26, 19911214, true),  // YY=91 >= 26 → 1991
            (b"991231", yymmdd, 26, 19991231, true),  // YY=99 >= 26 → 1999
            (b"100812", yymmdd, 26, 20100812, true),  // YY=10 < 26 → 2010
            (b"911214", yymmdd, 26, 20171214, false), // wrong century
            // N = 0: window [1900, 2000). All YY → 19xx.
            (b"000101", yymmdd, 0, 19000101, true),
            (b"991231", yymmdd, 0, 19991231, true),
            // N = 99: window [1999, 2099). YY=99 → 1999, YY=0..98 → 20xx.
            (b"990101", yymmdd, 99, 19990101, true),
            (b"000101", yymmdd, 99, 20000101, true),
            (b"980101", yymmdd, 99, 20980101, true),
        ];
        test_vecs.iter().for_each(|(input, format, n, expected, must_pass)| {
            run::<F>(
                input,
                *expected,
                ParseTarget::DateShortYear(*format, *n),
                *must_pass,
            )
        });
    }
}

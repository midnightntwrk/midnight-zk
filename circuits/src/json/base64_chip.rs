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

//! This module contains the `Base64Chip`, which implements Base64 decoding
//! instructions.
//!
//! In particular, this chip will be used to decode credentials. As such, it is
//! assumed that the input data is signed by a trusted party and therefore it is
//! well formed. This means that the decoding instructions do not enforce the
//! validity of the base64 input (i.e. the padding format).
//!
//! The instructions ensure that inputs that agree with the base64 specification
//! decode correctly.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    instructions::{
        base64::{Base64VarInstructions, Base64Vec},
        ArithInstructions, AssignmentInstructions, Base64Instructions, ControlFlowInstructions,
        DecompositionInstructions, EqualityInstructions, RangeCheckInstructions, ZeroInstructions,
    },
    types::{AssignedByte, AssignedVector, InnerValue, VectorInstructions},
    utils::ComposableChip,
};

/// Number of advice columns in [Base64Chip].
pub const NB_BASE64_ADVICE_COLS: usize = 4;

#[derive(Clone, Debug)]
/// Config for Base64Chip.
pub struct Base64Config {
    advice_cols: [Column<Advice>; NB_BASE64_ADVICE_COLS],

    lookup_sel: Selector,
    // Base64 table.
    t_char: TableColumn,
    t_val: TableColumn,
}

// Native gadget type abbreviation.
type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

// Contains 4 Base64 characters as bytes.
type B64Chunk<F> = [AssignedByte<F>; 4];

// Contains 4 ASCII characters as bytes.
type AsciiChunk<F> = [AssignedByte<F>; 3];

// Table padding for the lookup. This is different from the base64 padding '='.
// It needs to agree with the value of ASCII_ZERO.
pub(crate) const ALT_PAD: char = super::table::BASE64_TABLE[0].0;

#[cfg(test)]
const ASCII_ZERO: char = super::table::BASE64_TABLE[0].1 as char;

const B64_PAD: char = '=';

#[derive(Debug, Clone)]
/// Base64Chip capable of decoding base64 encoded strings.
pub struct Base64Chip<F>
where
    F: PrimeField,
{
    config: Base64Config,
    native_gadget: NG<F>,
}

impl<F: PrimeField> Base64Instructions<F> for Base64Chip<F> {
    fn decode_base64url(
        &self,
        layouter: &mut impl Layouter<F>,
        b64url_input: &[AssignedByte<F>],
        padded: bool,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let standard_b64 = self.url_to_standard(layouter, b64url_input)?;
        self.decode_base64(layouter, &standard_b64, padded)
    }

    fn decode_base64(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &[AssignedByte<F>],
        padded: bool,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        debug_assert!(
            b64_input.len() % 4 == 0 || !padded,
            "If pad is selected, the Base64 encoded input length must be a multiple of 4."
        );
        let mut last_chunk: B64Chunk<F>;
        let mut result = Vec::with_capacity((b64_input.len() + 3) / 4 * 3); // +3 for rounding up.
        let mut chunk_iter = b64_input.chunks(4).peekable();
        while let Some(b64_chunk) = chunk_iter.next() {
            let chunk_array: &B64Chunk<F> = if chunk_iter.peek().is_none() {
                last_chunk = if padded {
                    self.process_padded_chunk(
                        layouter,
                        b64_chunk.try_into().expect("Chunk of length 4."),
                    )?
                } else {
                    self.pad(layouter, b64_chunk)?
                };
                &last_chunk
            } else {
                b64_chunk.try_into().expect("Chunk of length 4")
            };
            let values = self.base64_to_val_chunk(layouter, chunk_array)?;
            let ascii_result = self.val_to_ascii_chunk(layouter, &values)?;
            result.append(&mut ascii_result.to_vec())
        }

        Ok(result)
    }
}

impl<F: PrimeField, const M: usize, const A: usize> Base64VarInstructions<F, M, A>
    for Base64Chip<F>
{
    fn assign_var_base64(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<u8>>,
    ) -> Result<Base64Vec<F, M, A>, Error> {
        let ng = &self.native_gadget;

        let vec = ng.assign_with_filler(layouter, value.clone(), Some(ALT_PAD as u8))?;

        //  A base64 string length must be multiple of 4.
        let q = {
            let q = value.map(|v| {
                assert_eq!(v.len() % 4, 0);
                F::from(v.len() as u64 / 4)
            });
            ng.assign_lower_than_fixed(layouter, q, &((M / 4 + 1) as u128).into())?
        };

        let check = ng.linear_combination(
            layouter,
            &[(F::from(4u64), q), (-F::ONE, vec.len.clone())],
            F::ZERO,
        )?;
        ng.assert_zero(layouter, &check)?;

        Ok(Base64Vec(vec))
    }

    fn base64_from_vec(
        &self,
        layouter: &mut impl Layouter<F>,
        vec: &AssignedVector<F, AssignedByte<F>, M, A>,
    ) -> Result<Base64Vec<F, M, A>, Error> {
        let ng = &self.native_gadget;
        let filler = ng.assign_fixed(layouter, ALT_PAD as u8)?;
        let flags = ng.padding_flag(layouter, vec)?;
        let result = vec
            .buffer
            .iter()
            .zip(flags.iter())
            .map(|(elem, is_padding)| ng.select(layouter, is_padding, &filler, elem))
            .collect::<Result<Vec<_>, Error>>()?
            .try_into()
            .unwrap();
        Ok(Base64Vec(AssignedVector {
            buffer: result,
            len: vec.len.clone(),
        }))
    }

    fn var_decode_base64url<const M_OUT: usize, const A_OUT: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        b64url_input: &Base64Vec<F, M, A>,
    ) -> Result<AssignedVector<F, AssignedByte<F>, M_OUT, A_OUT>, Error> {
        let vec = self.url_to_standard(layouter, &b64url_input.0.buffer)?;

        let b64_input = Base64Vec::<F, M, A>(AssignedVector {
            buffer: vec.try_into().unwrap(),
            len: b64url_input.0.len.clone(),
        });

        self.var_decode_base64(layouter, &b64_input)
    }

    fn var_decode_base64<const M_OUT: usize, const A_OUT: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &Base64Vec<F, M, A>,
    ) -> Result<AssignedVector<F, AssignedByte<F>, M_OUT, A_OUT>, Error> {
        // Assert correct capacity.
        // This is critical! We are decoding the whole buffer, so we must
        // be certain that the actual data is correctly aligned.
        assert_eq!(A % 4, 0);
        assert_eq!(M * 3, M_OUT * 4);
        assert_eq!(A * 3, A_OUT * 4);

        // Compute and constrain new length.
        let three = F::from(3u64);
        let four = F::from(4u64);
        let len = &b64_input.0.len;

        let new_len: AssignedNative<F> = {
            let len_value = len.value().map(|&l| l * four.invert().unwrap() * three);
            self.native_gadget.assign(layouter, len_value)?
        };

        let check = self.native_gadget.linear_combination(
            layouter,
            &[(four, new_len.clone()), (-three, len.clone())],
            F::ZERO,
        )?;
        self.native_gadget.assert_zero(layouter, &check)?;

        // Compute decoded buffer.
        let out_buffer = self.decode_base64(layouter, &b64_input.0.buffer, true)?;

        Ok(AssignedVector::<_, _, M_OUT, A_OUT> {
            buffer: out_buffer.try_into().unwrap(),
            len: new_len,
        })
    }
}

impl<F: PrimeField> Base64Chip<F> {
    /// Converts a Base64URL encoded strig into a Base64 sstring.
    /// It does so by substituting '-' for '+' and '_' for '/',
    /// leaving the rest of characters unchanged.
    fn url_to_standard(
        &self,
        layouter: &mut impl Layouter<F>,
        b64url_input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let ng = &self.native_gadget;
        let plus: AssignedByte<F> = ng.assign_fixed(layouter, b'+')?;
        let slash = ng.assign_fixed(layouter, b'/')?;

        b64url_input
            .iter()
            .map(|char| {
                let is_hyphen = ng.is_equal_to_fixed(layouter, char, b'-')?;
                let char = self
                    .native_gadget
                    .select(layouter, &is_hyphen, &plus, char)?;

                let is_underscore = ng.is_equal_to_fixed(layouter, &char, b'_')?;

                self.native_gadget
                    .select(layouter, &is_underscore, &slash, &char)
            })
            .collect::<Result<Vec<_>, _>>()
    }

    /// Process the last chunk, which may have 0, 1 or 2 characters of padding.
    /// The padding characters, if present, are removed and substituted by
    /// ALT_PAD, the base_64 character that will result in the ASCII_ZERO
    /// character.
    fn process_padded_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &B64Chunk<F>,
    ) -> Result<B64Chunk<F>, Error> {
        let ng = &self.native_gadget;

        let pad = ng.assign_fixed(layouter, ALT_PAD as u8)?;
        let pad_in_3rd = ng.is_equal_to_fixed(layouter, &b64_input[2], B64_PAD as u8)?;
        let pad_in_4th = ng.is_equal_to_fixed(layouter, &b64_input[3], B64_PAD as u8)?;

        // When the first character of padding is detected, the next must be padding as
        // well. This disallows padddings such as '=A' or '=?'.
        ng.cond_assert_equal(layouter, &pad_in_3rd, &pad_in_3rd, &pad_in_4th)?;

        Ok([
            b64_input[0].clone(),
            b64_input[1].clone(),
            ng.select(layouter, &pad_in_3rd, &pad, &b64_input[2])?,
            ng.select(layouter, &pad_in_4th, &pad, &b64_input[3])?,
        ])
    }

    /// Receives an incomplete chunk and returns it filled with circuit padding
    /// until it reaches full chunk length: 4.
    fn pad(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &[AssignedByte<F>],
    ) -> Result<B64Chunk<F>, Error> {
        let ng = &self.native_gadget;
        let pad: AssignedByte<F> = ng.assign_fixed(layouter, ALT_PAD as u8)?;
        let mut res = b64_input.to_vec();
        res.resize(4, pad);
        Ok(res.try_into().unwrap())
    }

    /// Receives 2 12-bit values, where each value represents a pair base64
    /// characters. Returns a vector of 3 [AssignedByte] with each symbol
    /// values. These values are guaranteed to be in the range [0, 2^8).
    fn val_to_ascii_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &[AssignedNative<F>; 2],
    ) -> Result<AsciiChunk<F>, Error> {
        // Sum ( b64_input[i] * 6^i ) = Sum ( byte[i] * 8^i)
        let terms = vec![
            (F::from(1u64 << 12), b64_input[0].clone()),
            (F::ONE, b64_input[1].clone()),
        ];
        let total = self
            .native_gadget
            .linear_combination(layouter, terms.as_slice(), F::ZERO)?;

        let bytes = self
            .native_gadget
            .assigned_to_be_bytes(layouter, &total, Some(3))?;

        Ok(bytes.try_into().unwrap())
    }

    /// Receives 4 ascii characters as [AssignedByte] representing a base64
    /// string. Returns a 2 [AssignedNative] with the value of each pair.
    /// These values are guaranteed to be in the range [0, 2^12).
    fn base64_to_val_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &B64Chunk<F>,
    ) -> Result<[AssignedNative<F>; 2], Error> {
        let advice_cols = self.config.advice_cols;
        // |-----|-----|--------|
        // | A   | B   | 0x0001 |
        // |-----|-----|--------|
        // | C   | D   | 0x0203 |
        // |-----|-----|--------|
        let decoded = layouter.assign_region(
            || "Base64 chunk",
            |mut region| {
                let decoded_outs: Vec<Value<F>> = b64_input
                    .chunks_exact(2)
                    .map(|vs| {
                        vs[0].value().zip(vs[1].value()).map(|(c0, c1)| {
                            let v0 = super::table::decode_char(c0 as char) as u64;
                            let v1 = super::table::decode_char(c1 as char) as u64;
                            F::from(v0 * (1 << 6) + v1)
                        })
                    })
                    .collect();

                // Enable lookup selector in both rows.
                self.config.lookup_sel.enable(&mut region, 0)?;
                self.config.lookup_sel.enable(&mut region, 1)?;

                // Positions of the inputs as: (column, row)
                let positions = [
                    [(0, 0), (1, 0)], //
                    [(0, 1), (1, 1)],
                ];
                for (input, pos) in b64_input.iter().zip(positions.as_flattened()) {
                    let input: AssignedNative<F> = input.clone().into();
                    input.copy_advice(|| "Base64 char", &mut region, advice_cols[pos.0], pos.1)?;
                }

                let result: Result<Vec<_>, _> = decoded_outs
                    .into_iter()
                    .zip(positions)
                    .map(|(output, pos)| {
                        region.assign_advice(
                            || "Base64 decoded values",
                            advice_cols[pos[0].0 + 2], /* same position as inputs, just 2
                                                        * columns right */
                            pos[0].1,
                            || output,
                        )
                    })
                    .collect();
                result
            },
        )?;

        Ok(decoded.try_into().unwrap())
    }
}

impl<F: PrimeField> Chip<F> for Base64Chip<F> {
    type Config = Base64Config;

    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> ComposableChip<F> for Base64Chip<F> {
    type SharedResources = [Column<Advice>; NB_BASE64_ADVICE_COLS];
    type InstructionDeps = NG<F>;

    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: sub_chips.clone(),
        }
    }

    fn configure(
        meta: &mut midnight_proofs::plonk::ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config {
        let advice_cols = *shared_resources;
        let lookup_sel = meta.complex_selector();

        // Lookup table columns.
        let t_char = meta.lookup_table_column();
        let t_val = meta.lookup_table_column();

        meta.lookup("Base64 lookup", |meta| {
            let s = meta.query_selector(lookup_sel);

            // Each row decodes 2 characters. The first 2 columns contain
            // the characters. The third column contains their combined value as:
            //  char_1 * (2^6) + char_2
            //
            // |characters | value |
            // |-----|-----|-------|
            // | A   | B   | 0x01  |
            // |-----|-----|-------|

            let col_1 = meta.query_advice(advice_cols[0], Rotation::cur());
            let col_2 = meta.query_advice(advice_cols[1], Rotation::cur());
            let characters = col_1 * Expression::Constant(F::from(1 << 8)) + col_2;

            let value = meta.query_advice(advice_cols[2], Rotation::cur());

            // Default value for the deactivated lookup.
            let default_char = Expression::Constant(F::from(super::table::two_entry_default()));

            vec![
                (
                    s.clone() * characters
                        + (Expression::Constant(F::ONE) - s.clone()) * default_char,
                    t_char,
                ),
                (s.clone() * value, t_val),
            ]
        });
        Base64Config {
            advice_cols,
            lookup_sel,
            t_char,
            t_val,
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "Base64 table",
            |mut table| {
                for (offset, (char, val)) in super::table::two_entry_table().into_iter().enumerate()
                {
                    let char = Value::known(F::from(char as u64));
                    let val = Value::known(F::from(val as u64));
                    table.assign_cell(|| "t_char", self.config.t_char, offset, || char)?;
                    table.assign_cell(|| "t_val", self.config.t_val, offset, || val)?;
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;
    use crate::{
        field::decomposition::chip::P2RDecompositionConfig,
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
    };

    type Fp = blstrs::Fq;

    struct TestCircuit<F: PrimeField> {
        input: Vec<u8>,  // base64 encoded string
        output: Vec<u8>, // decoded string
        options: TestOptions,
        _marker: PhantomData<F>,
    }

    #[derive(Clone, Copy, Debug)]
    struct TestOptions {
        input_pad: bool,
        url_safe: bool,
        variable: bool,
    }

    impl<F: PrimeField> TestCircuit<F> {
        fn new(input: &[u8], output: &[u8], options: TestOptions) -> Self {
            debug_assert_eq!(input.len() % 4 == 0, options.input_pad);
            // Pad output to a multiple of 3.
            let mut padded_out = output.to_vec();

            match output.len() % 3 {
                2 => padded_out.append(&mut [ASCII_ZERO as u8].to_vec()),
                1 => padded_out.append(&mut [ASCII_ZERO as u8, ASCII_ZERO as u8].to_vec()),
                _ => (),
            }

            debug_assert_eq!((input.len() + 3) / 4 * 3, padded_out.len());
            Self {
                input: input.to_vec(),
                output: padded_out,
                options,
                _marker: PhantomData,
            }
        }
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
        type Config = (P2RDecompositionConfig, Base64Config);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                input: vec![],
                output: vec![],
                options: TestOptions {
                    input_pad: true,
                    url_safe: false,
                    variable: false,
                },
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let ng_config = NativeGadget::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            );
            let sr = &ng_config.native_config.value_cols[..NB_BASE64_ADVICE_COLS]
                .try_into()
                .unwrap();
            let b64_config = Base64Chip::configure(meta, sr);

            (ng_config, b64_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let options = &self.options;

            // Create chips.
            let ng: NG<F> = NativeGadget::new_from_scratch(&config.0);
            let b64_chip = Base64Chip::new(&config.1, &ng);

            // Load tables.
            NativeGadget::load_from_scratch(&mut layouter, &config.0);
            b64_chip.load(&mut layouter)?;

            if options.variable {
                // Variable length.
                let assigned_in_var: Base64Vec<F, 1024, 4> =
                    b64_chip.assign_var_base64(&mut layouter, Value::known(self.input.clone()))?;
                let ret_var: AssignedVector<F, AssignedByte<F>, 768, 3> = if options.url_safe {
                    b64_chip.var_decode_base64url(&mut layouter, &assigned_in_var)
                } else {
                    b64_chip.var_decode_base64(&mut layouter, &assigned_in_var)
                }?;
                ng.assert_equal_to_fixed(&mut layouter, &ret_var, self.output.clone())?;
            } else {
                // Fixed length.
                let input_vals: Vec<Value<u8>> =
                    self.input.clone().into_iter().map(Value::known).collect();

                let output_vals: Vec<Value<u8>> =
                    self.output.clone().into_iter().map(Value::known).collect();

                let assigned_in: Vec<AssignedByte<F>> =
                    ng.assign_many(&mut layouter, &input_vals)?;
                let assigned_out: Vec<AssignedByte<F>> =
                    ng.assign_many(&mut layouter, &output_vals)?;
                let ret = if options.url_safe {
                    b64_chip.decode_base64url(&mut layouter, &assigned_in, options.input_pad)?
                } else {
                    b64_chip.decode_base64(&mut layouter, &assigned_in, options.input_pad)?
                };
                assert_eq!(assigned_out.len(), ret.len());
                for (a, b) in assigned_out.iter().zip(ret.iter()) {
                    ng.assert_equal(&mut layouter, a, b)?;
                }
            }

            Ok(())
        }
    }

    #[test]
    fn test_b64chip() {
        let k = 13;

        let b64_input: &[u8] = b"QWxsIHRoYXQgaXMgZ29sZCBkb2VzIG5vdCBnbGl0dGVyLApOb3QgYWxsIHRob3NlIHdobyB3YW5kZXIgYXJlIGxvc3Q7ClRoZSBvbGQgdGhhdCBpcyBzdHJvbmcgZG9lcyBub3Qgd2l0aGVyLApEZWVwIHJvb3RzIGFyZSBub3QgcmVhY2hlZCBieSB0aGUgZnJvc3QuCiAtIEouUi5SLiBUb2xraWVuLCAxOTU0";
        #[rustfmt::skip]
        let output: &[u8] =
          b"All that is gold does not glitter,
Not all those who wander are lost;
The old that is strong does not wither,
Deep roots are not reached by the frost.
 - J.R.R. Tolkien, 1954";

        let options = TestOptions {
            input_pad: true,
            url_safe: false,
            variable: false,
        };

        let circuit = TestCircuit::<Fp>::new(b64_input, output, options);

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_urlsafe_b64chip() {
        let k = 13;

        let b64_input: &[u8] = b"VVJMU2FmZSB0ZXN0OiA_Pz8gPz8-Lg==";
        let output: &[u8] = b"URLSafe test: ??? ??>.";

        let options = TestOptions {
            input_pad: true,
            url_safe: true,
            variable: false,
        };

        let circuit = TestCircuit::<Fp>::new(b64_input, output, options);

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_b64chip_w_padding() {
        let k = 13;

        let b64_input: &[u8] = b"QWxsIHRoYXQgaXMgZ29sZCBkb2VzIG5vdCBnbGl0dGVyLA==";
        let b64_input_bad: &[u8] = b"QWxsIHRoYXQgaXMgZ29sZCBkb2VzIG5vdCBnbGl0dGVyLA=A";
        let output: &[u8] = b"All that is gold does not glitter,";

        let options = TestOptions {
            input_pad: true,
            url_safe: false,
            variable: false,
        };

        let circuit = TestCircuit::<Fp>::new(b64_input, output, options);
        let circuit_bad = TestCircuit::<Fp>::new(b64_input_bad, output, options);

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit_bad, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        assert!(prover.verify().is_err());
    }

    #[test]
    fn test_b64chip_truncated() {
        let k = 13;

        let b64_input: &[u8] = b"QWxsIHRoYXQgaXMgZ29sZCBkb2VzIG5vdCBnbGl0dGVyLA";
        let output: &[u8] = b"All that is gold does not glitter,";

        let options = TestOptions {
            input_pad: false,
            url_safe: false,
            variable: false,
        };
        let circuit = TestCircuit::<Fp>::new(b64_input, output, options);

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_b64chip_variable() {
        let k = 13;

        let b64_input: &[u8] = b"QWxsIHRoYXQgaXMgZ29sZCBkb2VzIG5vdCBnbGl0dGVyLApOb3QgYWxsIHRob3NlIHdobyB3YW5kZXIgYXJlIGxvc3Q7ClRoZSBvbGQgdGhhdCBpcyBzdHJvbmcgZG9lcyBub3Qgd2l0aGVyLApEZWVwIHJvb3RzIGFyZSBub3QgcmVhY2hlZCBieSB0aGUgZnJvc3QuCiAtIEouUi5SLiBUb2xraWVuLCAxOTU0";
        #[rustfmt::skip]
        let output: &[u8] =
          b"All that is gold does not glitter,
Not all those who wander are lost;
The old that is strong does not wither,
Deep roots are not reached by the frost.
 - J.R.R. Tolkien, 1954";

        let options = TestOptions {
            input_pad: true,
            url_safe: false,
            variable: true,
        };

        let circuit = TestCircuit::<Fp>::new(b64_input, output, options);

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_urlsafe_b64chip_variable() {
        let k = 14;

        let b64_input: &[u8] = b"VVJMU2FmZSB0ZXN0OiA_Pz8gPz8-Lg==";
        let output: &[u8] = b"URLSafe test: ??? ??>.";

        let options = TestOptions {
            input_pad: true,
            url_safe: true,
            variable: true,
        };

        let circuit = TestCircuit::<Fp>::new(b64_input, output, options);

        let public_inputs = vec![vec![], vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }
}

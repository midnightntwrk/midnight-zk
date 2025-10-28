//! Chip that implements base64 decoding instructions.

use ff::PrimeField;
use halo2_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    instructions::{
        ArithInstructions, AssignmentInstructions, ControlFlowInstructions,
        DecompositionInstructions, EqualityInstructions,
    },
    types::{AssignedByte, Byte, InnerValue},
    utils::ComposableChip,
};

#[derive(Clone, Debug)]
/// Config for Base64Chip.
pub struct Base64Config {
    advice_cols: [Column<Advice>; 4],

    lookup_sel: Selector,
    // Base64 table.
    t_char: TableColumn,
    t_val: TableColumn,
}

// Native gadget type abbreviation.
type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

type B64Chunk<F> = [AssignedByte<F>; 4];
type AsciiChunk<F> = [AssignedByte<F>; 3];

// Table padding for the lookup. This is different from the base64 padding '='.
// It needs to agree with the value of ASCII_ZERO.
const ALT_PAD: char = super::table::BASE64_TABLE[0].0;
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
        let plus: AssignedByte<F> = ng.assign_fixed(layouter, Byte(b'+'))?;
        let slash = ng.assign_fixed(layouter, Byte(b'/'))?;

        b64url_input
            .iter()
            .map(|char| {
                let is_hyphen = ng.is_equal_to_fixed(layouter, char, Byte(b'-'))?;
                let char = self
                    .native_gadget
                    .select(layouter, &is_hyphen, &plus, char)?;

                let is_underscore = ng.is_equal_to_fixed(layouter, &char, Byte(b'_'))?;

                self.native_gadget
                    .select(layouter, &is_underscore, &slash, &char)
            })
            .collect::<Result<Vec<_>, _>>()
    }

    /// Receives a base64 url-safe encoded string as [AssignedByte]s and returns
    /// the decoded ascii string as a vector of [AssignedByte].
    /// The length of the output is 3/4 of the input's length.
    /// If pad is selected, the input length must be a multiple of 4.
    /// Output will be completed with one or two ASCII_ZERO chars if necessary.
    pub fn from_base64url(
        &self,
        layouter: &mut impl Layouter<F>,
        b64url_input: &[AssignedByte<F>],
        pad: bool,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let standard_b64 = self.url_to_standard(layouter, b64url_input)?;
        self.from_base64(layouter, &standard_b64, pad)
    }
    /// Receives a base64 encoded string as [AssignedByte]s and returns
    /// the decoded ascii string as a vector of [AssignedByte].
    /// The length of the output is 3/4 of the input's length.
    /// If pad is selected, the input length must be a multiple of 4.
    /// Output will be completed with one or two ASCII_ZERO chars if necessary.
    pub fn from_base64(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &[AssignedByte<F>],
        pad: bool,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        debug_assert!(
            b64_input.len() % 4 == 0 || !pad,
            "If pad is selected, the Base64 encoded input length must be a multiple of 4."
        );
        let mut last_chunk: B64Chunk<F>;
        let mut result = Vec::with_capacity((b64_input.len() + 3) / 4 * 3); // +3 for rounding up.
        let mut chunk_iter = b64_input.chunks(4).peekable();
        while let Some(b64_chunk) = chunk_iter.next() {
            let chunk_array: &B64Chunk<F> = if chunk_iter.peek().is_none() {
                last_chunk = if pad {
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

        let pad = ng.assign_fixed(layouter, Byte(ALT_PAD as u8))?;
        let pad_in_3rd = ng.is_equal_to_fixed(layouter, &b64_input[2], Byte(B64_PAD as u8))?;
        let pad_in_4th = ng.is_equal_to_fixed(layouter, &b64_input[3], Byte(B64_PAD as u8))?;

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
        let pad: AssignedByte<F> = ng.assign_fixed(layouter, Byte(ALT_PAD as u8))?;
        let mut res = b64_input.to_vec();
        res.resize(4, pad);
        Ok(res.try_into().unwrap())
    }

    /// Receives 4 6-bit values, corresponding to a string of 4 base64
    /// characters. Returns a vector of 3 [AssignedByte] with each symbol
    /// values. These values are guaranteed to be in the range [0, 2^8).
    fn val_to_ascii_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &[AssignedNative<F>; 4],
    ) -> Result<AsciiChunk<F>, Error> {
        // Sum ( b64_input[i] * 6^i ) = Sum ( byte[i] * 8^i)
        let terms = vec![
            (F::from(1u64 << (3 * 6)), b64_input[0].clone()),
            (F::from(1u64 << (2 * 6)), b64_input[1].clone()),
            (F::from(1u64 << 6), b64_input[2].clone()),
            (F::ONE, b64_input[3].clone()),
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
    /// string. Returns a vector of 4 [AssignedNative] with each symbol
    /// values. These values are guaranteed to be in the range [0, 2^6).
    fn base64_to_val_chunk(
        &self,
        layouter: &mut impl Layouter<F>,
        b64_input: &B64Chunk<F>,
    ) -> Result<[AssignedNative<F>; 4], Error> {
        let advice_cols = self.config.advice_cols;
        // |-----|-----|-----|-----|
        // | A   | B   |0x00 |0x01 |
        // |-----|-----|-----|-----|
        // | C   | D   |0x02 |0x03 |
        // |-----|-----|-----|-----|
        let decoded = layouter.assign_region(
            || "Base64 chunk",
            |mut region| {
                let decoded_outs: Vec<_> = b64_input
                    .iter()
                    .map(|a| {
                        a.value().map(|v| {
                            // Hope there is a cleaner way to do this.
                            // Byte implements Deref to get &u8.
                            let value: &u8 = &v;
                            let decoded = super::table::decode_char(*value as char);
                            F::from(decoded as u64)
                        })
                    })
                    .collect();

                // Enable lookup selector in both rows.
                self.config.lookup_sel.enable(&mut region, 0)?;
                self.config.lookup_sel.enable(&mut region, 1)?;

                // Positions of the inputs as: (column, row)
                let positions = [(0, 0), (1, 0), (0, 1), (1, 1)];
                for (input, pos) in b64_input.iter().zip(positions.iter()) {
                    // Need to transform into native first due to the restrictions on
                    // the `copied()` method that is needed to transform `Value<&V> -> Value<V>`.
                    let input: AssignedNative<F> = input.clone().into();
                    input.copy_advice(|| "Base64 char", &mut region, advice_cols[pos.0], pos.1)?;
                }

                let mut result = vec![];
                for (output, pos) in decoded_outs.into_iter().zip(positions.iter()) {
                    let assigned = region.assign_advice(
                        || "Base64 decoded values",
                        advice_cols[pos.0 + 2], // same position as inputs, just 2 columns right
                        pos.1,
                        || output,
                    )?;
                    result.push(assigned);
                }

                Ok(result)
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
    type SharedResources = [Column<Advice>; 4];
    type InstructionDeps = NG<F>;

    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: sub_chips.clone(),
        }
    }

    fn configure(
        meta: &mut halo2_proofs::plonk::ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config {
        let advice_cols = *shared_resources;
        let lookup_sel = meta.complex_selector();

        // Lookup table columns.
        let t_char = meta.lookup_table_column();
        let t_val = meta.lookup_table_column();

        meta.lookup("Base64 lookup", |meta| {
            let s = meta.query_selector(lookup_sel);

            // Each row decodes 2 characters.
            // 1st column decoding is placed in the 3rd column,
            // 2nd column decoding is placed in the 4th column.

            // |characters | values    |
            // |-----|-----|-----|-----|
            // | A   | B   |0x00 |0x01 |
            // |-----|-----|-----|-----|

            // characters = first_col * 8 + second_col
            let col_1 = meta.query_advice(advice_cols[0], Rotation::cur());
            let col_2 = meta.query_advice(advice_cols[1], Rotation::cur());
            let characters = col_1 * Expression::Constant(F::from(1 << 8)) + col_2;

            // values = third_col * 6 + fourth_col
            let col_3 = meta.query_advice(advice_cols[2], Rotation::cur());
            let col_4 = meta.query_advice(advice_cols[3], Rotation::cur());
            let values = col_3 * Expression::Constant(F::from(1 << 6)) + col_4;

            // default value for the deactivated lookup
            let default_char = Expression::Constant(F::from(super::table::two_entry_default()));

            vec![
                (
                    s.clone() * characters
                        + (Expression::Constant(F::ONE) - s.clone()) * default_char,
                    t_char,
                ),
                (s.clone() * values, t_val),
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

    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;
    use crate::{
        field::decomposition::chip::P2RDecompositionConfig,
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        types::Byte,
    };

    type Fp = blstrs::Scalar;

    struct TestCircuit<F: PrimeField> {
        input: Vec<u8>,  // base64 encoded string
        output: Vec<u8>, // decoded string
        input_pad: bool,
        url_safe: bool,
        _marker: PhantomData<F>,
    }
    impl<F: PrimeField> TestCircuit<F> {
        fn new(input: &[u8], output: &[u8], input_pad: bool, url_safe: bool) -> Self {
            debug_assert_eq!(input.len() % 4 == 0, input_pad);
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
                input_pad,
                url_safe,
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
                input_pad: true,
                url_safe: false,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_column = meta.instance_column();
            let ng_config = NativeGadget::configure_from_scratch(meta, &instance_column);
            let sr = &ng_config.native_config.value_cols[..4].try_into().unwrap();
            let b64_config = Base64Chip::configure(meta, sr);

            (ng_config, b64_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // Create chips.
            let ng: NG<F> = NativeGadget::new_from_scratch(&config.0);
            let b64_chip = Base64Chip::new(&config.1, &ng);

            // Load tables.
            NativeGadget::load_from_scratch(&mut layouter, &config.0);
            b64_chip.load(&mut layouter)?;

            let input_vals: Vec<Value<Byte>> = self
                .input
                .clone()
                .into_iter()
                .map(Byte)
                .map(Value::known)
                .collect();

            let output_vals: Vec<Value<Byte>> = self
                .output
                .clone()
                .into_iter()
                .map(Byte)
                .map(Value::known)
                .collect();

            let assigned_in: Vec<AssignedByte<F>> = ng.assign_many(&mut layouter, &input_vals)?;
            let assigned_out: Vec<AssignedByte<F>> = ng.assign_many(&mut layouter, &output_vals)?;

            let ret = if self.url_safe {
                b64_chip.from_base64url(&mut layouter, &assigned_in, self.input_pad)?
            } else {
                b64_chip.from_base64(&mut layouter, &assigned_in, self.input_pad)?
            };

            assert_eq!(assigned_out.len(), ret.len());
            for (a, b) in assigned_out.iter().zip(ret.iter()) {
                ng.assert_equal(&mut layouter, a, b)?;
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

        let circuit = TestCircuit::<Fp>::new(b64_input, output, true, false);

        let public_inputs = vec![vec![]];
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

        let circuit = TestCircuit::<Fp>::new(b64_input, output, true, true);

        let public_inputs = vec![vec![]];
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
        let output: &[u8] = b"All that is gold does not glitter,";

        let circuit = TestCircuit::<Fp>::new(b64_input, output, true, false);

        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_b64chip_truncated() {
        let k = 13;

        let b64_input: &[u8] = b"QWxsIHRoYXQgaXMgZ29sZCBkb2VzIG5vdCBnbGl0dGVyLA";
        let output: &[u8] = b"All that is gold does not glitter,";

        let circuit = TestCircuit::<Fp>::new(b64_input, output, false, false);

        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        assert_eq!(prover.verify(), Ok(()));
    }
}

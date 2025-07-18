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

//! Decomposition instructions interface.
//!
//! It provides functions for decomposing assigned values into bits or bytes,
//! but also composing bits or bytes into assigned values.
//!
//! This trait is parametrized by the `Assigned` type (a generic of this trait
//! that implements [InnerValue](crate::types::InnerValue)) that is being
//! decomposed/composed.

use std::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    instructions::{ArithInstructions, CanonicityInstructions, ConversionInstructions},
    types::{AssignedBit, AssignedByte, AssignedNative, InnerConstants, Instantiable},
};

/// The set of circuit instructions for (de)composition operations.
pub trait DecompositionInstructions<F, Assigned>:
    CanonicityInstructions<F, Assigned>
    + ArithInstructions<F, Assigned>
    + ConversionInstructions<F, AssignedBit<F>, Assigned>
    + ConversionInstructions<F, AssignedByte<F>, Assigned>
where
    F: PrimeField,
    Assigned::Element: PrimeField,
    Assigned: Instantiable<F> + InnerConstants + Clone,
{
    /// Returns a vector of assigned bits representing the given assigned
    /// element in little-endian.
    ///
    /// The number of bits (the length of the resulting vector) can be
    /// specified. If unspecified, the resulting vector will contain exactly
    /// `Self::Assigned::Element::NUM_BITS` bits (the minimum number of bits
    /// necessary to represent any element).
    ///
    /// If `enforce_canonical = true`, the output will be enforced to be in
    /// **canonical form**, i.e. the underlying system of constraints can
    /// only be satisfied by a single bit (bool) vector.
    /// If `enforce_canonical = false`, the output `{b_i}_i` is only restricted
    /// to satisfy: `x = sum_i 2^i b_i`, which may be satisfiable by more than
    /// one bit vector.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(5)))?;
    /// let bits = chip.assigned_to_le_bits(&mut layouter, &x, Some(4), true)?;
    ///
    /// // 5 is decomposed as 1010 in little-endian.
    /// assert_eq!(bits.len(), 4);
    /// chip.assert_equal_to_fixed(&mut layouter, &bits[0], true)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bits[1], false)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bits[2], true)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bits[3], false)?;
    /// # });
    /// ```
    ///
    /// # Panics
    ///
    /// If `x` cannot be decomposed in `nb_bits` bits (when this argument is
    /// specified), the circuit will become unsatisfiable.
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(16)))?;
    /// let bits = chip.assigned_to_le_bits(&mut layouter, &x, Some(4), true)?;
    /// # });
    /// ```
    fn assigned_to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error>;

    /// Same as [assigned_to_le_bits](Self::assigned_to_le_bits) but the output
    /// bits are given in big-endian.
    fn assigned_to_be_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        let mut bits = self.assigned_to_le_bits(layouter, x, nb_bits, enforce_canonical)?;
        bits.reverse();
        Ok(bits)
    }

    /// Returns a vector of assigned bytes representing the given element
    /// in little-endian.
    ///
    /// The output is enforced to be in **canonical form**, that is, there
    /// exists a single u8 vector that satisfies the underlying system of
    /// constraints.
    ///
    /// The number of bytes (the length of the resulting vector) can be
    /// specified. If unspecified, the resulting vector will contain exactly
    /// `ceil(Self::Assigned::Element::NUM_BITS / 8)` bytes (the minimum number
    /// of bytes necessary to represent any element).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(0x12345678)))?;
    /// let bytes = chip.assigned_to_le_bytes(&mut layouter, &x, Some(5))?;
    ///
    /// assert_eq!(bytes.len(), 5);
    /// chip.assert_equal_to_fixed(&mut layouter, &bytes[0], 0x78)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bytes[1], 0x56)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bytes[2], 0x34)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bytes[3], 0x12)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &bytes[4], 0x00)?;
    /// # });
    /// ```
    ///
    /// # Panics
    ///
    /// If `x` cannot be decomposed in `nb_bytes` bytes (when this argument is
    /// specified), the circuit will become unsatisfiable.
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(256)))?;
    /// let bytes = chip.assigned_to_le_bytes(&mut layouter, &x, Some(1))?;
    /// # });
    /// ```
    fn assigned_to_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error>;

    /// Same as [assigned_to_le_bytes](Self::assigned_to_le_bytes) but the
    /// output bytes are given in big-endian.
    fn assigned_to_be_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let mut bytes = self.assigned_to_le_bytes(layouter, x, nb_bytes)?;
        bytes.reverse();
        Ok(bytes)
    }

    /// Returns the element represented by the given vector of assigned bits,
    /// by interpreting it as a little-endian bit encoding.
    ///
    /// The number of input bits can be arbitrary.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let b0 = chip.assign(&mut layouter, Value::known(false))?;
    /// let b1 = chip.assign(&mut layouter, Value::known(true))?;
    /// let b2 = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let x = chip.assigned_from_le_bits(&mut layouter, &[b0, b1, b2])?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x, F::from(6))?;
    /// # });
    /// ```
    fn assigned_from_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<Assigned, Error> {
        let mut coeff = Assigned::Element::from(1);
        let mut terms = vec![];
        for b in bits {
            let b_as_element: Assigned = self.convert(layouter, b)?;
            terms.push((coeff, b_as_element));
            coeff = coeff + coeff; // double the coeff
        }
        let terms = terms
            .iter()
            .map(|(c, b)| (*c, b.clone()))
            .collect::<Vec<_>>();
        self.linear_combination(layouter, &terms, Assigned::Element::from(0))
    }

    /// Same as [assigned_from_le_bits](Self::assigned_from_le_bits) but the
    /// output bits are given in big-endian.
    fn assigned_from_be_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<Assigned, Error> {
        let mut bits = bits.to_vec();
        bits.reverse();
        self.assigned_from_le_bits(layouter, &bits)
    }

    /// Returns the element represented by the given vector of assigned bytes,
    /// by interpreting it in little-endian.
    ///
    /// For example, the sequence of bytes `[0x12, 0x34, 0x56, 0x78]`
    /// will be converted into an element encoding value `0x78563412`.
    ///
    /// The number of input bytes can be arbitrary.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let b0 = chip.assign(&mut layouter, Value::known(0x12))?;
    /// let b1 = chip.assign(&mut layouter, Value::known(0x34))?;
    /// let b2 = chip.assign(&mut layouter, Value::known(0x56))?;
    /// let b3 = chip.assign(&mut layouter, Value::known(0x78))?;
    ///
    /// let x = chip.assigned_from_le_bytes(&mut layouter, &[b0, b1, b2, b3])?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x, F::from(0x78563412))?;
    /// # });
    /// ```
    fn assigned_from_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<Assigned, Error> {
        let mut coeff = Assigned::Element::from(1);
        let mut terms = vec![];
        for byte in bytes {
            let byte_as_element: Assigned = self.convert(layouter, byte)?;
            terms.push((coeff, byte_as_element));
            coeff = Assigned::Element::from(256) * coeff; // scale the coeff
        }
        let terms = terms
            .iter()
            .map(|(c, b)| (*c, b.clone()))
            .collect::<Vec<_>>();
        self.linear_combination(layouter, &terms, Assigned::Element::from(0))
    }

    /// Same as [assigned_from_le_bytes](Self::assigned_from_le_bytes) but the
    /// output bytes are given in big-endian.
    fn assigned_from_be_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<Assigned, Error> {
        let mut bytes = bytes.to_vec();
        bytes.reverse();
        self.assigned_from_le_bytes(layouter, &bytes)
    }

    /// Returns a vector of [AssignedNative] values representing the given
    /// element in little-endian.
    /// The output length may be specified, in which case this function will be
    /// imposing an upper bound on the value of `x`.
    ///
    /// This vector is NOT guaranteed to be canonical, but it is guaranteed to
    /// satisfy: `x = sum_i 2^{i * nb_bits_per_chunk} * chunks_i`,
    /// when interpreting `chunks_i` as `Assigned` values instead of
    /// [AssignedNative] values. Note that this is possible because
    /// `Assigned::Element : PrimeField`.
    ///
    /// # Panics
    ///
    /// When `nb_chunks` is specified, if `x` cannot be decomposed in
    /// `nb_chunks` chunks of `nb_bits_per_chunk` size, the circuit becomes
    /// unsatisfiable.
    ///
    /// This function will panic if `nb_bits_per_chunk >= F::NUM_BITS`.
    fn assigned_to_le_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        nb_bits_per_chunk: usize,
        nb_chunks: Option<usize>,
    ) -> Result<Vec<AssignedNative<F>>, Error>;

    /// Sign function as described in RFC 9380. `sgn0(x) := x mod 2`.
    fn sgn0(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<AssignedBit<F>, Error> {
        let bits = self.assigned_to_le_bits(layouter, x, None, true)?;
        Ok(bits[0].clone())
    }
}

/// Pow2Range range-check instructions.
pub trait Pow2RangeInstructions<F: PrimeField>: Debug + Clone {
    /// Asserts that all the given assigned values in the range `[0, 2^n)`.
    fn assert_values_lower_than_2_pow_n(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[AssignedNative<F>],
        n: usize,
    ) -> Result<(), Error>;
}

#[cfg(test)]
#[allow(missing_docs)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::{Field, FromUniformBytes};
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use num_bigint::BigUint;
    use num_traits::One;
    use rand::{RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        types::InnerValue,
        utils::{
            circuit_modeling::circuit_to_json,
            util::{big_to_fe, fe_to_big, modulus},
        },
    };

    #[derive(Clone, Debug)]
    enum Endianess {
        LE,
        BE,
    }

    #[derive(Clone, Debug)]
    enum Operation {
        ToBits,
        ToBytes,
        FromBits,
        FromBytes,
        Sgn0,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, DecompChip, AuxChip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        decomposed: Vec<u8>,
        nb_parts: Option<usize>,
        endianess: Endianess,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, DecompChip, AuxChip)>,
    }

    impl<F, Assigned, DecompChip, AuxChip> Circuit<F> for TestCircuit<F, Assigned, DecompChip, AuxChip>
    where
        F: PrimeField,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        DecompChip: DecompositionInstructions<F, Assigned> + FromScratch<F>,
        AuxChip: AssertionInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedByte<F>>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, AssignedByte<F>>
            + FromScratch<F>,
    {
        type Config = (
            <DecompChip as FromScratch<F>>::Config,
            <AuxChip as FromScratch<F>>::Config,
        );
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let instance_columns = [committed_instance_column, instance_column];
            (
                DecompChip::configure_from_scratch(meta, &instance_columns),
                AuxChip::configure_from_scratch(meta, &instance_columns),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = DecompChip::new_from_scratch(&config.0);
            DecompChip::load_from_scratch(&mut layouter, &config.0);

            let aux_chip = AuxChip::new_from_scratch(&config.1);
            AuxChip::load_from_scratch(&mut layouter, &config.1);

            use Endianess::*;
            match self.operation {
                Operation::ToBits => {
                    let x: Assigned = chip.assign_fixed(&mut layouter, self.x)?;
                    let nb_bits = self.nb_parts;
                    let bits = match self.endianess {
                        LE => chip.assigned_to_le_bits(&mut layouter, &x, nb_bits, true),
                        BE => chip.assigned_to_be_bits(&mut layouter, &x, nb_bits, true),
                    }?;
                    assert_eq!(bits.len(), self.decomposed.len());
                    bits.iter()
                        .zip(self.decomposed.iter())
                        .try_for_each(|(bit, expected)| {
                            aux_chip.assert_equal_to_fixed(&mut layouter, bit, *expected == 1)
                        })
                }
                Operation::ToBytes => {
                    let x: Assigned = chip.assign_fixed(&mut layouter, self.x)?;
                    let nb_bytes = self.nb_parts;
                    let bytes = match self.endianess {
                        LE => chip.assigned_to_le_bytes(&mut layouter, &x, nb_bytes),
                        BE => chip.assigned_to_be_bytes(&mut layouter, &x, nb_bytes),
                    }?;
                    bytes
                        .iter()
                        .zip(self.decomposed.iter())
                        .try_for_each(|(bit, expected)| {
                            aux_chip.assert_equal_to_fixed(&mut layouter, bit, *expected)
                        })
                }
                Operation::FromBits => {
                    let bits = self
                        .decomposed
                        .iter()
                        .map(|b| chip.assign_fixed(&mut layouter, *b == 1))
                        .collect::<Result<Vec<_>, Error>>()?;
                    let x = match self.endianess {
                        LE => chip.assigned_from_le_bits(&mut layouter, &bits),
                        BE => chip.assigned_from_be_bits(&mut layouter, &bits),
                    }?;
                    chip.assert_equal_to_fixed(&mut layouter, &x, self.x)
                }
                Operation::FromBytes => {
                    let bytes = self
                        .decomposed
                        .iter()
                        .map(|byte| aux_chip.assign_fixed(&mut layouter, *byte))
                        .collect::<Result<Vec<_>, Error>>()?;
                    let x = match self.endianess {
                        LE => chip.assigned_from_le_bytes(&mut layouter, &bytes),
                        BE => chip.assigned_from_be_bytes(&mut layouter, &bytes),
                    }?;
                    chip.assert_equal_to_fixed(&mut layouter, &x, self.x)
                }
                Operation::Sgn0 => {
                    // Handle 0.
                    let decomposed = if self.decomposed.is_empty() {
                        &vec![0u8]
                    } else {
                        &self.decomposed
                    };
                    let x: Assigned = chip.assign_fixed(&mut layouter, self.x)?;
                    let sign = chip.sgn0(&mut layouter, &x)?;
                    let lsb = match self.endianess {
                        LE => decomposed[0] & 1,
                        BE => decomposed.last().unwrap() & 1,
                    };
                    aux_chip.assert_equal_to_fixed(&mut layouter, &sign, lsb == 1u8)
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, DecompChip, AuxChip>(
        x: Assigned::Element,
        decomposed: &[u8],
        nb_parts: Option<usize>,
        endianess: Endianess,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        DecompChip: DecompositionInstructions<F, Assigned> + FromScratch<F>,
        AuxChip: AssertionInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedByte<F>>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, AssignedByte<F>>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, DecompChip, AuxChip> {
            x,
            decomposed: decomposed.to_vec(),
            nb_parts,
            endianess,
            operation,
            _marker: PhantomData,
        };
        let log2_nb_rows = 10;
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, op_name, 0, circuit);
        }
    }

    /// The output type is u8 instead of bool because, for readability, we
    /// express the test vectors with integers `0` and `1` instead of
    /// `false` and `true` (respectively).
    fn biguint_to_bits(n: &BigUint) -> Vec<u8> {
        (0..(n.bits() as usize))
            .map(|i| if n.bit(i as u64) { 1 } else { 0 })
            .collect()
    }

    fn biguint_to_bytes(n: &BigUint) -> Vec<u8> {
        biguint_to_bits(n)
            .chunks(8)
            .map(|chunk| chunk.iter().enumerate().map(|(i, bi)| (1 << i) * bi).sum())
            .collect()
    }

    macro_rules! parse {
        ($n:expr) => {
            Assigned::Element::from($n)
        };
    }

    pub fn test_bit_decomposition<F, Assigned, DecompChip, AuxChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        DecompChip: DecompositionInstructions<F, Assigned> + FromScratch<F>,
        AuxChip: AssertionInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedByte<F>>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, AssignedByte<F>>
            + FromScratch<F>,
    {
        use Endianess::*;
        use Operation::*;
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u64();
        let mut bits_of_r = biguint_to_bits(&r.into());
        bits_of_r.resize(64, 0);
        let m = modulus::<Assigned::Element>();
        let m_minus_1 = m.clone() - BigUint::one();
        let mut cost_model = true;
        [
            // These test vectors are designed in little-endian
            (parse!(r), bits_of_r, Some(64), true, true),
            (parse!(0), biguint_to_bits(&m), None, false, true),
            (-parse!(1), biguint_to_bits(&m_minus_1), None, true, true),
            (parse!(0), vec![], Some(0), true, true),
            (parse!(0), vec![0], Some(1), true, true),
            (parse!(1), vec![1], Some(1), true, true),
            (parse!(3), vec![1, 1, 0, 0, 0], Some(5), true, true),
            (parse!(3), vec![0, 0, 0, 1, 1], Some(5), false, false),
        ]
        .iter()
        .for_each(|(x, bits, nb_bits, ok_to, ok_from)| {
            let mut rev = bits.clone();
            rev.reverse();
            run::<F, Assigned, DecompChip, AuxChip>(
                *x, bits, *nb_bits, LE, ToBits, *ok_to, cost_model, name, "to_bits",
            );
            run::<F, Assigned, DecompChip, AuxChip>(
                *x,
                bits,
                None,
                LE,
                FromBits,
                *ok_from,
                cost_model,
                name,
                "from_bits",
            );
            cost_model = false;
            run::<F, Assigned, DecompChip, AuxChip>(
                *x, &rev, *nb_bits, BE, ToBits, *ok_to, false, "", "",
            );
            run::<F, Assigned, DecompChip, AuxChip>(
                *x, &rev, None, BE, FromBits, *ok_from, false, "", "",
            );
        });
    }

    pub fn test_byte_decomposition<F, Assigned, DecompChip, AuxChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        DecompChip: DecompositionInstructions<F, Assigned> + FromScratch<F>,
        AuxChip: AssertionInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedByte<F>>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, AssignedByte<F>>
            + FromScratch<F>,
    {
        use Endianess::*;
        use Operation::*;

        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u64();
        let mut bytes_of_r = biguint_to_bytes(&r.into());
        bytes_of_r.resize(8, 0);
        let m = modulus::<Assigned::Element>();
        let m_minus_1 = m.clone() - BigUint::one();
        let mut cost_model = true;
        [
            // These test vectors are designed in little-endian
            (parse!(r), bytes_of_r, Some(8), true, true),
            (parse!(0), biguint_to_bytes(&m), None, false, true),
            (-parse!(1), biguint_to_bytes(&m_minus_1), None, true, true),
            (parse!(0), vec![], Some(0), true, true),
            (parse!(255), vec![255, 0], Some(2), true, true),
            (parse!(256), vec![0, 1], Some(2), true, true),
            (parse!(256), vec![1, 0], Some(2), false, false),
            (
                parse!(0x12345678),
                vec![0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00],
                Some(7),
                true,
                true,
            ),
        ]
        .iter()
        .for_each(|(x, bytes, nb_bytes, ok_to, ok_from)| {
            let mut rev = bytes.clone();
            rev.reverse();
            run::<F, Assigned, DecompChip, AuxChip>(
                *x, bytes, *nb_bytes, LE, ToBytes, *ok_to, cost_model, name, "to_bytes",
            );
            run::<F, Assigned, DecompChip, AuxChip>(
                *x,
                bytes,
                None,
                LE,
                FromBytes,
                *ok_from,
                cost_model,
                name,
                "from_bytes",
            );
            cost_model = false;
            run::<F, Assigned, DecompChip, AuxChip>(
                *x, &rev, *nb_bytes, BE, ToBytes, *ok_to, false, "", "",
            );
            run::<F, Assigned, DecompChip, AuxChip>(
                *x, &rev, None, BE, FromBytes, *ok_from, false, "", "",
            );
        });
    }

    pub fn test_sgn0<F, Assigned, DecompChip, AuxChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        DecompChip: DecompositionInstructions<F, Assigned> + FromScratch<F>,
        AuxChip: AssertionInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedByte<F>>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, AssignedByte<F>>
            + FromScratch<F>,
    {
        // Random test cases.
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let random_test_cases: Vec<_> = (0..100)
            .map(|_| Assigned::Element::random(&mut rng))
            .collect();

        // Edge case where x = 0 | p_mid | 1.
        // (same as the modulus p but with the msb turned to 0).
        let mut p = modulus::<Assigned::Element>();
        p.set_bit(F::NUM_BITS as u64 - 1, false);
        let x = big_to_fe(p.clone());

        let edge_cases = &[
            parse!(0),
            parse!(1),
            x,
            big_to_fe(modulus::<Assigned::Element>() - BigUint::one()),
        ];

        let test_cases = &[random_test_cases.as_slice(), edge_cases].concat();

        test_cases.iter().enumerate().for_each(|(i, x)| {
            let bytes = biguint_to_bytes(&fe_to_big(*x));
            run::<F, Assigned, DecompChip, AuxChip>(
                *x,
                &bytes,
                None,
                Endianess::LE,
                Operation::Sgn0,
                true,
                i == 0, // Cost model on for the first example.
                name,
                "sgn0",
            );
        })
    }
}

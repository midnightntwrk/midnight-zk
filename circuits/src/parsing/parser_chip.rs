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

use std::{cell::RefCell, cmp::min, marker::PhantomData, rc::Rc};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use num_bigint::BigUint;
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance};

use crate::{
    field::AssignedNative, instructions::NativeInstructions, types::AssignedByte,
    utils::ComposableChip,
};

/// Number of advice columns required for substring functionality.
pub const NB_SUBSTRING_ADVICE_COLS: usize = 2;

/// Configuration for substring checking via dynamic lookups.
#[derive(Clone, Debug)]
pub struct SubstringConfig {
    /// Selector for substring lookup checks.
    q_substring: Selector,
    /// Fixed column for tags to isolate different `check_bytes` calls. For
    /// soundness reasons, this column cannot be shared (elements have to be 0
    /// in rows unrelated to `check_bytes` calls).
    tag_col: Column<Fixed>,
    /// Advice column for indices.
    index_col: Column<Advice>,
    /// Advice column for byte values.
    byte_col: Column<Advice>,
}

#[derive(Clone, Debug)]
/// A chip for parsing data. It is parametrized by:
///  - F: the native field,
///  - N: a set of in-circuit native instructions.
pub struct ParserChip<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    pub(crate) native_gadget: N,
    config: SubstringConfig,
    /// Counter for generating unique positive tags for each `check_bytes` call.
    substring_tag_counter: Rc<RefCell<u64>>,
    _marker: PhantomData<F>,
}

impl<F, N> Chip<F> for ParserChip<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F> + Clone,
{
    type Config = SubstringConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F, N> ComposableChip<F> for ParserChip<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F> + Clone,
{
    type InstructionDeps = N;
    type SharedResources = [Column<Advice>; NB_SUBSTRING_ADVICE_COLS];

    fn new(config: &SubstringConfig, deps: &N) -> Self {
        Self {
            native_gadget: deps.clone(),
            config: config.clone(),
            substring_tag_counter: Rc::new(RefCell::new(1)),
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice_cols: &[Column<Advice>; NB_SUBSTRING_ADVICE_COLS],
    ) -> SubstringConfig {
        let q_substring = meta.complex_selector();
        // Tag column that identify each function calls to this lookup table (see the
        // field `substring_tag_counter` of `ParserChip`). For soundness, it is required
        // that:
        // 1. each function call gets a fresh tag that is never 0
        // 2. this column is 0 outside check_bytes regions. Therefore, this column
        //    cannot be shared.
        let tag_col = meta.fixed_column();
        let index_col = advice_cols[0];
        let byte_col = advice_cols[1];

        meta.enable_equality(index_col);
        meta.enable_equality(byte_col);

        // Dynamic lookup for substring checking. This is a self-referential lookup
        // where we look up (tag, index, byte) triples from the same columns, similarly
        // to the ECC chip. Key correctness arguments:
        // 1. Rows where the selector is deactivated (0) induce triples (teg, index,
        //    byte) that are automatically matched in the table.
        // 2. Rows where the selector is activated (1) induce triples (teg, index, byte)
        //    that need to be matched by at least one triple in a row where the selector
        //    is 0.
        // 3. The tag is 0 iff the row is not used for an actual substring check. It
        //    avoids that the triple (0,0,0) is unsoundly matched (always in the table
        //    due to rows where the selector is 0).
        meta.lookup_any("substring lookup", |meta| {
            let sel = meta.query_selector(q_substring);
            let not_sel = Expression::Constant(F::ONE) - sel;

            let tag = meta.query_fixed(tag_col, Rotation::cur());
            let index = meta.query_advice(index_col, Rotation::cur());
            let byte = meta.query_advice(byte_col, Rotation::cur());

            vec![
                (tag.clone(), not_sel.clone() * tag),
                (index.clone(), not_sel.clone() * index),
                (byte.clone(), not_sel * byte),
            ]
        });

        SubstringConfig {
            q_substring,
            tag_col,
            index_col,
            byte_col,
        }
    }

    fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

impl<F, N> ParserChip<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    /// Given a `sequence` of assigned native values, an index `idx`
    /// (represented with an assigned native value) and a length `len`,
    /// returns a vector of length `len` that is guaranteed to contain
    /// consecutive values from `sequence` starting at `idx`. Namely:
    /// `vec![sequence[idx], sequence[idx+1]..., sequence[idx+len-1]]`.
    ///
    /// This is enforced with constraints while keeping `idx` private.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If `idx` is not in the range `[0, |sequence| - len]`.
    fn get_subsequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        idx: &AssignedNative<F>,
        len: usize,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        let native = &self.native_gadget;
        let n = sequence.len();
        native.assert_lower_than_fixed(layouter, idx, &BigUint::from(n - len + 1))?;

        let default = self.native_gadget.assign_fixed(layouter, F::default())?;
        let mut output = vec![default; len];

        for i in 0..=(n - len) {
            let b = native.is_equal_to_fixed(layouter, idx, F::from(i as u64))?;
            for j in 0..len {
                output[j] = native.select(layouter, &b, &sequence[i + j], &output[j])?;
            }
        }

        Ok(output)
    }

    /// Given a `sequence` of assigned bytes, an index `idx` (represented with
    /// an assigned native value) and a length `len`, returns a vector of
    /// length `len` that is guaranteed to contain consecutive bytes from
    /// `sequence` starting at `idx`. Namely:
    /// `vec![sequence[idx], sequence[idx+1]..., sequence[idx+len-1]]`.
    ///
    /// This is enforced with constraints while keeping `idx` private.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If `idx` is not in the range `[0, |sequence| - len]`.
    pub fn fetch_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedByte<F>],
        idx: &AssignedNative<F>,
        len: usize,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let native = &self.native_gadget;
        let n = sequence.len();
        native.assert_lower_than_fixed(layouter, idx, &BigUint::from(n - len + 1))?;

        // We will aggregate the bytes while they fit in a single native value.
        // We then call [get_subsequence] on the aggregated values to get closer
        // to the region of interest.
        // Once there, we can expand to bytes again and perform a finer search
        // over the bytes.

        let nb_bytes_per_chunk = F::CAPACITY as usize / 8;
        let nb_chunks = n.div_ceil(nb_bytes_per_chunk);

        let mut chunks = Vec::with_capacity(nb_chunks + 1); // A dummy chunk will be added.
        for chunk_bytes in sequence.chunks(nb_bytes_per_chunk) {
            let chunk = native.assigned_from_le_bytes(layouter, chunk_bytes)?;
            chunks.push(chunk);
        }

        // The idx will be split into chunk_idx and fine_search_idx, where:
        //   * chunk_idx       := idx / nb_bytes_per_chunk
        //   * fine_search_idx := idx % nb_bytes_per_chunk
        //
        let (chunk_idx, fine_search_idx) = native.div_rem(
            layouter,
            idx,
            nb_bytes_per_chunk.into(),
            Some((1u64 << 18).into()),
        )?;

        // Add 1 because the index of interest could be between 2 chunks, even if
        // the length we are looking for fits in 1 chunk.
        let len_for_chunks = min(nb_chunks, 1 + len.div_ceil(nb_bytes_per_chunk));

        // Add a dummy chunk before the chunk search, to account for the +1 added to
        // len_for_chunks. This dummy value will never be read, but it is necessary
        // for the call to [get_subsequence] to work properly.
        let dummy = native.assign_fixed(layouter, F::default())?;
        chunks.push(dummy);

        // The following is implicitly range-checking chunk_idx to be in the range
        // [0, |chunks| - len_for_chunks]. Note that:
        //   * |chunks|       := n.div_ceil(nb_bytes_per_chunk)
        //   * len_for_chunks := min(|chunks|, 1 + len.div_ceil(nb_bytes_per_chunk))
        //
        // Thus the above range is equal to [0, 0] or
        // [0, n.div_ceil(nb_bytes_per_chunk) - len.div_ceil(nb_bytes_per_chunk) - 1],
        // which is equal or contained in the desired range:
        // [0, (n - len) / nb_bytes_per_chunk].
        let selected_chunks =
            self.get_subsequence(layouter, &chunks, &chunk_idx, len_for_chunks)?;

        // We now convert the selected chunks back to bytes in order to perform the
        // finer search.

        let mut selected_bytes = Vec::with_capacity(len_for_chunks * 8);
        for chunk in selected_chunks.iter() {
            let bytes = native.assigned_to_le_bytes(layouter, chunk, Some(nb_bytes_per_chunk))?;
            selected_bytes.extend(bytes);
        }

        let bytes_as_native: Vec<AssignedNative<F>> =
            selected_bytes.into_iter().map(|byte| byte.into()).collect();
        let output = self.get_subsequence(layouter, &bytes_as_native, &fine_search_idx, len)?;

        output
            .iter()
            .map(|x| native.convert_unsafe(layouter, x))
            .collect::<Result<Vec<_>, Error>>()
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, N> FromScratch<F> for ParserChip<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F> + FromScratch<F> + Clone,
{
    type Config = (<N as FromScratch<F>>::Config, SubstringConfig);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_gadget = <N as FromScratch<F>>::new_from_scratch(&config.0);
        <ParserChip<F, N> as ComposableChip<F>>::new(&config.1, &native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let native_config = <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns);
        let advice_cols: [Column<Advice>; NB_SUBSTRING_ADVICE_COLS] =
            [meta.advice_column(), meta.advice_column()];
        let substring_config = ParserChip::<F, N>::configure(meta, &advice_cols);
        (native_config, substring_config)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)
    }
}

#[cfg(test)]
mod tests {
    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::Circuit,
    };

    use super::*;
    use crate::{
        field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
        instructions::AssignmentInstructions,
    };

    #[derive(Clone, Debug)]
    enum Operation {
        GetSubseq,
        FetchBytes,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, N> {
        sequence: Vec<Value<F>>,
        idx: Value<F>,
        expected: Vec<F>,
        operation: Operation,
        _marker: PhantomData<N>,
    }

    impl<F, N> Circuit<F> for TestCircuit<F, N>
    where
        F: PrimeField,
        N: NativeInstructions<F> + FromScratch<F> + Clone,
    {
        type Config = <ParserChip<F, N> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            ParserChip::<F, N>::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let parser_chip = ParserChip::<F, N>::new_from_scratch(&config);
            let native_gadget = &parser_chip.native_gadget;

            let sequence = native_gadget.assign_many(&mut layouter, &self.sequence)?;
            let idx = native_gadget.assign(&mut layouter, self.idx)?;
            let len = self.expected.len();

            let res = match self.operation {
                Operation::GetSubseq => {
                    parser_chip.get_subsequence(&mut layouter, &sequence, &idx, len)
                }
                Operation::FetchBytes => {
                    let bytes = sequence
                        .iter()
                        .map(|x| native_gadget.convert(&mut layouter, x))
                        .collect::<Result<Vec<AssignedByte<F>>, Error>>()?;
                    let fetched = parser_chip.fetch_bytes(&mut layouter, &bytes, &idx, len)?;
                    Ok(fetched.iter().map(|b| b.clone().into()).collect::<Vec<_>>())
                }
            }?;

            assert_eq!(res.len(), len);
            for (resulted, expected) in res.iter().zip(self.expected.iter()) {
                native_gadget.assert_equal_to_fixed(&mut layouter, resulted, *expected)?;
            }

            parser_chip.load_from_scratch(&mut layouter)
        }
    }

    fn run<F>(sequence: &[u8], idx: usize, expected: &[u8], operation: Operation, must_pass: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>> {
            sequence: sequence.iter().map(|x| F::from(*x as u64)).map(Value::known).collect(),
            idx: Value::known(F::from(idx as u64)),
            expected: expected.iter().map(|x| F::from(*x as u64)).collect(),
            operation,
            _marker: PhantomData,
        };
        let log2_nb_rows = if sequence.len() > 1000 { 13 } else { 12 };
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }
    }

    #[test]
    fn test_get_subsequence() {
        type F = midnight_curves::Fq;
        [
            (vec![1, 2, 3, 4, 5, 6], 0, vec![1, 2, 3], true),
            (vec![1, 2, 3, 4, 5, 6], 1, vec![2, 3, 4, 5], true),
            (vec![1, 2, 4, 8, 16], 3, vec![8, 16], true),
            (vec![1, 2, 4, 8, 16], 3, vec![8], true),
            (vec![1, 2, 4, 8, 16], 3, vec![], true),
            (vec![1, 2, 4, 8, 16], 6, vec![], false),
            (vec![1, 2, 4, 8, 16], 5, vec![0], false),
            (vec![1, 2, 4, 8, 16], 4, vec![0, 0], false),
            (vec![1, 2, 4, 8, 16], 4, vec![16], true),
            (vec![3, 14, 15, 9, 26, 53, 58], 5, vec![26], false),
            (vec![3, 14, 15, 9, 26, 53, 58], 5, vec![53], true),
        ]
        .iter()
        .for_each(|(sequence, idx, expected, must_pass)| {
            run::<F>(sequence, *idx, expected, Operation::GetSubseq, *must_pass)
        });
    }

    #[test]
    fn test_fetch_bytes() {
        type F = midnight_curves::Fq;
        let short = "L'essentiel est invisible pour les yeux".as_bytes();
        let long: Vec<u8> = (0..=2000).map(|i| i as u8).collect();
        [
            (short, 0, "L".as_bytes(), true),
            (short, 12, "est".as_bytes(), true),
            (short, 26, "pour".as_bytes(), true),
            (short, 27, "our les yeu".as_bytes(), true),
            (short, 35, "yeu".as_bytes(), true),
            (short, 35, "yeux".as_bytes(), true),
            (short, 38, "x".as_bytes(), true),
            (short, 38, "".as_bytes(), true),
            (short, 39, "".as_bytes(), true),
            (short, 40, "".as_bytes(), false),
            (&long, 0, &[0, 1, 2, 3, 4], true),
            (&long, 256, &[0, 1, 2], true),
            (&long, 1000, &[232, 233], true),
            (
                &long,
                1234,
                &(0..30).map(|i| (1234 + i) as u8).collect::<Vec<_>>(),
                true,
            ),
            (&long, 1995, &[203, 204, 205], true),
            (&long, 1995, &[203, 204, 205, 206, 207], true),
            (&long, 1996, &[204, 205, 206, 207, 208], true),
            (&long, 1997, &[205, 206, 207, 208, 209], false),
        ]
        .iter()
        .for_each(|(bytes, idx, expected, must_pass)| {
            run::<F>(bytes, *idx, expected, Operation::FetchBytes, *must_pass)
        });
    }
}

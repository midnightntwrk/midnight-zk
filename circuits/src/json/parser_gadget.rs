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

use std::{cmp::min, marker::PhantomData};

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    midnight_proofs::plonk::{Column, ConstraintSystem, Instance},
};

use crate::{field::AssignedNative, instructions::NativeInstructions, types::AssignedByte};

#[derive(Clone, Debug)]
/// A gadget for parsing json data. It is parametrized by:
///  - F: the native field,
///  - N: a set of in-circuit native instructions.
pub struct ParserGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    pub(crate) native_gadget: N,
    _marker: PhantomData<F>,
}

impl<F, N> ParserGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    /// Create a new parser gadget.
    pub fn new(native_gadget: &N) -> Self {
        Self {
            native_gadget: native_gadget.clone(),
            _marker: PhantomData,
        }
    }

    /// Given a `sequence` of assigned native values, an index `idx`
    /// (represented with an assigned native value) and a length `len`,
    /// returns a vector of length `len` that is guaranteed to contain
    /// consecutive values from `sequence` starting at `idx`. Namely:
    /// `vec![sequence[idx], sequence[idx+1]..., sequence[idx+len-1]]`.
    ///
    /// This is enforced with constraints while keeping `idx` private.
    ///
    /// # Panics
    /// Let `n` be the length of the sequence. If `idx` is not in the range
    /// `[0, n - len]`, the circuit will become unsatisfiable.
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
    /// # Panics
    /// Let `n` be the length of the sequence. If `idx` is not in the range
    /// `[0, n - len]`, the circuit will become unsatisfiable.
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
        let (chunk_idx, fine_search_idx) =
            native.div_rem(layouter, idx, 1 << 18, nb_bytes_per_chunk as u32)?;

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
impl<F, N> FromScratch<F> for ParserGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F> + FromScratch<F>,
{
    type Config = <N as FromScratch<F>>::Config;

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_gadget = <N as FromScratch<F>>::new_from_scratch(config);
        ParserGadget::<F, N>::new(&native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        <N as FromScratch<F>>::configure_from_scratch(meta, instance_columns)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        <N as FromScratch<F>>::load_from_scratch(layouter, config);
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
    use crate::field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget};

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

            let sequence = native_gadget.assign_many(&mut layouter, &self.sequence)?;
            let idx = native_gadget.assign(&mut layouter, self.idx)?;
            let len = self.expected.len();

            let res = match self.operation {
                Operation::GetSubseq => {
                    parser_gadget.get_subsequence(&mut layouter, &sequence, &idx, len)
                }
                Operation::FetchBytes => {
                    let bytes = sequence
                        .iter()
                        .map(|x| native_gadget.convert(&mut layouter, x))
                        .collect::<Result<Vec<AssignedByte<F>>, Error>>()?;
                    let fetched = parser_gadget.fetch_bytes(&mut layouter, &bytes, &idx, len)?;
                    Ok(fetched.iter().map(|b| b.clone().into()).collect::<Vec<_>>())
                }
            }?;

            assert_eq!(res.len(), len);
            for (resulted, expected) in res.iter().zip(self.expected.iter()) {
                native_gadget.assert_equal_to_fixed(&mut layouter, resulted, *expected)?;
            }

            Ok(())
        }
    }

    fn run<F>(sequence: &[u8], idx: usize, expected: &[u8], operation: Operation, must_pass: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>> {
            sequence: sequence
                .iter()
                .map(|x| F::from(*x as u64))
                .map(Value::known)
                .collect(),
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
        type F = blstrs::Fq;
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
        type F = blstrs::Fq;
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

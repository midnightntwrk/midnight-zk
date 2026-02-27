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

//! Substring verification via packed lookup arguments.
//!
//! Each `(index, byte)` pair is packed into a single field element
//! `index * (ALPHABET_MAX_SIZE + 1) + byte` (see
//! [`ScannerChip::index_and_pack_sequence`]). Because indexes start at 1, zero
//! is never a valid packed value and can safely be used for padding.
//!
//! Calls to [`ScannerChip::check_bytes`] are deferred and grouped by
//! `sequence` argument in the [`SequenceCache`](super::SequenceCache). At
//! synthesis end, [`ScannerChip::finalise_substring_checks`] drains the
//! cache, packs both table and query entries, builds a row plan, and assigns
//! the region.

use midnight_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::Error,
};
use num_bigint::BigUint;

use super::{ScannerChip, NB_SUBSTRING_COLS, PARSING_MAX_LEN_BITS};
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions, RangeCheckInstructions},
    parsing::scanner::{Sequence, ALPHABET_MAX_SIZE},
    types::AssignedByte,
    CircuitField,
};

/// Structure of assigned cells for verifying substring checks.
type SubstringCheckLayout<F> = Vec<[Sequence<F>; NB_SUBSTRING_COLS]>;

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    F: CircuitField + Ord,
{
    /// Asserts that `sub` is a contiguous subsequence of `sequence` starting at
    /// index `idx` (0-indexed). In practice, this function queues the call
    /// (grouping those with the same `sequence` argument) for batch
    /// finalisation in `Self::finalise_substring_checks`.
    ///
    /// # Cost
    ///
    /// The cost of one call is of the order of `|sequence| + |sub|` rows.
    /// Due to caching, multiple calls with the same `sequence` argument only
    /// pay the `sequence`-related cost once. Up to `SUBSTRING_PARALLELISM`
    /// calls with different `sequence` arguments share the same rows through
    /// parallel lookups.
    ///
    /// # Range check
    ///
    /// The starting index is range-checked (`idx < 2^PARSING_MAX_LEN_BITS`)
    /// so that the packed lookup value `(idx + i) * (ALPHABET_MAX_SIZE + 1) +
    /// byte` is injective over the field.
    pub fn check_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedByte<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedByte<F>],
    ) -> Result<(), Error> {
        let sequence: Sequence<F> = sequence.iter().map(AssignedNative::from).collect();
        let sub: Sequence<F> = sub.iter().map(AssignedNative::from).collect();
        self.check_subsequence(layouter, &sequence, idx, &sub)
    }

    /// Generic version of `check_bytes`. Cannot be exposed publicly because
    /// it is unsound without range-checks on the elements of `sequence` and
    /// `sub` (they are packed with indexes, so values outside `[0, 255]`
    /// would break injectivity).
    fn check_subsequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        if sub.is_empty() {
            // The circuit logic will assume `sub` is not empty for padding purposes, hence
            // handling it separately.
            return Ok(());
        }
        // Range-check idx to ensure packing injectivity.
        self.native_gadget.assert_lower_than_fixed(
            layouter,
            idx,
            &(BigUint::from(1u8) << PARSING_MAX_LEN_BITS),
        )?;

        self.sequence_cache
            .borrow_mut()
            .entry(sequence.to_vec())
            .and_modify(|(calls, len)| {
                *len += sub.len();
                calls.push((idx.clone(), sub.to_vec()))
            })
            .or_insert_with(|| (vec![(idx.clone(), sub.to_vec())], sub.len()));

        Ok(())
    }
}

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    F: CircuitField,
{
    /// Packs a sequence of assigned bytes into indexed field elements:
    /// `packed[i] = (start_idx + i) * (ALPHABET_MAX_SIZE + 1) +
    /// byte[i]`
    fn index_and_pack_sequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        start_idx: &AssignedNative<F>,
    ) -> Result<Sequence<F>, Error> {
        let shift = F::from(ALPHABET_MAX_SIZE as u64 + 1);
        (sequence.iter().enumerate())
            .map(|(i, byte)| {
                let constant = F::from(i as u64);
                self.native_gadget.linear_combination(
                    layouter,
                    &[(shift, start_idx.clone()), (F::ONE, byte.clone())],
                    constant * shift,
                )
            })
            .collect()
    }

    /// Drains the sequence cache, sorts entries by decreasing sequence length
    /// (then decreasing cumulative sub length), and packs query entries with
    /// their index. Returns one `(packed_sequence, flattened_packed_subs)` per
    /// unique sequence. Each sequences and subs have been padded and organised
    /// so that it only remains to assign them in circuit.
    fn index_and_pack_calls(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<SubstringCheckLayout<F>, Error> {
        let mut calls: Vec<_> = self.sequence_cache.borrow_mut().drain().collect();
        calls.sort_by(|a, b| b.0.len().cmp(&a.0.len()).then(b.1 .1.cmp(&a.1 .1)));
        if calls.is_empty() {
            // Ensures we can access the last element of `calls` without panicking.
            return Ok(vec![]);
        }

        // Padding tables with a value that cannot be a valid byte.
        let sequence_padding: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;

        let mut layout: SubstringCheckLayout<F> = Vec::with_capacity(calls.len());
        for (sequence, (indexes_and_subs, len)) in calls {
            let region_size = sequence.len().max(len);
            let mut padded_sequence: Sequence<F> = sequence.to_vec();
            padded_sequence.resize(region_size, sequence_padding.clone());
            let subs_packed: Sequence<F> = (indexes_and_subs.iter())
                .map(|(idx, sub)| self.index_and_pack_sequence(layouter, sub, idx))
                .collect::<Result<Vec<Sequence<F>>, _>>()?
                .into_iter()
                .flatten()
                .collect();
            // Padding by repeating the first element, which never panics
            // since `check_subsequence` rejects empty `sub` arguments.
            let mut padded_subs_packed = subs_packed.clone();
            padded_subs_packed.resize(region_size, subs_packed[0].clone());
            layout.push([padded_sequence, padded_subs_packed]);
        }
        Ok(layout)
    }

    /// Assigns a single row of the substring region.
    fn assign_substring_row(
        &self,
        region: &mut Region<'_, F>,
        lookups: &[AssignedNative<F>; NB_SUBSTRING_COLS],
        offset: usize,
        index: usize,
        tag: usize,
    ) -> Result<(), Error> {
        self.config.q_substring.enable(region, offset)?;
        region.assign_fixed(
            || "substring check (index)",
            self.config.index_col,
            offset,
            || Value::known(F::from(index as u64)),
        )?;
        region.assign_fixed(
            || "substring check (tag)",
            self.config.tag_col,
            offset,
            || Value::known(F::from(tag as u64)),
        )?;
        lookups[0].copy_advice(
            || format!("substring check (table {offset})"),
            region,
            self.config.state_col,
            offset,
        )?;
        lookups[1].copy_advice(
            || format!("substring check (query {offset})"),
            region,
            self.config.letter_col,
            offset,
        )?;
        Ok(())
    }

    /// Finalises all deferred `check_bytes` calls. Called from
    /// `ComposableChip::load` at the end of circuit synthesis.
    ///
    /// The sequence cache is drained and each unique sequence, together with
    /// all its associated `(idx, sub)` pairs, is packed into indexed field
    /// elements. The packed entries are then chunked into groups of
    /// `SUBSTRING_PARALLELISM` (each group assigned a fresh non-zero tag) and
    /// laid out row by row:
    ///
    /// - **sel=ON rows**: contribute table entries (packed sequence values) and
    ///   carry queries (packed sub values). Shorter sequences within a chunk
    ///   are zero-padded, which adds `(tag, 0)` to the lookup table.
    /// - **sel=OFF rows** (if subs overflow): carry remaining queries, which
    ///   are still verified against the same tag's table entries.
    ///
    /// Each chunk contains one extra sel=ON row beyond the longest sequence,
    /// guaranteeing that `(tag, 0)` is always in the table so that
    /// zero-padded queries always pass.
    pub(super) fn finalise_substring_checks(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        // Pack all cached calls into indexed field elements.
        let packed_calls = self.index_and_pack_calls(layouter)?;

        // Build the row layout and assign in a single region.
        layouter.assign_region(
            || "substring checks",
            |mut region| {
                let mut offset = 1;
                for (tag, parallel_calls) in packed_calls.iter().enumerate() {
                    for row in 0..parallel_calls[0].len() {
                        let lookups = core::array::from_fn(|col| parallel_calls[col][row].clone());
                        self.assign_substring_row(&mut region, &lookups, offset, row, tag + 1)?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod test {
    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use super::super::ScannerChip;
    use crate::{
        instructions::AssignmentInstructions, testing_utils::FromScratch, types::AssignedByte,
        utils::circuit_modeling::circuit_to_json, CircuitField,
    };

    /// Check bytes test circuit with two witnesses, so that the isolation of
    /// successive calls to `check_bytes` is also tested.
    #[derive(Clone, Debug)]
    struct CheckBytesTestCircuit<F: CircuitField> {
        full1: Vec<Value<u8>>,
        sub1: Vec<Value<u8>>,
        idx1: Value<F>,
        full2: Vec<Value<u8>>,
        sub2: Vec<Value<u8>>,
        idx2: Value<F>,
    }

    impl<F: CircuitField> CheckBytesTestCircuit<F> {
        fn new(case1: (&str, &str, usize), case2: (&str, &str, usize)) -> Self {
            let (full1, sub1, idx1) = case1;
            let (full2, sub2, idx2) = case2;
            CheckBytesTestCircuit {
                full1: full1.bytes().map(Value::known).collect(),
                sub1: sub1.bytes().map(Value::known).collect(),
                idx1: Value::known(F::from(idx1 as u64)),
                full2: full2.bytes().map(Value::known).collect(),
                sub2: sub2.bytes().map(Value::known).collect(),
                idx2: Value::known(F::from(idx2 as u64)),
            }
        }
    }

    impl<F> Circuit<F> for CheckBytesTestCircuit<F>
    where
        F: CircuitField + FromUniformBytes<64> + Ord,
    {
        type Config = <ScannerChip<usize, F> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_columns = [meta.instance_column(), meta.instance_column()];
            ScannerChip::<usize, F>::configure_from_scratch(meta, &instance_columns)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let scanner = ScannerChip::<usize, F>::new_from_scratch(&config);
            let native_gadget = &scanner.native_gadget;

            let full1: Vec<AssignedByte<F>> =
                native_gadget.assign_many(&mut layouter, &self.full1)?;
            let sub1: Vec<AssignedByte<F>> =
                native_gadget.assign_many(&mut layouter, &self.sub1)?;
            let idx1 = native_gadget.assign(&mut layouter, self.idx1)?;
            let full2: Vec<AssignedByte<F>> =
                native_gadget.assign_many(&mut layouter, &self.full2)?;
            let sub2: Vec<AssignedByte<F>> =
                native_gadget.assign_many(&mut layouter, &self.sub2)?;
            let idx2 = native_gadget.assign(&mut layouter, self.idx2)?;

            // Two separate check_bytes calls — each gets a different sequence
            // key in the cache, so they will be assigned different tags.
            scanner.check_bytes(&mut layouter, &full1, &idx1, &sub1)?;
            scanner.check_bytes(&mut layouter, &full2, &idx2, &sub2)?;

            // Load triggers finalise_substring_checks (deferred execution model).
            scanner.load_from_scratch(&mut layouter)
        }
    }

    fn check_bytes_test(
        cost_model: bool,
        k: u32,
        case1: (&str, &str, usize),
        case2: (&str, &str, usize),
        must_pass: bool,
    ) {
        assert!(
            !cost_model || must_pass,
            "(bug) if cost_model is set to true, must_pass should be set to true"
        );
        type F = midnight_curves::Fq;

        let circuit = CheckBytesTestCircuit::<F>::new(case1, case2);
        println!(
            ">> [test check_bytes] [must{} pass] on\n\t- input1: \"{}\" = \"{}\"[{}..{}]\n\t- input2: \"{}\" = \"{}\"[{}..{}]",
            if must_pass { "" } else { " not" },
            case1.1,
            case1.0,
            case1.2,
            case1.2 + case1.1.len(),
            case2.1,
            case2.0,
            case2.2,
            case2.2 + case2.1.len(),
        );
        let result = MockProver::run(k, &circuit, vec![vec![], vec![]]);
        match result {
            Ok(p) => {
                let verified = p.verify();
                if must_pass {
                    verified.expect("the test should have passed")
                } else {
                    assert!(verified.is_err(), "the test should have failed");
                }
            }
            Err(e) => {
                assert!(!must_pass, "Prover failed unexpectedly: {:?}", e);
            }
        }
        println!("... test successful!");

        if cost_model {
            circuit_to_json::<F>(
                "Scanner",
                &format!(
                    "substring perf (full length = {}, sub length = {})",
                    case1.0.len(),
                    case1.1.len()
                ),
                circuit,
            );
        }
    }

    #[test]
    fn test_check_bytes() {
        // Test of a trivial case.
        let trivial = ("", "", 0);
        check_bytes_test(false, 9, trivial, trivial, true);

        // Basic tests (with trivial second case).
        check_bytes_test(false, 9, ("hello world", "hello", 0), trivial, true); // At beginning.
        check_bytes_test(false, 9, ("hello world", "lo wo", 3), trivial, true); // In middle.
        check_bytes_test(false, 9, ("hello world", "world", 6), trivial, true); // At end.
        check_bytes_test(false, 9, ("abcdef", "d", 3), trivial, true); // Single char.
        check_bytes_test(false, 9, ("test", "test", 0), trivial, true); // Full string.
        check_bytes_test(false, 9, ("hello world", "xyz", 0), trivial, false); // Off-Topic.
        check_bytes_test(false, 9, ("hello world", "world", 0), trivial, false); // Wrong idx.

        // Tag isolation tests.
        check_bytes_test(false, 9, ("a", "b", 0), ("b", "a", 0), false);
        check_bytes_test(
            false,
            9,
            ("hello world", "hello", 0),
            ("world", " world", 1),
            false,
        );
        check_bytes_test(false, 9, ("hello", "ell", 1), ("world", "orl", 1), true);

        // Performance test for the golden files, using a sub of 50 bytes.
        let full = "abcdefghij abcdefghij abcdefghij abcdefghij abcdefghij abcdefghij";
        let sub = &full[5..55]; // 50 bytes
        check_bytes_test(true, 10, (full, sub, 5), ("world", "orl", 1), true);
    }
}

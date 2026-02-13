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

//! Substring verification using dynamic lookups.

use std::hash::Hash;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use super::ScannerChip;
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    types::AssignedByte,
};

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: PrimeField + Ord,
{
    /// Asserts that `sub` is a contiguous subsequence of `sequence` starting at
    /// index `idx` (0-indexed). More efficient than extracting the subsequence
    /// with `fetch_bytes` and asserting equality with `sub`.
    pub fn check_subsequence(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedNative<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        // Check if the sequence is already cached; if not, allocate a fresh tag
        // and copy the sequence into the tag/byte columns.
        let seq_key = sequence.to_vec();
        let cached_tag = self.sequence_cache.borrow().get(&seq_key).copied();
        let tag = if let Some(t) = cached_tag {
            F::from(t)
        } else {
            let new_tag = {
                let mut counter = self.substring_tag_counter.borrow_mut();
                let t = *counter;
                *counter += 1;
                t
            };
            self.sequence_cache.borrow_mut().insert(seq_key, new_tag);
            let tag = F::from(new_tag);

            // Precompute all `sequence` indices.
            let seq_indices: Vec<AssignedNative<F>> = (0..sequence.len() as u64)
                .map(|i| self.native_gadget.assign_fixed(layouter, F::from(i)))
                .collect::<Result<_, Error>>()?;

            // Copy sequence into the tag/byte columns (only on first use).
            layouter.assign_region(
                || "substring sequence table",
                |mut region| {
                    for ((offset, byte), offset_assigned) in
                        sequence.iter().enumerate().zip(seq_indices.iter())
                    {
                        region.assign_fixed(
                            || format!("sequence tag {}", offset),
                            self.config.substring_tag_col,
                            offset,
                            || Value::known(tag),
                        )?;
                        offset_assigned.copy_advice(
                            || format!("sequence index {}", offset),
                            &mut region,
                            self.config.index_col,
                            offset,
                        )?;
                        byte.copy_advice(
                            || format!("sequence byte {}", offset),
                            &mut region,
                            self.config.byte_col,
                            offset,
                        )?;
                    }
                    Ok(())
                },
            )?;

            tag
        };

        // Precompute all `sub` indices.
        let sub_indices = (sub.iter().enumerate())
            .map(|(i, _)| self.native_gadget.add_constant(layouter, idx, F::from(i as u64)))
            .collect::<Result<Vec<_>, Error>>()?;

        // Assign `sub` as lookup rows (selector ON) with the (possibly cached) tag.
        layouter.assign_region(
            || "substring lookup",
            |mut region| {
                for (offset, (byte, idx)) in sub.iter().zip(sub_indices.iter()).enumerate() {
                    self.config.q_substring.enable(&mut region, offset)?;

                    region.assign_fixed(
                        || format!("sub tag {}", offset),
                        self.config.substring_tag_col,
                        offset,
                        || Value::known(tag),
                    )?;
                    idx.copy_advice(
                        || format!("sub index {}", offset),
                        &mut region,
                        self.config.index_col,
                        offset,
                    )?;
                    byte.copy_advice(
                        || format!("sub byte {}", offset),
                        &mut region,
                        self.config.byte_col,
                        offset,
                    )?;
                }

                Ok(())
            },
        )
    }

    /// Wrapper of `check_subsequence` for `AssignedByte` inputs. More efficient
    /// than using `fetch_bytes` and asserting equality with `sub`.
    pub fn check_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &[AssignedByte<F>],
        idx: &AssignedNative<F>,
        sub: &[AssignedByte<F>],
    ) -> Result<(), Error> {
        let sequence: Vec<AssignedNative<F>> = sequence.iter().map(AssignedNative::from).collect();
        let sub: Vec<AssignedNative<F>> = sub.iter().map(AssignedNative::from).collect();
        self.check_subsequence(layouter, &sequence, idx, &sub)
    }
}

#[cfg(test)]
mod test {
    use ff::{FromUniformBytes, PrimeField};
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use super::super::ScannerChip;
    use crate::{
        instructions::AssignmentInstructions, testing_utils::FromScratch, types::AssignedByte,
        utils::circuit_modeling::circuit_to_json,
    };

    /// Check bytes test circuit with two witnesses, so that the isolation of
    /// successive calls to `check_bytes` is also tested.
    #[derive(Clone, Debug)]
    struct CheckBytesTestCircuit<F: PrimeField> {
        full1: Vec<Value<u8>>,
        sub1: Vec<Value<u8>>,
        idx1: Value<F>,
        full2: Vec<Value<u8>>,
        sub2: Vec<Value<u8>>,
        idx2: Value<F>,
    }

    impl<F: PrimeField> CheckBytesTestCircuit<F> {
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
        F: PrimeField + FromUniformBytes<64> + Ord,
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

            // Two separate check_bytes calls - each should be isolated by its tag.
            scanner.check_bytes(&mut layouter, &full1, &idx1, &sub1)?;
            scanner.check_bytes(&mut layouter, &full2, &idx2, &sub2)?;

            // Only loading the native_gadget tables, as static automaton tables aren't
            // needed here.
            scanner.native_gadget.load_from_scratch(&mut layouter)
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

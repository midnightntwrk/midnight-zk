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

//! Variable-length substring checks.

use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use super::{varlen::ScannerVec, ScannerChip, PARSING_MAX_LEN_BITS};
use crate::{
    field::AssignedNative, instructions::RangeCheckInstructions, types::AssignedByte, CircuitField,
};

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord,
{
    /// Similar to [`check_bytes`](`ScannerChip::check_bytes`), but supports
    /// variable-length inputs. If `sub` has known fixed length, use
    /// [`check_bytes_varlen_partial`](`ScannerChip::check_bytes_varlen_partial`)
    /// instead.
    pub fn check_bytes_varlen<
        const M_SEQ: usize,
        const A_SEQ: usize,
        const M_SUB: usize,
        const A_SUB: usize,
    >(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &ScannerVec<F, M_SEQ, A_SEQ>,
        idx: &AssignedNative<F>,
        sub: &ScannerVec<F, M_SUB, A_SUB>,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;

        // Range-check idx to ensure packing injectivity.
        ng.assert_lower_than_fixed(layouter, idx, &(BigUint::from(1u8) << PARSING_MAX_LEN_BITS))?;

        // Index offsets: +seq_start and -sub_start, folded into packing LCs.
        let idx_offsets = vec![
            (F::ONE, sequence.limits.0.clone()),
            (-F::ONE, sub.limits.0.clone()),
        ];

        let seq_native = sequence.buffer.to_vec();
        let sub_native = sub.buffer.to_vec();
        let flags = sub.padding_flags.to_vec();
        let sub_entry = (idx.clone(), idx_offsets, sub_native, Some(flags));

        self.sequence_cache
            .borrow_mut()
            .entry(seq_native)
            .and_modify(|(calls, len)| {
                *len += M_SUB;
                calls.push(sub_entry.clone())
            })
            .or_insert_with(|| (vec![sub_entry], M_SUB));

        Ok(())
    }

    /// Similar to [`check_bytes`](`ScannerChip::check_bytes`), but the sequence
    /// is variable-length while `sub` is fixed-length. More efficient than
    /// [`check_bytes_varlen`](`ScannerChip::check_bytes_varlen`).
    pub fn check_bytes_varlen_partial<const M: usize, const A: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        sequence: &ScannerVec<F, M, A>,
        idx: &AssignedNative<F>,
        sub: &[AssignedByte<F>],
    ) -> Result<(), Error> {
        if sub.is_empty() {
            return Ok(());
        }
        let ng = &self.native_gadget;

        // Range-check idx to ensure packing injectivity.
        ng.assert_lower_than_fixed(layouter, idx, &(BigUint::from(1u8) << PARSING_MAX_LEN_BITS))?;

        // Index offset: +seq_start, folded into packing LCs.
        let idx_offsets = vec![(F::ONE, sequence.limits.0.clone())];

        let seq_native = sequence.buffer.to_vec();
        let sub_native: Vec<AssignedNative<F>> = sub.iter().map(AssignedNative::from).collect();

        self.sequence_cache
            .borrow_mut()
            .entry(seq_native)
            .and_modify(|(calls, len)| {
                *len += sub_native.len();
                calls.push((idx.clone(), idx_offsets.clone(), sub_native.clone(), None))
            })
            .or_insert_with(|| {
                let sub_entry = (idx.clone(), idx_offsets, sub_native, None);
                (vec![sub_entry], sub.len())
            });

        Ok(())
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

    // ---- check_bytes_varlen_partial tests ----

    /// Circuit: ScannerVec sequence (M=16) + fixed sub + idx.
    #[derive(Clone, Debug)]
    struct VarlenPartialCircuit<F: CircuitField> {
        full: Value<Vec<u8>>,
        sub: Vec<Value<u8>>,
        idx: Value<F>,
    }

    impl<F: CircuitField> VarlenPartialCircuit<F> {
        fn new(full: &[u8], sub: &[u8], idx: usize) -> Self {
            Self {
                full: Value::known(full.to_vec()),
                sub: sub.iter().map(|&b| Value::known(b)).collect(),
                idx: Value::known(F::from(idx as u64)),
            }
        }
    }

    impl<F> Circuit<F> for VarlenPartialCircuit<F>
    where
        F: CircuitField + FromUniformBytes<64> + Ord,
    {
        type Config = <ScannerChip<F> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_columns = [meta.instance_column(), meta.instance_column()];
            ScannerChip::<F>::configure_from_scratch(meta, &instance_columns)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let scanner = ScannerChip::<F>::new_from_scratch(&config);
            let ng = &scanner.native_gadget;

            let sequence = scanner.assign_scanner_vec::<16, 1>(&mut layouter, self.full.clone())?;
            let sub: Vec<AssignedByte<F>> = ng.assign_many(&mut layouter, &self.sub)?;
            let idx = ng.assign(&mut layouter, self.idx)?;

            scanner.check_bytes_varlen_partial(&mut layouter, &sequence, &idx, &sub)?;
            scanner.load_from_scratch(&mut layouter)
        }
    }

    fn varlen_partial_test(full: &[u8], sub: &[u8], idx: usize, must_pass: bool) {
        type F = midnight_curves::Fq;
        let circuit = VarlenPartialCircuit::<F>::new(full, sub, idx);
        println!(
            ">> [varlen_partial] [must{} pass] idx={idx}, sub len={}, full len={}",
            if must_pass { "" } else { " not" },
            sub.len(),
            full.len(),
        );
        let result = MockProver::run(10, &circuit, vec![vec![], vec![]]);
        match result {
            Ok(p) => {
                let verified = p.verify();
                if must_pass {
                    verified.expect("should have passed")
                } else {
                    assert!(verified.is_err(), "should have failed");
                }
            }
            Err(e) => assert!(!must_pass, "Prover failed unexpectedly: {:?}", e),
        }
        println!("... ok!");
    }

    #[test]
    fn test_check_bytes_varlen_partial() {
        // Correct matches.
        varlen_partial_test(b"hello world", b"hello", 0, true);
        varlen_partial_test(b"hello world", b"world", 6, true);
        varlen_partial_test(b"hello world", b"lo wo", 3, true);
        varlen_partial_test(b"hello world", b"hello world", 0, true);
        varlen_partial_test(b"abcdef", b"d", 3, true);

        // Empty sub.
        varlen_partial_test(b"hello", b"", 0, true);

        // Wrong content.
        varlen_partial_test(b"hello world", b"xyz", 0, false);
        // Wrong index.
        varlen_partial_test(b"hello world", b"world", 0, false);

        // Performance test for the golden files (M=16, sub=5).
        {
            type F = midnight_curves::Fq;
            let circuit = VarlenPartialCircuit::<F>::new(b"hello world", b"world", 6);
            circuit_to_json::<F>(
                "Scanner",
                "varlen partial substring perf (M = 16, sub length = 5)",
                circuit,
            );
        }
    }

    // ---- check_bytes_varlen tests ----

    /// Circuit: two ScannerVecs (M_SEQ=16, M_SUB=8) + idx.
    #[derive(Clone, Debug)]
    struct VarlenFullCircuit<F: CircuitField> {
        full: Value<Vec<u8>>,
        sub: Value<Vec<u8>>,
        idx: Value<F>,
    }

    impl<F: CircuitField> VarlenFullCircuit<F> {
        fn new(full: &[u8], sub: &[u8], idx: usize) -> Self {
            Self {
                full: Value::known(full.to_vec()),
                sub: Value::known(sub.to_vec()),
                idx: Value::known(F::from(idx as u64)),
            }
        }
    }

    impl<F> Circuit<F> for VarlenFullCircuit<F>
    where
        F: CircuitField + FromUniformBytes<64> + Ord,
    {
        type Config = <ScannerChip<F> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_columns = [meta.instance_column(), meta.instance_column()];
            ScannerChip::<F>::configure_from_scratch(meta, &instance_columns)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let scanner = ScannerChip::<F>::new_from_scratch(&config);
            let ng = &scanner.native_gadget;

            let sequence = scanner.assign_scanner_vec::<16, 1>(&mut layouter, self.full.clone())?;
            let sub = scanner.assign_scanner_vec::<8, 1>(&mut layouter, self.sub.clone())?;
            let idx = ng.assign(&mut layouter, self.idx)?;

            scanner.check_bytes_varlen(&mut layouter, &sequence, &idx, &sub)?;
            scanner.load_from_scratch(&mut layouter)
        }
    }

    fn varlen_full_test(full: &[u8], sub: &[u8], idx: usize, must_pass: bool) {
        type F = midnight_curves::Fq;
        let circuit = VarlenFullCircuit::<F>::new(full, sub, idx);
        println!(
            ">> [varlen_full] [must{} pass] idx={idx}, sub len={}, full len={}",
            if must_pass { "" } else { " not" },
            sub.len(),
            full.len(),
        );
        let result = MockProver::run(11, &circuit, vec![vec![], vec![]]);
        match result {
            Ok(p) => {
                let verified = p.verify();
                if must_pass {
                    verified.expect("should have passed")
                } else {
                    assert!(verified.is_err(), "should have failed");
                }
            }
            Err(e) => assert!(!must_pass, "Prover failed unexpectedly: {:?}", e),
        }
        println!("... ok!");
    }

    #[test]
    fn test_check_bytes_varlen() {
        // Correct matches.
        varlen_full_test(b"hello world", b"hello", 0, true);
        varlen_full_test(b"hello world", b"world", 6, true);
        varlen_full_test(b"hello world", b"lo wo", 3, true);
        varlen_full_test(b"abcdef", b"d", 3, true);

        // Wrong content.
        varlen_full_test(b"hello world", b"xyz", 0, false);
        // Wrong index.
        varlen_full_test(b"hello world", b"world", 0, false);

        // Performance test for the golden files (M_SEQ=16, M_SUB=8, sub=5).
        {
            type F = midnight_curves::Fq;
            let circuit = VarlenFullCircuit::<F>::new(b"hello world", b"world", 6);
            circuit_to_json::<F>(
                "Scanner",
                "varlen full substring perf (M_SEQ = 16, M_SUB = 8, sub length = 5)",
                circuit,
            );
        }
    }
}

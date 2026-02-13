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

//! Dynamic automaton parsing: uses dynamic (self-referential) lookups to parse
//! arbitrary regular expressions at runtime.

use std::hash::Hash;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::Error,
};

use super::{NativeAutomaton, Regex, ScannerChip, ALPHABET_MAX_SIZE};
use crate::{
    field::AssignedNative, instructions::AssignmentInstructions, types::AssignedByte,
};

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: PrimeField + Ord,
{
    #[allow(clippy::too_many_arguments)]
    /// Loads one transition of a dynamic automaton table.
    fn add_dynamic_table_entry(
        &self,
        region: &mut Region<'_, F>,
        tag: F,
        source: F,
        target: F,
        letter: F,
        output: F,
        offset: &mut usize,
    ) -> Result<(), Error> {
        // q_dynamic is not enabled for table rows.
        region.assign_fixed(
            || "dyn table tag",
            self.config.automaton_tag_col,
            *offset,
            || Value::known(tag),
        )?;
        // Table values are assigned as constants so that a malicious prover
        // cannot substitute an arbitrary automaton.
        region.assign_advice_from_constant(
            || "dyn table source",
            self.config.state_col,
            *offset,
            source,
        )?;
        region.assign_advice_from_constant(
            || "dyn table target",
            self.config.target_col,
            *offset,
            target,
        )?;
        region.assign_advice_from_constant(
            || "dyn table letter",
            self.config.letter_col,
            *offset,
            letter,
        )?;
        region.assign_advice_from_constant(
            || "dyn table output",
            self.config.output_col,
            *offset,
            output,
        )?;
        *offset += 1;
        Ok(())
    }

    /// Load the full transition table of a dynamic automaton.
    fn assign_dynamic_automaton_table(
        &self,
        layouter: &mut impl Layouter<F>,
        automaton: &NativeAutomaton<F>,
        tag: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "dynamic automaton table",
            |mut region| {
                let mut offset = 0;

                // Main transitions.
                for ((source, letter), (target, output)) in automaton.transitions.iter() {
                    assert!(
                        *source != F::ZERO && *target != F::ZERO,
                        "sanity check failed: dynamic automaton must not use state 0"
                    );
                    self.add_dynamic_table_entry(
                        &mut region,
                        tag,
                        *source,
                        *target,
                        *letter,
                        *output,
                        &mut offset,
                    )?;
                }

                // Sentinel final-state rows: (state, 256, 0, 0).
                for state in automaton.final_states.iter() {
                    self.add_dynamic_table_entry(
                        &mut region,
                        tag,
                        *state,
                        F::ZERO,
                        F::from(ALPHABET_MAX_SIZE as u64),
                        F::ZERO,
                        &mut offset,
                    )?;
                }

                Ok(())
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    /// Applies one transition of a dynamic automaton run. Analogous to
    /// `apply_one_transition` but uses the dynamic lookup columns
    /// (`q_dynamic`, `automaton_tag_col`, `target_col`) instead of the fixed table.
    ///
    /// Assumes `state` is already assigned at `state_col[offset]`. Enables
    /// `q_dynamic`, writes the tag, copies the letter, computes the transition,
    /// writes `target_col` and `output_col` at the current offset, then writes
    /// the next state at `state_col[offset+1]`.
    fn apply_one_dynamic_transition(
        &self,
        region: &mut Region<'_, F>,
        automaton: &NativeAutomaton<F>,
        tag: F,
        state: &mut AssignedNative<F>,
        letter: &AssignedByte<F>,
        markers: &mut Vec<AssignedNative<F>>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_dynamic.enable(region, *offset)?;

        // Assigning tag and input letter at the current offset.
        region.assign_fixed(
            || "dyn parse tag",
            self.config.automaton_tag_col,
            *offset,
            || Value::known(tag),
        )?;
        let letter_native = AssignedNative::from(letter);
        letter_native.copy_advice(
            || "dyn parse letter",
            region,
            self.config.letter_col,
            *offset,
        )?;

        // Gets the next state and outputs from the transition table (off-circuit).
        let target_opt_value = state
            .value()
            .zip(letter_native.value())
            .map(|(s, l)| automaton.transitions.get(&(*s, *l)).copied());
        target_opt_value.error_if_known_and(|o| o.is_none())?;
        let target_value = target_opt_value.map(|o| o.unwrap());
        let next_state_value = target_value.map(|t| t.0);
        let next_output_value = target_value.map(|t| t.1);

        // Assigning the target state and output.
        region.assign_advice(
            || "dyn parse target",
            self.config.target_col,
            *offset,
            || next_state_value,
        )?;
        let output = region.assign_advice(
            || "dyn parse output",
            self.config.output_col,
            *offset,
            || next_output_value,
        )?;
        markers.push(output);

        // Next state at the next row.
        *offset += 1;
        *state = region.assign_advice(
            || "dyn parse next state",
            self.config.state_col,
            *offset,
            || next_state_value,
        )?;
        Ok(())
    }

    /// Analogous to `assert_final_state` but for the dynamic lookup.
    fn assert_dynamic_final_state(
        &self,
        region: &mut Region<'_, F>,
        tag: F,
        invalid_letter: AssignedNative<F>,
        zero: AssignedNative<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_dynamic.enable(region, *offset)?;
        region.assign_fixed(
            || "dyn final tag",
            self.config.automaton_tag_col,
            *offset,
            || Value::known(tag),
        )?;
        invalid_letter.copy_advice(
            || format!("dyn final letter ({})", ALPHABET_MAX_SIZE),
            region,
            self.config.letter_col,
            *offset,
        )?;
        zero.copy_advice(
            || "dyn final output (0)",
            region,
            self.config.output_col,
            *offset,
        )?;
        zero.copy_advice(
            || "dyn final target (0)",
            region,
            self.config.target_col,
            *offset,
        )?;
        Ok(())
    }

    /// Parses `input` against the automaton derived from `regex`, using dynamic
    /// lookups. Unlike [`parse_static`], this method does not require the
    /// automaton to be baked into the circuit configuration. Instead, each
    /// distinct `regex` is lazily converted into a [`NativeAutomaton`],
    /// assigned as a dynamic lookup table (selector OFF rows), and then the
    /// parse run is constrained via lookup rows (selector ON). A caching
    /// mechanism ensures that a given regex is only converted and loaded
    /// once.
    pub(super) fn parse_dynamic(
        &self,
        layouter: &mut impl Layouter<F>,
        regex: &Regex,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        // Cache lookup: obtain automaton, tag, and whether the table needs to
        // be assigned (i.e. this is the first time we see this regex).
        let (automaton, tag_f, table_needs_assignment) = {
            let mut cache = self.regex_cache.borrow_mut();
            if let Some((aut, t)) = cache.get(regex) {
                println!("\n\nCACHE HIT!!\n\n");
                (aut.clone(), F::from(*t), false)
            } else {
                println!("\n\nCACHE MISS!!\n\n");
                let native_automaton: NativeAutomaton<F> =
                    regex.to_automaton().offset_states(1).into();
                let t = {
                    let mut counter = self.dynamic_tag_counter.borrow_mut();
                    let val = *counter;
                    *counter += 1;
                    val
                };
                cache.insert(regex.clone(), (native_automaton.clone(), t));
                (native_automaton, F::from(t), true)
            }
        };

        // Assign the table rows if this is a new automaton.
        if table_needs_assignment {
            self.assign_dynamic_automaton_table(layouter, &automaton, tag_f)?;
        }

        // Pre-assign constants.
        let invalid_letter: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;
        let zero: AssignedNative<F> = self.native_gadget.assign_fixed(layouter, F::ZERO)?;

        // Assign the parse run (q_dynamic ON rows).
        layouter.assign_region(
            || "dynamic parsing layout",
            |mut region| {
                let mut offset = 0;
                let mut markers = Vec::with_capacity(input.len());

                let mut state = region.assign_advice_from_constant(
                    || "dyn initial state",
                    self.config.state_col,
                    offset,
                    automaton.initial_state,
                )?;

                for letter in input {
                    self.apply_one_dynamic_transition(
                        &mut region,
                        &automaton,
                        tag_f,
                        &mut state,
                        letter,
                        &mut markers,
                        &mut offset,
                    )?;
                }

                self.assert_dynamic_final_state(
                    &mut region,
                    tag_f,
                    invalid_letter.clone(),
                    zero.clone(),
                    &mut offset,
                )?;

                Ok(markers)
            },
        )
    }
}
#[cfg(test)]
mod test {
    use ff::PrimeField;
    use itertools::Itertools;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use super::super::{regex::Regex, ScannerChip};
    use crate::{
        field::AssignedNative,
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        types::AssignedByte,
        utils::circuit_modeling::circuit_to_json,
    };

    /// A circuit that parses two inputs against dynamically-provided regexes
    /// using `parse_dynamic`. When both regexes are equal, the second call
    /// should hit the cache. `must_cache` controls whether this is asserted.
    #[derive(Clone, Debug)]
    struct DynamicRegexCircuit<F: PrimeField> {
        regex1: Regex,
        input1: Vec<Value<u8>>,
        output1: Vec<Value<F>>,
        regex2: Regex,
        input2: Vec<Value<u8>>,
        output2: Vec<Value<F>>,
        must_cache: bool,
    }

    impl<F: PrimeField> DynamicRegexCircuit<F> {
        fn new(
            regex1: Regex,
            input1: &str,
            output1: &[usize],
            regex2: Regex,
            input2: &str,
            output2: &[usize],
            must_cache: bool,
        ) -> Self {
            Self {
                regex1,
                input1: input1.bytes().map(Value::known).collect(),
                output1: output1.iter().map(|&x| Value::known(F::from(x as u64))).collect(),
                regex2,
                input2: input2.bytes().map(Value::known).collect(),
                output2: output2.iter().map(|&x| Value::known(F::from(x as u64))).collect(),
                must_cache,
            }
        }
    }

    impl<F> Circuit<F> for DynamicRegexCircuit<F>
    where
        F: PrimeField + Ord,
    {
        type Config = <ScannerChip<usize, F> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            ScannerChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let scanner_chip = ScannerChip::<usize, F>::new_from_scratch(&config);

            // First parse.
            let input1: Vec<AssignedByte<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.input1)?;
            let output1: Vec<AssignedNative<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.output1)?;
            let parsed1 = scanner_chip.parse_dynamic(&mut layouter, &self.regex1, &input1)?;
            assert_eq!(parsed1.len(), output1.len(), "first output length mismatch");
            parsed1.iter().zip_eq(output1.iter()).try_for_each(|(o1, o2)| {
                scanner_chip.native_gadget.assert_equal(&mut layouter, o1, o2)
            })?;

            // Second parse.
            let input2: Vec<AssignedByte<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.input2)?;
            let output2: Vec<AssignedNative<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.output2)?;
            let parsed2 = scanner_chip.parse_dynamic(&mut layouter, &self.regex2, &input2)?;
            assert_eq!(
                parsed2.len(),
                output2.len(),
                "second output length mismatch"
            );
            parsed2.iter().zip_eq(output2.iter()).try_for_each(|(o1, o2)| {
                scanner_chip.native_gadget.assert_equal(&mut layouter, o1, o2)
            })?;

            // Check caching: tag counter starts at 1; each cache miss
            // increments it. With caching, same regex -> 1 miss (counter=2).
            // Without caching, 2 different regexes -> 2 misses (counter=3).
            let tag_count = *scanner_chip.dynamic_tag_counter.borrow();
            if self.must_cache {
                assert_eq!(
                    tag_count, 2,
                    "expected cache hit (1 distinct regex), got {tag_count} tags"
                );
            } else {
                assert_eq!(
                    tag_count, 3,
                    "expected cache miss (2 distinct regexes), got {tag_count} tags"
                );
            }

            // Load the fixed tables (pow2range etc.). The automaton fixed
            // table is not loaded since we only use dynamic lookups.
            scanner_chip.native_gadget.load_from_scratch(&mut layouter)
        }
    }

    fn dynamic_basic_test(
        test_index: usize,
        cost_model: bool,
        entry1: (Regex, &str, &[usize]),
        entry2: (Regex, &str, &[usize]),
        must_pass: bool,
        must_cache: bool,
    ) {
        assert!(
            !cost_model || must_pass,
            ">> [dynamic test {test_index}] (bug) if cost_model is set to true, must_pass should be set to true"
        );
        let circuit = DynamicRegexCircuit::<midnight_curves::Fq>::new(
            entry1.0, entry1.1, entry1.2, entry2.0, entry2.1, entry2.2, must_cache,
        );
        let prover = MockProver::<midnight_curves::Fq>::run(11, &circuit, vec![vec![], vec![]]);
        if must_pass {
            println!(
                ">> [dynamic test {test_index}] Parsing inputs '{}' and '{}', which should pass (cache: {must_cache})",
                entry1.1, entry2.1
            );
            prover.unwrap().assert_satisfied()
        } else {
            match prover {
                Ok(prover) => {
                    if let Ok(()) = prover.verify() {
                        panic!(
                            ">> [dynamic test {test_index}] inputs '{}' / '{}' incorrectly accepted",
                            entry1.1, entry2.1
                        )
                    } else {
                        println!(">> [dynamic test {test_index}] verifier failed (expected)",)
                    }
                }
                Err(_) => println!(">> [dynamic test {test_index}] prover failed (expected)",),
            }
        }

        if cost_model {
            circuit_to_json::<midnight_curves::Fq>(
                "Scanner",
                &format!("dynamic parsing perf (input length = {})", entry1.1.len()),
                circuit,
            );
        }
    }

    #[test]
    fn dynamic_parsing_test() {
        let regex1 = Regex::hard_coded_example1();
        let regex2 = Regex::hard_coded_example0();

        // Two correct inputs with the same regex, cache expected.
        dynamic_basic_test(
            0,
            false,
            (
                regex1.clone(),
                "holy hell !!!",
                &[0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            ),
            (
                regex1.clone(),
                "holyyyy hell !!!",
                &[0, 1, 2, 1, 1, 1, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            ),
            true,
            true,
        );

        // Same regex, wrong output markers on second input.
        dynamic_basic_test(
            1,
            false,
            (
                regex1.clone(),
                "holy hell !!!",
                &[0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            ),
            (regex1.clone(), "holy hell !!!", &[0; 13]),
            false,
            true,
        );

        // Same regex, second input doesn't match (missing space).
        dynamic_basic_test(
            2,
            false,
            (
                regex1.clone(),
                "holy hell !!!",
                &[0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            ),
            (regex1.clone(), "holy hell!!!", &[0; 12]),
            false,
            true,
        );

        // Two different regexes, no cache expected.
        dynamic_basic_test(
            3,
            false,
            (
                regex1.clone(),
                "holy hell !!!",
                &[0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            ),
            (regex2, "hello (world)!!!!!", &[0; 18]),
            true,
            false,
        );

        // Performance test for the golden files, using an input of 50 bytes.
        let perf_input = "holyyyyyyyyy   hell    !!!!!!!!!!!!!!!!!!!!!!!!!!!";
        #[rustfmt::skip]
        let perf_output: &[usize] = &[
            0, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        ];
        dynamic_basic_test(
            4,
            true,
            (regex1.clone(), perf_input, perf_output),
            (regex1, perf_input, perf_output),
            true,
            true,
        );
    }
}

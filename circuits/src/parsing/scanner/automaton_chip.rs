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

//! Automaton parsing: assigns transitions into advice columns and verifies them
//! against a fixed lookup table.

use midnight_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::Error,
};

use super::{
    NativeAutomaton, ScannerChip, ALPHABET_MAX_SIZE, AUTOMATON_PARALLELISM, NB_AUTOMATON_COLS,
};
use crate::{
    field::AssignedNative, instructions::AssignmentInstructions, parsing::scanner::AutomatonParser,
    types::AssignedByte, CircuitField,
};

impl<F> NativeAutomaton<F>
where
    F: CircuitField + Ord,
{
    /// Computes a transition off-circuit: given the current state and a letter,
    /// returns `(target, output)`.
    fn next_transition(
        &self,
        state: &AssignedNative<F>,
        letter: &AssignedByte<F>,
    ) -> Result<(Value<F>, Value<F>), Error> {
        let letter_native: AssignedNative<F> = letter.into();
        let target_opt =
            state.value().zip(letter_native.value()).map(|(s, l)| self.get_transition(s, l));
        target_opt.error_if_known_and(|o| o.is_none())?;
        let target = target_opt.map(|o| o.unwrap());
        Ok((target.map(|t| t.0), target.map(|t| t.1)))
    }
}

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord,
{
    /// Verifies that an input matches the regular expression represented by the
    /// given automaton, using parallel lookups
    /// (`AUTOMATON_PARALLELISM` transitions per row).
    ///
    /// Layout per row (q_automaton ON):
    ///  - Group g: `adv[N*g]`=source, `adv[N*g+1]`=letter, `adv[N*g+2]`=output
    ///    (N=`NB_AUTOMATON_COLS`).
    ///  - Target of group g: `adv[N*(g+1)]` (cur) for non-last groups, `adv[0]`
    ///    (next) for last.
    ///
    /// The final row handles remaining bytes (< AUTOMATON_PARALLELISM), the
    /// final-state check, and zero-padding for unused groups.
    pub(super) fn parse_automaton(
        &self,
        layouter: &mut impl Layouter<F>,
        automaton: &NativeAutomaton<F>,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        let init_state: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, automaton.initial_state)?;
        let invalid_letter: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;
        let zero: AssignedNative<F> = self.native_gadget.assign_fixed(layouter, F::ZERO)?;

        layouter.assign_region(
            || "parsing layout",
            |mut region| {
                let mut offset = 0;
                let mut markers = Vec::with_capacity(input.len());

                // Assign initial state.
                let mut state = init_state.copy_advice(
                    || "initial state",
                    &mut region,
                    self.config.advice_cols[0],
                    offset,
                )?;

                // Process AUTOMATON_PARALLELISM bytes per row.
                for chunk in input.chunks(AUTOMATON_PARALLELISM) {
                    for (batch, letter) in chunk.iter().enumerate() {
                        self.apply_one_transition(
                            &mut region,
                            automaton,
                            &mut state,
                            letter,
                            batch,
                            &mut markers,
                            &mut offset,
                        )?;
                    }
                }

                // Final-state check + padding on the last row.
                #[allow(clippy::modulo_one)]
                self.assert_final_state(
                    &mut region,
                    &invalid_letter,
                    &zero,
                    input.len() % AUTOMATON_PARALLELISM,
                    &mut offset,
                )?;

                Ok(markers)
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    /// Applies one automaton transition at position `batch` within the current
    /// row. Assumes that `state` (the source) is already assigned at the
    /// correct cell.
    ///
    /// Copies the `letter`, assigns the `output` marker and the next state,
    /// then updates `state`. When `batch` is the last group in the row, the
    /// offset is incremented and the next state is placed at adv\[0\] of the
    /// following row.
    fn apply_one_transition(
        &self,
        region: &mut Region<'_, F>,
        automaton: &NativeAutomaton<F>,
        state: &mut AssignedNative<F>,
        letter: &AssignedByte<F>,
        batch: usize,
        markers: &mut Vec<AssignedNative<F>>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_automaton.enable(region, *offset)?;

        let base = NB_AUTOMATON_COLS * batch;
        let letter_native: AssignedNative<F> = letter.into();
        letter_native.copy_advice(
            || format!("letter batch {batch}"),
            region,
            self.config.advice_cols[base + 1],
            *offset,
        )?;

        let (next_state_val, output_val) = automaton.next_transition(state, letter)?;

        let marker = region.assign_advice(
            || format!("output batch {batch}"),
            self.config.advice_cols[base + 2],
            *offset,
            || output_val,
        )?;
        markers.push(marker);

        let target_col = if batch == AUTOMATON_PARALLELISM - 1 {
            *offset += 1;
            0
        } else {
            base + NB_AUTOMATON_COLS
        };
        *state = region.assign_advice(
            || format!("next state batch {batch}"),
            self.config.advice_cols[target_col],
            *offset,
            || next_state_val,
        )?;

        Ok(())
    }

    /// Checks that the current state is a final state, by looking up the dummy
    /// transition `(state, 256, 0, 0)`. Fills remaining groups with zeros
    /// (matching the dummy `(0,0,0,0)` table entry) and assigns the terminal
    /// row (`adv[0] = 0`, target of the last group).
    fn assert_final_state(
        &self,
        region: &mut Region<'_, F>,
        invalid_letter: &AssignedNative<F>,
        zero: &AssignedNative<F>,
        batch: usize,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_automaton.enable(region, *offset)?;

        // Final-state check (letter=256; output=0 and target=0 will be assigned as part
        // of the trailing zeroes).
        let base = NB_AUTOMATON_COLS * batch;
        invalid_letter.copy_advice(
            || format!("final check letter ({ALPHABET_MAX_SIZE})"),
            region,
            self.config.advice_cols[base + 1],
            *offset,
        )?;

        // Zero-fill remaining columns on the current row + terminal 0.
        for col in (base + 2)..(NB_AUTOMATON_COLS * AUTOMATON_PARALLELISM) {
            zero.copy_advice(
                || "parsing trailing 0",
                region,
                self.config.advice_cols[col],
                *offset,
            )?;
        }
        *offset += 1;
        zero.copy_advice(
            || "parsing trailing 0",
            region,
            self.config.advice_cols[0],
            *offset,
        )?;

        Ok(())
    }
}

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord,
{
    /// Loads the automaton data (both static library and dynamic regexes) into
    /// a single fixed lookup table. Notably:
    ///
    ///  - The dummy transition `(0,0,0,0)` is added since the empty lookup rows
    ///    will be filled by it.
    ///  - Dummy transitions `(s, 256, 0, 0)` are added for all final states `s`
    ///    to emulate final-state checking.
    pub(crate) fn load_automata_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let cache = self.automaton_cache.borrow();
        layouter.assign_table(
            || "automaton table",
            |mut table| {
                let mut offset = 0;
                let mut add_entry =
                    |source: F, letter: F, target: F, marker: F| -> Result<(), Error> {
                        table.assign_cell(
                            || "t_source",
                            self.config.t_source,
                            offset,
                            || Value::known(source),
                        )?;
                        table.assign_cell(
                            || "t_letter",
                            self.config.t_letter,
                            offset,
                            || Value::known(letter),
                        )?;
                        table.assign_cell(
                            || "t_target",
                            self.config.t_target,
                            offset,
                            || Value::known(target),
                        )?;
                        table.assign_cell(
                            || "t_output",
                            self.config.t_output,
                            offset,
                            || Value::known(marker),
                        )?;
                        offset += 1;
                        Ok(())
                    };

                // Dummy transition for empty rows.
                add_entry(F::ZERO, F::ZERO, F::ZERO, F::ZERO)?;

                // Transitions and final-state checks for every used automaton.
                for automaton in cache.values() {
                    for (source, inner) in automaton.transitions.iter() {
                        for (letter, (target, output_extr)) in inner.iter() {
                            assert!(
                                *source != F::ZERO && *target != F::ZERO,
                                "sanity check failed: the circuit requires that state 0 \
                                 is not used, but the automaton generation failed to \
                                 ensure it."
                            );
                            add_entry(*source, *letter, *target, *output_extr)?
                        }
                    }
                    for state in automaton.final_states.iter() {
                        add_entry(*state, F::from(ALPHABET_MAX_SIZE as u64), F::ZERO, F::ZERO)?
                    }
                }
                Ok(())
            },
        )
    }
}

impl<F> ScannerChip<F>
where
    F: CircuitField + Ord,
{
    /// Resolves an `AutomatonParser` to a `NativeAutomaton<F>`, caching the
    /// result. On first use the raw automaton (from the static library or from
    /// a regex) is offset so that its states don't collide with any previously
    /// resolved automaton.
    fn resolve_automaton(&self, parser: &AutomatonParser) -> NativeAutomaton<F> {
        if let Some(aut) = self.automaton_cache.borrow().get(parser) {
            return aut.clone();
        }

        let raw_automaton = match parser {
            AutomatonParser::Static(spec) => self.config.static_library[spec].clone(),
            AutomatonParser::Dynamic(regex) => regex.to_automaton(),
        };

        let offset = {
            let mut ms = self.max_state.borrow_mut();
            let o = *ms;
            *ms += raw_automaton.nb_states;
            o
        };
        let native: NativeAutomaton<F> = raw_automaton.offset_states(offset).into();
        self.automaton_cache.borrow_mut().insert(parser.clone(), native.clone());
        native
    }

    /// Parses `input` in-circuit w.r.t. a regular expression / transducer and
    /// outputs the sequence of integers it produces. The parser may either be
    /// part of a static library (faster to parse) or an arbitrary regex (more
    /// costly but supports any regex). Both variants use the same fixed lookup
    /// table mechanism.
    pub fn parse(
        &self,
        layouter: &mut impl Layouter<F>,
        parser: AutomatonParser,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        let automaton = self.resolve_automaton(&parser);
        self.parse_automaton(layouter, &automaton, input)
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use super::{
        super::{regex::Regex, AutomatonParser},
        ScannerChip,
    };
    use crate::{
        field::AssignedNative,
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        types::AssignedByte,
        utils::circuit_modeling::circuit_to_json,
        CircuitField,
    };

    #[derive(Clone, Debug)]
    struct RegexCircuit<F> {
        input: Vec<Value<u8>>,
        output: Vec<Value<F>>,
        regex: Regex,
    }

    impl<F: CircuitField> RegexCircuit<F> {
        fn new(s: &str, output: &[usize], regex: Regex) -> Self {
            let input = s.bytes().map(Value::known).collect::<Vec<_>>();
            let output =
                output.iter().map(|&x| Value::known(F::from(x as u64))).collect::<Vec<_>>();
            RegexCircuit {
                input,
                output,
                regex,
            }
        }
    }

    impl<F> Circuit<F> for RegexCircuit<F>
    where
        F: CircuitField + Ord,
    {
        type Config = <ScannerChip<F> as FromScratch<F>>::Config;

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
            let scanner_chip = ScannerChip::<F>::new_from_scratch(&config);

            let input: Vec<AssignedByte<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.input.clone())?;
            let output: Vec<AssignedNative<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.output)?;

            let parsed_output = scanner_chip.parse(
                &mut layouter,
                AutomatonParser::Dynamic(self.regex.clone()),
                &input,
            )?;
            assert!(
                parsed_output.len() == output.len(),
                "test failed: the lengths of the
            parsed output (len = {}) and of the expected output (len = {}) are
            different",
                parsed_output.len(),
                output.len()
            );
            parsed_output.iter().zip_eq(output.iter()).try_for_each(|(o1, o2)| {
                scanner_chip.native_gadget.assert_equal(&mut layouter, o1, o2)
            })?;

            scanner_chip.load_from_scratch(&mut layouter)
        }
    }

    fn parsing_one_test(
        test_index: usize,
        cost_model: bool,
        k: u32,
        input: &str,
        output: &[usize],
        circuit: &RegexCircuit<midnight_curves::Fq>,
        must_pass: bool,
    ) {
        assert!(
            !cost_model || must_pass,
            ">> [test {test_index}] (bug) if cost_model is set to true, must_pass should be set to true"
        );
        let prover = MockProver::<midnight_curves::Fq>::run(k, circuit, vec![vec![], vec![]]);
        if must_pass {
            println!(
                ">> [test {test_index}] Parsing input {}, which should pass (output: {:?})",
                input, output
            );
            prover.unwrap().assert_satisfied()
        } else {
            match prover {
                Ok(prover) => {
                    if let Ok(()) = prover.verify() {
                        panic!(
                            ">> [test {test_index}] (bug) input {} is incorrectly accepted (output {:?})",
                            input, output
                        )
                    } else {
                        println!(
                            ">> [test {test_index}] The verifier failed on input {}, which is expected",
                            input
                        )
                    }
                }
                Err(_) => println!(
                    ">> [test {test_index}] The prover failed on input {}, which is (supposedly) expected",
                    input
                ),
            }
        }

        if cost_model {
            circuit_to_json::<midnight_curves::Fq>(
                "Scanner",
                &format!(
                    "automaton parsing perf (input length = {})",
                    circuit.input.len()
                ),
                circuit.clone(),
            );
        }
    }

    // A test to check the validity of the circuit.
    fn basic_test(test_index: usize, input: &str, output: &[usize], regex: Regex, must_pass: bool) {
        parsing_one_test(
            test_index,
            false,
            10,
            input,
            output,
            &RegexCircuit::new(input, output, regex),
            must_pass,
        )
    }

    // A test for inputs that do not match the tested regex.
    fn basic_fail_test(test_index: usize, input: &str, regex: Regex) {
        basic_test(test_index, input, &vec![0; input.len()], regex, false)
    }

    // A test to record the performances of the circuit in the golden files.
    fn perf_test(test_index: usize, input: &str, regex: Regex, k: u32) {
        println!("\n>> Performance test, input size {}:", input.len());
        let output = vec![0; input.len()];
        parsing_one_test(
            test_index,
            true,
            k,
            input,
            &output,
            &RegexCircuit::new(input, &output, regex),
            true,
        )
    }

    #[test]
    // Tests automaton parsing with a single regex.
    fn parsing_test() {
        let regex0 = Regex::hard_coded_example0();
        let regex1 = Regex::hard_coded_example1();

        // Correct inputs for automaton 0.
        basic_test(0, "hello (world)!!!!!", &[0; 18], regex0.clone(), true);
        basic_test(0, "hello (world)!!!!!", &[1; 18], regex0.clone(), false); // Variant with a wrong output.
        basic_test(
            1,
            "hello (world)!!!!!oipdsfihs32,;'p'';@",
            &[0; 37],
            regex0.clone(),
            true,
        );
        basic_test(2, "hello (world)  !!!!!", &[0; 20], regex0.clone(), true);
        basic_test(2, "hello (world)  !!!!!", &[1; 20], regex0.clone(), false); // Variant with a wrong output.
        basic_test(3, "hello (world  )!!!!!", &[0; 20], regex0.clone(), true);
        basic_test(4, "hello (  world)!!!!!", &[0; 20], regex0.clone(), true);
        basic_test(
            5,
            "hello  hello hello  (world , world ) !!!!!",
            &[0; 42],
            regex0.clone(),
            true,
        );
        basic_test(
            6,
            "hello  hello hello  (world , world ) !!!!!  ;'{][0(*&6235%  /.,><",
            &[0; 65],
            regex0.clone(),
            true,
        );
        basic_test(
            7,
            "hello   hello  hello ( world,world  , world )!!!!!",
            &[0; 50],
            regex0.clone(),
            true,
        );

        // Incorrect inputs for automaton 0:
        // Missing '!'.
        basic_fail_test(8, "hello (world)!!!!", regex0.clone());
        // Additional '!'.
        basic_fail_test(9, "hello (world)!!!!!!", regex0.clone());
        // Missing '('.
        basic_fail_test(10, "hello world)!!!!!", regex0.clone());
        // Spelling.
        basic_fail_test(11, "hello (warudo)!!!!!", regex0.clone());
        // Missing space before '('.
        basic_fail_test(12, "hello hello hello(world)!!!!!", regex0.clone());
        // "world"s should be separated by ','.
        basic_fail_test(
            13,
            "hello  hello hello  (world  world ) !!!!!",
            regex0.clone(),
        );
        // Missing space.
        basic_fail_test(14, "hello hellohello ( world,world )!!!!!", regex0.clone());
        // Spaces between '!'s.
        basic_fail_test(15, "hello hellohello ( world,world )!!! !!", regex0.clone());

        // Correct inputs for automaton 1.
        basic_test(
            16,
            "holy hell !!!",
            &[0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            regex1.clone(),
            true,
        );
        basic_test(16, "holy hell !!!", &[0; 13], regex1.clone(), false); // Variant with a wrong output.
        basic_test(
            17,
            "holy   hell    !!!!!!",
            &[
                0, 1, 2, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
            ],
            regex1.clone(),
            true,
        );
        basic_test(17, "holy   hell    !!!!!!", &[0; 21], regex1.clone(), false); // Variant with a wrong output.
        basic_test(
            18,
            "holyyyy hell !!!",
            &[0, 1, 2, 1, 1, 1, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            regex1.clone(),
            true,
        );
        basic_test(
            19,
            "holyyyy   hell    !!!!!!",
            &[
                0, 1, 2, 1, 1, 1, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
            ],
            regex1.clone(),
            true,
        );

        // Incorrect inputs for automaton 1:
        // Missing space.
        basic_fail_test(20, "holy hell!!!", regex1.clone());
        basic_fail_test(21, "holyhell !!!", regex1.clone());
        basic_fail_test(22, "holyhell!!!", regex1.clone());
        basic_fail_test(23, "holyyyy hell!!!", regex1.clone());
        basic_fail_test(24, "holyyyyhell    !!!!!!", regex1.clone());
        // Missing '!'.
        basic_fail_test(25, "holy hell ", regex1.clone());
        basic_fail_test(26, "holyyyy      hell   ", regex1.clone());
        // Additional 'l'.
        basic_fail_test(27, "holy hellllll !!!", regex1.clone());

        // Performance inputs for the golden files, using automaton 0, for an input of
        // 50 bytes.
        perf_test(
            28,
            "hello hello  hello (world, world  , world )  !!!!!",
            regex0,
            10,
        );
    }

    // ---- Multi-regex / caching tests ----

    /// A circuit that parses two inputs against dynamically-provided regexes.
    /// When both regexes are equal, the second call should hit the cache.
    /// `must_cache` controls whether this is asserted.
    #[derive(Clone, Debug)]
    struct DynamicRegexCircuit<F: CircuitField> {
        regex1: Regex,
        input1: Vec<Value<u8>>,
        output1: Vec<Value<F>>,
        regex2: Regex,
        input2: Vec<Value<u8>>,
        output2: Vec<Value<F>>,
        must_cache: bool,
    }

    impl<F: CircuitField> DynamicRegexCircuit<F> {
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
        F: CircuitField + Ord,
    {
        type Config = <ScannerChip<F> as FromScratch<F>>::Config;
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
            let scanner_chip = ScannerChip::<F>::new_from_scratch(&config);

            // First parse.
            let input1: Vec<AssignedByte<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.input1)?;
            let output1: Vec<AssignedNative<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.output1)?;
            let parsed1 = scanner_chip.parse(
                &mut layouter,
                AutomatonParser::Dynamic(self.regex1.clone()),
                &input1,
            )?;
            assert_eq!(parsed1.len(), output1.len(), "first output length mismatch");
            parsed1.iter().zip_eq(output1.iter()).try_for_each(|(o1, o2)| {
                scanner_chip.native_gadget.assert_equal(&mut layouter, o1, o2)
            })?;

            // Second parse.
            let input2: Vec<AssignedByte<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.input2)?;
            let output2: Vec<AssignedNative<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.output2)?;
            let parsed2 = scanner_chip.parse(
                &mut layouter,
                AutomatonParser::Dynamic(self.regex2.clone()),
                &input2,
            )?;
            assert_eq!(
                parsed2.len(),
                output2.len(),
                "second output length mismatch"
            );
            parsed2.iter().zip_eq(output2.iter()).try_for_each(|(o1, o2)| {
                scanner_chip.native_gadget.assert_equal(&mut layouter, o1, o2)
            })?;

            // Check caching: with the same regex used twice, only 1 entry
            // should be in the cache. With 2 distinct regexes, 2 entries.
            let cache_size = scanner_chip.automaton_cache.borrow().len();
            if self.must_cache {
                assert_eq!(cache_size, 1, "expected 1 cached regex, got {cache_size}");
            } else {
                assert_eq!(cache_size, 2, "expected 2 cached regexes, got {cache_size}");
            }

            scanner_chip.load_from_scratch(&mut layouter)
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
                &format!(
                    "multi-regex parsing perf (input length = {})",
                    entry1.1.len()
                ),
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

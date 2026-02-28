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

//! Static automaton parsing: uses a fixed lookup table of transitions from a
//! pre-loaded library of automata.

use std::hash::Hash;

use midnight_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::Error,
};

use super::{ScannerChip, ALPHABET_MAX_SIZE};
use crate::{
    field::AssignedNative, instructions::AssignmentInstructions, types::AssignedByte, CircuitField,
};

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: CircuitField + Ord,
{
    /// Updates the state of the automaton (AssignedNative) according to the
    /// letter being read. If the run is stuck (i.e., no transition are
    /// possible), an `Error` is returned.
    ///
    /// This function enables the automaton selector at the current offset. It
    /// assumes that `state` is already properly copied in the current region
    /// and offset, but not `letter`. It then copies `letter` at the current
    /// offset, the next state at the next one, and updates `state` and
    /// `offset`.
    fn apply_one_transition(
        &self,
        region: &mut Region<'_, F>,
        automaton_index: &LibIndex,
        state: &mut AssignedNative<F>,
        letter: &AssignedByte<F>,
        markers: &mut Vec<AssignedNative<F>>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_automaton.enable(region, *offset)?;

        // Casting the letter as a regular `AssignedNative` to enable some methods.
        let letter: AssignedNative<F> = letter.into();

        letter.copy_advice(
            || "copying letter for parsing",
            region,
            self.config.letter_col,
            *offset,
        )?;
        let target_opt_value = state.value().zip(letter.value()).map(|(state, letter)| {
            self.config.automata[automaton_index]
                .transitions
                .get(&(*state, *letter))
                .copied()
        });
        target_opt_value.error_if_known_and(|o| o.is_none())?;
        let target_value = target_opt_value.map(|o| o.unwrap());
        let next_state_value = target_value.map(|t| t.0);
        let next_output_value = target_value.map(|t| t.1);
        let output = region.assign_advice(
            || "parsing output boolean",
            self.config.output_col,
            *offset,
            || next_output_value,
        )?;
        markers.push(output);
        *offset += 1;
        *state = region.assign_advice(
            || "parsing next state",
            self.config.state_col,
            *offset,
            || next_state_value,
        )?;
        Ok(())
    }

    /// Checks that the state, assigned at the current offset in the column
    /// `t_source`, is a final state. This is done by using a dummy transition
    /// labelled with the invalid byte number 256, and with the target state and
    /// the output marker set to 0. If the state is not final (which means the
    /// parsed input does not match the expected regular expression), the
    /// circuit will become unsatisfiable.
    fn assert_final_state(
        &self,
        region: &mut Region<'_, F>,
        invalid_letter: AssignedNative<F>,
        invalid_state: AssignedNative<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_automaton.enable(region, *offset)?;
        invalid_letter.copy_advice(
            || format!("dummy invalid letter ({})", ALPHABET_MAX_SIZE),
            region,
            self.config.letter_col,
            *offset,
        )?;
        invalid_state.copy_advice(
            || "dummy output boolean (0)",
            region,
            self.config.output_col,
            *offset,
        )?;
        *offset += 1;
        invalid_state.copy_advice(
            || "dummy target state (0)",
            region,
            self.config.state_col,
            *offset,
        )?;
        Ok(())
    }
}

impl<LibIndex, F> ScannerChip<LibIndex, F>
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
        layouter.assign_table(
            || "automaton table",
            |mut table| {
                let mut offset = 0;
                let mut add_entry =
                    |source: F, letter: F, target: F, marker:F| -> Result<(), Error> {
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

                // Main transitions.
                for automaton in self.config.automata.iter() {
                    for ((source, letter), (target,output_extr)) in automaton.1.transitions.iter() {
                            assert!(
                                *source != F::ZERO && *target != F::ZERO ,
                                "sanity check failed: the circuit requires that state 0 is not used, but the automaton generation failed to ensure it."
                            );
                            add_entry(*source, *letter, *target, *output_extr)?
                    }
                    // Dummy transitions to represent final states. Recall that letter are
                    // represented in-circuit by elements of `AssignedByte`, which are therefore
                    // range-checked to be lower than `REGEX_ALPHABET_MAX_SIZE`.
                    for state in automaton.1.final_states.iter() {
                        add_entry(*state, F::from(ALPHABET_MAX_SIZE as u64), F::ZERO, F::ZERO)?
                    }
                }
                Ok(())
            },
        )
    }
}
impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: CircuitField + Ord,
{
    /// Verifies that an input, taken under the form of a slice of
    /// `AssignedNative`, matches the regular expression represented by the
    /// automaton in `self.config.automaton`. Additionally asserts that all
    /// assigned values of `input` are lower than `regex::ALPHABET_MAX_SIZE` to
    /// enforce that the slice elements represent valid elements of type
    /// `RegexLetter`.
    pub fn parse(
        &self,
        layouter: &mut impl Layouter<F>,
        automaton_index: &LibIndex,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        let init_state: AssignedNative<F> = self.native_gadget.assign_fixed(
            layouter,
            self.config.automata[automaton_index].initial_state,
        )?;
        let invalid_letter: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;
        let invalid_state: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(0))?;
        layouter.assign_region(
            || "parsing layout",
            |mut region| {
                let mut offset = 0;
                let mut markers = Vec::with_capacity(input.len());
                let mut state = init_state.copy_advice(
                    || "initial state",
                    &mut region,
                    self.config.state_col,
                    offset,
                )?;
                input.iter().try_for_each(|letter| {
                    self.apply_one_transition(
                        &mut region,
                        automaton_index,
                        &mut state,
                        letter,
                        &mut markers,
                        &mut offset,
                    )
                })?;
                self.assert_final_state(
                    &mut region,
                    invalid_letter.clone(),
                    invalid_state.clone(),
                    &mut offset,
                )?;
                Ok(markers)
            },
        )
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

    use super::ScannerChip;
    use crate::{
        field::AssignedNative,
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        types::AssignedByte,
        utils::circuit_modeling::circuit_to_json,
        CircuitField,
    };

    #[derive(Clone, Debug, Default)]
    struct RegexCircuit<F> {
        input: Vec<Value<u8>>,
        output: Vec<Value<F>>,
        automaton_index: usize,
    }

    impl<F: CircuitField> RegexCircuit<F> {
        fn new(s: &str, output: &[usize], automaton_index: usize) -> Self {
            let input = s.bytes().map(Value::known).collect::<Vec<_>>();
            let output =
                output.iter().map(|&x| Value::known(F::from(x as u64))).collect::<Vec<_>>();
            RegexCircuit {
                input,
                output,
                automaton_index,
            }
        }
    }

    impl<F> Circuit<F> for RegexCircuit<F>
    where
        F: CircuitField + Ord,
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

            let input: Vec<AssignedByte<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.input.clone())?;
            let output: Vec<AssignedNative<F>> =
                scanner_chip.native_gadget.assign_many(&mut layouter, &self.output)?;

            println!(">> [test] About to parse an automaton with index {}, which contains {} transitions, and {} final states.",
                self.automaton_index,
                scanner_chip.config.automata[&self.automaton_index].transitions.len(),
                scanner_chip.config.automata[&self.automaton_index].final_states.len()
            );
            let parsed_output = scanner_chip.parse(&mut layouter, &self.automaton_index, &input)?;
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
                ">> [test {test_index}] Parsing input {} with automaton {}, which should pass (output: {:?})",
                input, circuit.automaton_index, output
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
                    "static parsing perf (input length = {})",
                    circuit.input.len()
                ),
                circuit.clone(),
            );
        }
    }

    // A test to check the validity of the circuit.
    fn basic_test(
        test_index: usize,
        input: &str,
        output: &[usize],
        automaton_index: usize,
        must_pass: bool,
    ) {
        parsing_one_test(
            test_index,
            false,
            10,
            input,
            output,
            &RegexCircuit::new(input, output, automaton_index),
            must_pass,
        )
    }

    // A test for inputs that do not match the tested regex.
    fn basic_fail_test(test_index: usize, input: &str, automaton_index: usize) {
        basic_test(
            test_index,
            input,
            &vec![0; input.len()],
            automaton_index,
            false,
        )
    }

    // A test to record the performances of the circuit in the golden files.
    fn perf_test(test_index: usize, input: &str, automaton_index: usize, k: u32) {
        println!(
            "\n>> Performance test (automaton {automaton_index}), input size {}:",
            input.len()
        );
        let output = vec![0; input.len()];
        parsing_one_test(
            test_index,
            true,
            k,
            input,
            &output,
            &RegexCircuit::new(input, &output, automaton_index),
            true,
        )
    }

    #[test]
    // Tests static automaton parsing.
    fn parsing_test() {
        // Correct inputs for automaton 0.
        basic_test(0, "hello (world)!!!!!", &[0; 18], 0, true);
        basic_test(0, "hello (world)!!!!!", &[1; 18], 0, false); // Variant with a wrong output.
        basic_test(
            1,
            "hello (world)!!!!!oipdsfihs32,;'p'';@",
            &[0; 37],
            0,
            true,
        );
        basic_test(2, "hello (world)  !!!!!", &[0; 20], 0, true);
        basic_test(2, "hello (world)  !!!!!", &[1; 20], 0, false); // Variant with a wrong output.
        basic_test(3, "hello (world  )!!!!!", &[0; 20], 0, true);
        basic_test(4, "hello (  world)!!!!!", &[0; 20], 0, true);
        basic_test(
            5,
            "hello  hello hello  (world , world ) !!!!!",
            &[0; 42],
            0,
            true,
        );
        basic_test(
            6,
            "hello  hello hello  (world , world ) !!!!!  ;'{][0(*&6235%  /.,><",
            &[0; 65],
            0,
            true,
        );
        basic_test(
            7,
            "hello   hello  hello ( world,world  , world )!!!!!",
            &[0; 50],
            0,
            true,
        );

        // Incorrect inputs for automaton 0:
        // Missing '!'.
        basic_fail_test(8, "hello (world)!!!!", 0);
        // Additional '!'.
        basic_fail_test(9, "hello (world)!!!!!!", 0);
        // Missing '('.
        basic_fail_test(10, "hello world)!!!!!", 0);
        // Spelling.
        basic_fail_test(11, "hello (warudo)!!!!!", 0);
        // Missing space before '('.
        basic_fail_test(12, "hello hello hello(world)!!!!!", 0);
        // "world"s should be separated by ','.
        basic_fail_test(13, "hello  hello hello  (world  world ) !!!!!", 0);
        // Missing space.
        basic_fail_test(14, "hello hellohello ( world,world )!!!!!", 0);
        // Spaces between '!'s.
        basic_fail_test(15, "hello hellohello ( world,world )!!! !!", 0);

        // Correct inputs for automaton 1.
        basic_test(
            16,
            "holy hell !!!",
            &[0, 1, 2, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            1,
            true,
        );
        basic_test(16, "holy hell !!!", &[0; 13], 1, false); // Variant with a wrong output.
        basic_test(
            17,
            "holy   hell    !!!!!!",
            &[
                0, 1, 2, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
            ],
            1,
            true,
        );
        basic_test(17, "holy   hell    !!!!!!", &[0; 21], 1, false); // Variant with a wrong output.
        basic_test(
            18,
            "holyyyy hell !!!",
            &[0, 1, 2, 1, 1, 1, 1, 0, 0, 1, 2, 2, 0, 1, 1, 1],
            1,
            true,
        );
        basic_test(
            19,
            "holyyyy   hell    !!!!!!",
            &[
                0, 1, 2, 1, 1, 1, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
            ],
            1,
            true,
        );

        // Incorrect inputs for automaton 1:
        // Missing space.
        basic_fail_test(20, "holy hell!!!", 1);
        basic_fail_test(21, "holyhell !!!", 1);
        basic_fail_test(22, "holyhell!!!", 1);
        basic_fail_test(23, "holyyyy hell!!!", 1);
        basic_fail_test(24, "holyyyyhell    !!!!!!", 1);
        // Missing '!'.
        basic_fail_test(25, "holy hell ", 1);
        basic_fail_test(26, "holyyyy      hell   ", 1);
        // Additional 'l'.
        basic_fail_test(27, "holy hellllll !!!", 1);

        // Performance inputs for the golden files, using automaton 0, for an input of
        // 50 bytes.
        perf_test(
            28,
            "hello hello  hello (world, world  , world )  !!!!!",
            0,
            10,
        );
    }
}

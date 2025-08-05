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

// Implementation of automaton parsing in circuit. Given a collection of regular
// expressions:
//  - each one is converted into an Automaton using `Regex::to_automaton`;
//  - their states are renamed using `Automaton::offset_states` so that they do
//    not share states;
//  - all transitions are loaded into a single lookup table.
//
// The entries of the table are of the form `(source state, byte number, target
// state, marker)`. Several dummy transitions are also added:
//
//  - (0,0,0,0). By offsetting the automata states (`Automaton::offset_states`),
//    it is ensured that `0` is never a reachable state, so this transition will
//    never be used. It is simply there to satisfy lookup checks when the
//    associated selector is deactivated.
//  - (s,alphabet::ALPHABET_MAX_SIZE,0,0) for each final state `s`. This
//    transition can also never be valid assuming the input alphabet only
//    contains letters (non-negative integers) lower than
//    `alphabet::ALPHABET_MAX_SIZE`. These dummy transitions are used to check
//    whether the terminal state of an automaton run is final.

use std::collections::{BTreeMap, BTreeSet};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};
#[cfg(test)]
use {
    super::regex::Regex, super::regex::RegexInstructions,
    crate::field::decomposition::chip::P2RDecompositionConfig,
    crate::field::decomposition::pow2range::Pow2RangeChip, crate::field::native::NB_ARITH_COLS,
    crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance,
};

use super::automaton::{Automaton, ALPHABET_MAX_SIZE};
use crate::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    instructions::AssignmentInstructions,
    types::AssignedByte,
    utils::ComposableChip,
};

/// Number of columns for the automata chip.
pub const NB_AUTOMATA_COLS: usize = 3;
/// Number of columns for the tables of the automata chip.
pub const NB_AUTOMATA_TABLE_COLS: usize = 4;

// Native gadget functions.
type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// A simple map from the automaton structure to handle field elements, and thus
/// precompute all transition operations on the prover code.
#[derive(Clone, Debug)]
pub struct NativeAutomaton<F> {
    /// The initial state of the automaton.
    pub initial_state: F,
    /// The final states of the automaton.
    pub final_states: BTreeSet<F>,
    /// `transitions[state][letter]` gives the transition target and its marker
    /// when in state `state`, reading input `letter`. Can be undefined, in
    /// which case it means the automaton jumps into an implicit deadlock
    /// state.
    pub transitions: BTreeMap<(F, F), (F, F)>,
}

impl<F> From<&Automaton> for NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from(value: &Automaton) -> Self {
        NativeAutomaton {
            initial_state: F::from(value.initial_state as u64),
            final_states: value
                .final_states
                .iter()
                .map(|s| F::from(*s as u64))
                .collect::<BTreeSet<_>>(),
            transitions: value
                .transitions
                .iter()
                .map(|(&(s1, a), &(s2, marker))| {
                    (
                        (F::from(s1 as u64), F::from(a as u64)),
                        (F::from(s2 as u64), F::from(marker as u64)),
                    )
                })
                .collect::<BTreeMap<_, _>>(),
        }
    }
}

impl<F> From<Automaton> for NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from(value: Automaton) -> Self {
        (&value).into()
    }
}

impl<F> NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from_collection(automata: &[Automaton]) -> Vec<Self> {
        // The offset needs to start from 1 and not 0, to ensure that no automata will
        // use the state 0 (required by the automaton chip for soundness, since
        // 0 is used as a dummy state to encode some checks as fake
        // transitions).
        let mut offset = 1;
        let mut v = Vec::with_capacity(automata.len());
        for automaton in automata {
            let na: NativeAutomaton<F> = automaton.offset_states(offset).into();
            v.push(na);
            offset += automaton.state_bound;
        }
        v
    }
}

/// Automaton gate configuration.
#[derive(Clone, Debug)]
pub struct AutomatonConfig<F> {
    automata: Vec<NativeAutomaton<F>>,
    q_automaton: Selector,
    state_col: Column<Advice>,
    letter_col: Column<Advice>,
    output_col: Column<Advice>,
    t_source: TableColumn,
    t_letter: TableColumn,
    t_target: TableColumn,
    t_output: TableColumn,
}

/// Chip for Automaton parsing.
#[derive(Clone, Debug)]
pub struct AutomatonChip<F>
where
    F: PrimeField,
{
    config: AutomatonConfig<F>,
    native_gadget: NG<F>,
}

impl<F> Chip<F> for AutomatonChip<F>
where
    F: PrimeField,
{
    type Config = AutomatonConfig<F>;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F> ComposableChip<F> for AutomatonChip<F>
where
    F: PrimeField + Ord,
{
    type InstructionDeps = NG<F>;

    type SharedResources = (
        [Column<Advice>; NB_AUTOMATA_COLS],
        [TableColumn; NB_AUTOMATA_TABLE_COLS],
        Vec<Automaton>,
    );

    fn new(config: &AutomatonConfig<F>, deps: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: deps.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> AutomatonConfig<F> {
        let q_automaton = meta.complex_selector();

        let (advice_cols, table_cols, automata) = shared_res;
        let state_col = advice_cols[0];
        let letter_col = advice_cols[1];
        let output_col = advice_cols[2];
        let t_source = table_cols[0];
        let t_letter = table_cols[1];
        let t_target = table_cols[2];
        let t_output = table_cols[3];
        // The fixed automaton of the configuration. Its set of states is offset by 1 to
        // ensure that 0 is not a reachable state (required due to how the table lookup
        // is filled).
        let automata: Vec<NativeAutomaton<F>> = NativeAutomaton::<F>::from_collection(automata);

        meta.lookup("automaton transition check", |meta| {
            let q = meta.query_selector(q_automaton);
            let source = meta.query_advice(state_col, Rotation::cur());
            let letter = meta.query_advice(letter_col, Rotation::cur());
            let target = meta.query_advice(state_col, Rotation::next());
            let output = meta.query_advice(output_col, Rotation::cur());
            vec![
                (q.clone() * source, t_source),
                (q.clone() * letter, t_letter),
                (q.clone() * target, t_target),
                (q * output, t_output),
            ]
        });

        AutomatonConfig {
            automata,
            q_automaton,
            state_col,
            letter_col,
            output_col,
            t_source,
            t_letter,
            t_target,
            t_output,
        }
    }

    // Load the automaton data (stored in config) inside a lookup table. Notably:
    //  - The dummy transition `(0,0,0)` is added since the empty lookup rows will
    //    be filled by it. This assumes that the transition table of the automaton
    //    has been offset by at least 1 to ensure that 0 can never be a reachable
    //    state of the automaton.
    //  - Dummy transitions (s,256,0) are added for all final states s to emulate
    //    final-state checking at the end of the automaton's run. The number 256 is
    //    chosen in particular since it is not a valid byte number.
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
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
                    for ((source, letter), (target,output_extr)) in automaton.transitions.iter() {
                            assert!(
                                *source != F::ZERO && *target != F::ZERO ,
                                "sanity check failed: the circuit requires that state 0 is not used, but the automaton generation failed to ensure it."
                            );
                            add_entry(*source, *letter, *target, *output_extr)?
                    }
                    // Dummy transitions to represent final states. Recall that letter are
                    // represented in-circuit by elements of `AssignedByte`, which are therefore
                    // range-checked to be lower than `REGEX_ALPHABET_MAX_SIZE`.
                    for state in automaton.final_states.iter() {
                        add_entry(*state, F::from(ALPHABET_MAX_SIZE as u64), F::ZERO, F::ZERO)?
                    }
                }
                Ok(())
            },
        )
    }
}

impl<F> AutomatonChip<F>
where
    F: PrimeField + Ord,
{
    // Updates the state of the automaton (AssignedNative) according to the letter
    // being read. If the run is stuck (i.e., no transition are possible), an
    // `Error` is returned.
    //
    // This function enables the automaton selector at the current offset. It
    // assumes that `state` is already properly copied in the current region and
    // offset, but not `letter`. It then copies `letter` at the current offset,
    // the next state at the next one, and updates `state` and `offset`.
    fn apply_one_transition(
        &self,
        region: &mut Region<'_, F>,
        automaton_index: usize,
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

    // Checks that the state, assigned at the current offset in the column
    // `t_source`, is a final state. This is done by using a dummy transition
    // labelled with the invalid byte number 256, and with the target state and
    // the output marker set to 0. If the state is not final (which means the
    // parsed input does not match the expected regular expression), the circuit
    // will become unsatisfiable.
    fn assert_final_state(
        &self,
        region: &mut Region<'_, F>,
        invalid_letter: AssignedNative<F>,
        invalid_state: AssignedNative<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_automaton.enable(region, *offset)?;
        invalid_letter.copy_advice(
            || (format!("dummy invalid letter ({})", ALPHABET_MAX_SIZE)),
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

    /// Verifies that an input, taken under the form of a slice of
    /// `AssignedNative`, matches the regular expression represented by the
    /// automaton in `self.config.automaton`. Additionally asserts that all
    /// assigned values of `input` are lower than `regex::ALPHABET_MAX_SIZE` to
    /// enforce that the slice elements represent valid elements of type
    /// `RegexLetter`.
    pub fn parse(
        &self,
        layouter: &mut impl Layouter<F>,
        automaton_index: usize,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        assert!(automaton_index < self.config.automata.len(),
            "Attempted to parse the automaton nb {automaton_index} of a configuration that only contains {} automata.",
            self.config.automata.len()
        );
        let init_state: AssignedNative<F> = self.native_gadget.assign_fixed(
            layouter,
            self.config.automata[automaton_index].initial_state,
        )?;
        let invalid_letter: AssignedNative<F> = self
            .native_gadget
            .assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;
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
// An example of a regular expression/automaton for building circuits, since
// they have to be hardcoded in the circuit at the moment. There are probably
// cleaner ways to introduce regular expressions into circuits.
impl Automaton {
    // "hello hello [...] hello \( world , world , [...] , world \) !!!!!" with
    // 1. arbitrary spaces whenever there is one
    // 2. at least one "hello" and one "world"
    // 3. an arbitrary sequence of characters different from '!' at the end of the
    //    string.
    // The definition of the regex purposely performs some non succinct operations
    // to test several constructions of the library.
    fn hard_coded_example0() -> Self {
        let hellos = Regex::word("hello").separated_non_empty_list(Regex::blanks_strict());
        let worlds = Regex::word("world").separated_non_empty_list(Regex::cat([
            Regex::blanks(),
            ",".into(),
            Regex::blanks(),
        ]));
        let marks5 = Regex::word("!").repeat(5);
        let trail = Regex::any_byte().minus("!".into()).list();
        let regex = Regex::separated_cat(
            [
                hellos.terminated(Regex::one_blank()),
                worlds
                    .delimited(Regex::blanks(), Regex::blanks())
                    .delimited("(".into(), ")".into()),
                marks5,
                trail,
            ],
            Regex::blanks(),
        );
        regex.to_automaton()
    }

    fn hard_coded_example1() -> Self {
        // `marker_regex` accepts any character, marking 'l' as 2, and
        // any other non-blank character different from 'h' as 1.
        let marker_regex = Regex::any_byte()
            .update_markers_when(&|b| !b"h\n\t ".contains(&b), 1)
            .update_markers_on(b"l", 2)
            .list();
        let holy = Regex::word("holy").terminated(Regex::word("y").list());
        let hell = Regex::word("hell");
        let marks = Regex::word("!").non_empty_list();
        let sentence = Regex::separated_cat([holy, hell, marks], Regex::blanks_strict());
        let regex = sentence.and(marker_regex);
        regex.to_automaton()
    }
}

#[cfg(test)]
impl<F> FromScratch<F> for AutomatonChip<F>
where
    F: PrimeField + Ord,
{
    type Config = (P2RDecompositionConfig, AutomatonConfig<F>);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let max_bit_len = 8;
        let native_chip = NativeChip::new(&config.0.native_config, &());
        let core_decomposition_chip = P2RDecompositionChip::new(&config.0, &max_bit_len);
        let native_gadget = NG::<F>::new(core_decomposition_chip, native_chip);
        <AutomatonChip<F> as ComposableChip<F>>::new(&config.1, &native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let nb_advice_cols = std::cmp::max(NB_AUTOMATA_COLS, NB_ARITH_COLS);
        let advice_cols = (0..nb_advice_cols)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();
        let fixed_cols = (0..NB_ARITH_COLS + 4)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();
        let table_cols: [TableColumn; NB_AUTOMATA_TABLE_COLS] =
            core::array::from_fn(|_| meta.lookup_table_column());
        let automata = vec![
            Automaton::hard_coded_example0(),
            Automaton::hard_coded_example1(),
        ];

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_cols[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_cols[..NB_ARITH_COLS + 4].try_into().unwrap(),
                *instance_columns,
            ),
        );

        let automaton_config = AutomatonChip::configure(
            meta,
            &(
                advice_cols[..NB_AUTOMATA_COLS].try_into().unwrap(),
                table_cols,
                automata,
            ),
        );

        let pow2range_config = Pow2RangeChip::configure(meta, &advice_cols[1..=4]);

        let native_gadget_config = P2RDecompositionConfig {
            native_config,
            pow2range_config,
        };

        (native_gadget_config, automaton_config)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        NG::<F>::load_from_scratch(layouter, &config.0);
        let chip = Self::new_from_scratch(config);
        let _ = chip.load(layouter);
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

    use super::AutomatonChip;
    use crate::{
        field::AssignedNative,
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        types::AssignedByte,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    struct RegexCircuit<F> {
        input: Vec<Value<u8>>,
        output: Vec<Value<F>>,
        automaton_index: usize, // Which automaton to use from the hardcoded examples.
    }

    impl<F: PrimeField> RegexCircuit<F> {
        fn new(s: &str, output: &[usize], automaton_index: usize) -> Self {
            let input = s.bytes().map(Value::known).collect::<Vec<_>>();
            let output = output
                .iter()
                .map(|&x| Value::known(F::from(x as u64)))
                .collect::<Vec<_>>();
            RegexCircuit {
                input,
                output,
                automaton_index,
            }
        }
    }

    impl<F> Circuit<F> for RegexCircuit<F>
    where
        F: PrimeField + Ord,
    {
        type Config = <AutomatonChip<F> as FromScratch<F>>::Config;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            AutomatonChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let automaton_chip = AutomatonChip::<F>::new_from_scratch(&config);
            AutomatonChip::load_from_scratch(&mut layouter, &config);

            let input: Vec<AssignedByte<F>> = automaton_chip
                .native_gadget
                .assign_many(&mut layouter, &self.input.clone())?;
            let output: Vec<AssignedNative<F>> = automaton_chip
                .native_gadget
                .assign_many(&mut layouter, &self.output)?;

            // The line below can be uncommented to estimate the cost of parsing two times.
            // The difference with parsing 1 time gives a more precise estimate of how many
            // rows the chip consumes.

            // automaton_chip.parse(&mut layouter, self.automaton_index, &bytes)?;

            println!(">> [test] About to parse an automaton with index {}, which contains {} transitions, and {} final states.",
                self.automaton_index,
                automaton_chip.config.automata[self.automaton_index].transitions.len(),
                automaton_chip.config.automata[self.automaton_index].final_states.len()
            );
            let parsed_output =
                automaton_chip.parse(&mut layouter, self.automaton_index, &input)?;
            assert!(
                parsed_output.len() == output.len(),
                "test failed: the lengths of the
            parsed output (len = {}) and of the expected output (len = {}) are
            different",
                parsed_output.len(),
                output.len()
            );
            parsed_output
                .iter()
                .zip_eq(output.iter())
                .try_for_each(|(o1, o2)| {
                    automaton_chip
                        .native_gadget
                        .assert_equal(&mut layouter, o1, o2)
                })
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
                k,
                "Automaton",
                &format!("parsing perf (input length = {})", circuit.input.len()),
                0,
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
    // Tests automaton parsing.
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

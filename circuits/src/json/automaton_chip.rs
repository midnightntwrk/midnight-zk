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

// Implementation of automaton parsing in circuit. Simply converts a regular
// expression into an Automaton using `Regex::to_automaton` and loads the
// transition table as a lookup table. Its entries are of the form `(source
// state, byte number, target state)`. In addition, several dummy transitions
// are added to the lookup table:
// - (0,0,0). By offsetting the automata states (`Automaton::offset_states`), it
//   is ensured that `0` is never a reachable state, so this transition will
//   never be used. It is simply there to satisfy lookup checks when the
//   associated selector is deactivated.
// - (s,REGEX_ALPHABET_MAX_SIZE,0) for each final state `s`. This transition can
//   also never be valid assuming the input alphabet only contains letters
//   (non-negative integers) lower than `REGEX_ALPHABET_MAX_SIZE`. These dummy
//   transitions are used to check whether the terminal state of an automaton
//   run is final.

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
    crate::field::decomposition::pow2range::Pow2RangeChip,
    crate::field::decomposition::pow2range::NB_POW2RANGE_COLS, crate::field::native::NB_ARITH_COLS,
    crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance,
};

use super::{automaton::Automaton, REGEX_ALPHABET_MAX_SIZE};
use crate::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    instructions::AssignmentInstructions,
    types::AssignedByte,
    utils::ComposableChip,
};

/// Number of columns for the automata chip.
pub const NB_AUTOMATA_COLS: usize = 2;
/// Number of columns for the tables of the automata chip.
pub const NB_AUTOMATA_TABLE_COLS: usize = 3;

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
    /// `transitions[state][letter]` gives the transition target when in state
    /// `state`, reading input `letter`. Can be undefined, in which case it
    /// means the automaton jumps into an implicit deadlock state.
    pub transitions: BTreeMap<(F, F), F>,
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
                .map(|(&(s1, a), &s2)| {
                    ((F::from(s1 as u64), F::from(a as u64)), F::from(s2 as u64))
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
    t_source: TableColumn,
    t_letter: TableColumn,
    t_target: TableColumn,
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
        let t_source = table_cols[0];
        let t_letter = table_cols[1];
        let t_target = table_cols[2];
        // The fixed automaton of the configuration. Its set of states is offset by 1 to
        // ensure that 0 is not a reachable state (required due to how the table lookup
        // is filled).
        let automata: Vec<NativeAutomaton<F>> = NativeAutomaton::<F>::from_collection(automata);

        meta.lookup("automaton transition check", |meta| {
            let q = meta.query_selector(q_automaton);
            let source = meta.query_advice(state_col, Rotation::cur());
            let letter = meta.query_advice(letter_col, Rotation::cur());
            let target = meta.query_advice(state_col, Rotation::next());
            vec![
                (q.clone() * source, t_source),
                (q.clone() * letter, t_letter),
                (q * target, t_target),
            ]
        });

        AutomatonConfig {
            automata,
            q_automaton,
            state_col,
            letter_col,
            t_source,
            t_letter,
            t_target,
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
                    |source: F, letter: F, target: F| -> Result<(), Error> {
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
                        offset += 1;
                        Ok(())
                    };

                // Dummy transition for empty rows.
                add_entry(F::ZERO, F::ZERO, F::ZERO)?;

                // Main transitions.
                for automaton in self.config.automata.iter() {
                    for ((source, letter), target) in automaton.transitions.iter() {
                            assert!(
                                *source != F::ZERO && *target != F::ZERO ,
                                "sanity check failed: the circuit requires that state 0 is not used, but the automaton generation failed to ensure it."
                            );
                            add_entry(*source, *letter, *target)?
                    }
                    // Dummy transitions to represent final states. Recall that letter are 
                    // represented in-circuit by elements of `AssignedByte`, which are therefore 
                    // range-checked to be lower than `REGEX_ALPHABET_MAX_SIZE`.
                    for state in automaton.final_states.iter() {
                        add_entry(*state, F::from(REGEX_ALPHABET_MAX_SIZE as u64), F::ZERO)?
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
        let next_state_opt_value = state.value().zip(letter.value()).map(|(state, letter)| {
            self.config.automata[automaton_index]
                .transitions
                .get(&(*state, *letter))
                .copied()
        });
        next_state_opt_value.error_if_known_and(|o| o.is_none())?;
        let next_state_value = next_state_opt_value.map(|o| o.unwrap());
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
    // `t_source`, is a final state. This is done by using a dummy transition label
    // with the invalid byte number 256. If the state is not final (which means the
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
            || (format!("dummy invalid letter ({})", REGEX_ALPHABET_MAX_SIZE)),
            region,
            self.config.letter_col,
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
    /// assigned values of `input` are lower than `REGEX_ALPHABET_MAX_SIZE` to
    /// enforce that the slice elements represent valid elements of type
    /// `RegexLetter`.
    pub fn parse(
        &self,
        layouter: &mut impl Layouter<F>,
        automaton_index: usize,
        input: &[AssignedByte<F>],
    ) -> Result<(), Error> {
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
            .assign_fixed(layouter, F::from(REGEX_ALPHABET_MAX_SIZE as u64))?;
        let invalid_state: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(0))?;
        layouter.assign_region(
            || "parsing layout",
            |mut region| {
                let mut offset = 0;
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
                        &mut offset,
                    )
                })?;
                self.assert_final_state(
                    &mut region,
                    invalid_letter.clone(),
                    invalid_state.clone(),
                    &mut offset,
                )
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
    fn hard_coded_example0() -> Self {
        let hellos = Regex::word("hello").separated_non_empty_list(" ".into());
        let worlds = Regex::word("world").separated_non_empty_list(",".into());
        let marks5 = Regex::word("!").repeat(5);
        let trail = Regex::once_any().minus("!".into()).list();
        let regex = Regex::separated_cat(
            [
                hellos.terminated(Regex::one_space()),
                worlds.delimited(Regex::lparen(), Regex::rparen()),
                marks5,
                trail,
            ],
            Regex::epsilon(),
        );
        regex.to_automaton()
    }

    fn hard_coded_example1() -> Self {
        let holy = Regex::word("holy").terminated(Regex::word("y").list());
        let hell = Regex::word("hell");
        let marks = Regex::word("!").non_empty_list();
        let regex = Regex::separated_cat([holy, hell, marks], Regex::one_space());
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

        let pow2range_config = Pow2RangeChip::configure(meta, &advice_cols[1..=NB_POW2RANGE_COLS]);

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
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use super::AutomatonChip;
    use crate::{
        instructions::AssignmentInstructions, testing_utils::FromScratch,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    struct RegexCircuit {
        input: Vec<Value<u8>>,
        automaton_index: usize, // Which automaton to use from the hardcoded examples.
    }

    impl RegexCircuit {
        fn new(s: &str, index: usize) -> Self {
            let input_bytes = s.bytes().map(Value::known).collect::<Vec<_>>();
            RegexCircuit {
                input: input_bytes,
                automaton_index: index,
            }
        }
    }

    impl<F> Circuit<F> for RegexCircuit
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

            let bytes = automaton_chip
                .native_gadget
                .assign_many(&mut layouter, &self.input.clone())?;

            // The line below can be uncommented to estimate the cost of parsing two times.
            // The difference with parsing 1 time gives a more precise estimate of how many
            // rows the chip consumes.

            // automaton_chip.parse(&mut layouter, 0, &bytes)?;

            automaton_chip.parse(&mut layouter, self.automaton_index, &bytes)
        }
    }

    fn parsing_one_test(
        cost_model: bool,
        k: u32,
        input: &str,
        circuit: &RegexCircuit,
        must_pass: bool,
    ) {
        assert!(
            !cost_model || must_pass,
            "if cost_model is set to true, must_pass should be set to true"
        );
        let prover = MockProver::<midnight_curves::Fq>::run(k, circuit, vec![vec![], vec![]]);
        if must_pass {
            println!(
                ">> Parsing input {} with automaton {}, which should pass",
                input, circuit.automaton_index
            );
            prover.unwrap().assert_satisfied()
        } else {
            match prover {
                Ok(prover) => {
                    if let Ok(()) = prover.verify() {
                        panic!("input {} is incorrectly accepted", input)
                    } else {
                        println!(
                            ">> The verifier failed on input {}, which is expected",
                            input
                        )
                    }
                }
                Err(_) => println!(
                    ">> The prover failed on input {}, which is (supposedly) expected",
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
    fn basic_test(input: &str, automaton_index: usize, must_pass: bool) {
        parsing_one_test(
            false,
            10,
            input,
            &RegexCircuit::new(input, automaton_index),
            must_pass,
        )
    }

    // A test to record the performances of the circuit in the golden files.
    fn perf_test(input: &str, automaton_index: usize, k: u32) {
        println!(
            "\n>> Performance test (automaton {automaton_index}), input size {}:",
            input.len()
        );
        parsing_one_test(
            true,
            k,
            input,
            &RegexCircuit::new(input, automaton_index),
            true,
        )
    }

    #[test]
    // Tests automaton parsing.
    fn parsing_test() {
        // Correct inputs for automaton 0.
        basic_test("hello (world)!!!!!", 0, true);
        basic_test("hello (world)!!!!!oipdsfihs32,;'p'';@", 0, true);
        basic_test("hello (world)  !!!!!", 0, true);
        basic_test("hello (world  )!!!!!", 0, true);
        basic_test("hello (  world)!!!!!", 0, true);
        basic_test("hello  hello hello  (world , world ) !!!!!", 0, true);
        basic_test(
            "hello  hello hello  (world , world ) !!!!!  ;'{][0(*&6235%  /.,><",
            0,
            true,
        );
        basic_test(
            "hello   hello  hello ( world,world  , world )!!!!!",
            0,
            true,
        );

        // Incorrect inputs for automaton 0:
        // Missing '!'.
        basic_test("hello (world)!!!!", 0, false);
        // Additional '!'.
        basic_test("hello (world)!!!!!!", 0, false);
        // Missing '('.
        basic_test("hello world)!!!!!", 0, false);
        // Spelling.
        basic_test("hello (warudo)!!!!!", 0, false);
        // Missing space before '('.
        basic_test("hello hello hello(world)!!!!!", 0, false);
        // "world"s should be separated by ','.
        basic_test("hello  hello hello  (world  world ) !!!!!", 0, false);
        // Missing space.
        basic_test("hello hellohello ( world,world )!!!!!", 0, false);
        // Spaces between '!'s.
        basic_test("hello hellohello ( world,world )!!! !!", 0, false);

        // Correct inputs for automaton 1.
        basic_test("holy hell !!!", 1, true);
        basic_test("holy   hell    !!!!!!", 1, true);
        basic_test("holyyyy hell !!!", 1, true);
        basic_test("holyyyy   hell    !!!!!!", 1, true);

        // Incorrect inputs for automaton 1:
        // Missing space.
        basic_test("holy hell!!!", 1, false);
        basic_test("holyhell !!!", 1, false);
        basic_test("holyhell!!!", 1, false);
        basic_test("holyyyy hell!!!", 1, false);
        basic_test("holyyyyhell    !!!!!!", 1, false);
        // Missing '!'.
        basic_test("holy hell ", 1, false);
        basic_test("holyyyy      hell   ", 1, false);
        // Additional 'l'.
        basic_test("holy hellllll !!!", 1, false);

        // Performance inputs for the golden files, using automaton 0.
        perf_test("hello (world)!!!!!", 0, 10);
        perf_test("hello hello  hello (world, world  , world )  !!!!!", 0, 10);
    }
}

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

//! A chip combining lookup-based parsing techniques such automaton-based
//! parsing. The chip supports:
//!
//! - **Static automaton parsing** ([`parse_static`]): uses a fixed lookup table
//!   pre-loaded with transitions from a library of automata ([`StdLibParser`]).
//! - **Dynamic automaton parsing** ([`parse_dynamic`]): uses dynamic lookups to
//!   parse arbitrary regular expressions at runtime.
//! - **Substring verification** ([`check_subsequence`], [`check_bytes`]): uses
//!   dynamic lookups to verify that a subsequence appears in a given sequence.

pub(crate) mod automaton;
mod dynamic_automaton;
/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;
mod serialization;
mod static_automaton;
pub(crate) mod static_specs;
mod substring;

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    hash::Hash,
    rc::Rc,
};

use automaton::{Automaton, ALPHABET_MAX_SIZE};
use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use regex::Regex;
use rustc_hash::FxHashMap;
pub use static_specs::{spec_library, StdLibParser};
#[cfg(test)]
use {
    crate::field::decomposition::chip::P2RDecompositionConfig,
    crate::field::decomposition::pow2range::Pow2RangeChip, crate::field::native::NB_ARITH_COLS,
    crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance, regex::RegexInstructions,
};

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    types::AssignedByte,
    utils::ComposableChip,
};

/// Number of advice columns for the scanner chip.
pub const NB_SCANNER_ADVICE_COLS: usize = 4;

// Native gadget type abbreviation.
type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// A simple map from the automaton structure to handle field elements, and thus
/// precompute all transition operations on the prover code.
#[derive(Clone, Debug)]
pub struct NativeAutomaton<F> {
    /// The initial state of the automaton.
    pub initial_state: F,
    /// The final states of the automaton.
    pub final_states: BTreeSet<F>,
    /// When `transitions[(source_state,letter)] = (target_state,marker)`, it
    /// means that in state `source_state`, upon reading the byte `letter`, the
    /// automaton run moves to state `target_state` and marks `letter` with
    /// `marker`. If the entry is undefined, the automaton run gets stuck.
    pub transitions: BTreeMap<(F, F), (F, F)>,
}

impl<F> From<&Automaton> for NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from(value: &Automaton) -> Self {
        NativeAutomaton {
            initial_state: F::from(value.initial_state as u64),
            final_states: (value.final_states.iter())
                .map(|s| F::from(*s as u64))
                .collect::<BTreeSet<_>>(),
            transitions: (value.transitions.iter())
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
    fn from_collection<LibIndex>(
        automata: &FxHashMap<LibIndex, Automaton>,
    ) -> FxHashMap<LibIndex, NativeAutomaton<F>>
    where
        LibIndex: Hash + Eq + Copy,
    {
        // The offset needs to start from 1 and not 0, to ensure that no automata will
        // use the state 0 (required by the automaton chip for soundness, since
        // 0 is used as a dummy state to encode some checks as fake
        // transitions).
        let mut offset = 1;
        (automata.iter())
            .map(|(name, automaton)| {
                let na: NativeAutomaton<F> = automaton.offset_states(offset).into();
                offset += automaton.nb_states;
                (*name, na)
            })
            .collect::<FxHashMap<_, _>>()
    }
}

#[derive(Clone, Debug)]
/// A reference for parsing methods for the function `parse`. Either an entry of
/// the static automaton library (more efficient, but limited library), or a
/// dynamic regular expression (more costly, but supports arbitrary regexes).
pub enum AutomatonParser {
    /// Static automaton library, as defined in `parsing::static_specs` (see the
    /// documentation of each object of type `StdLibParser` to get the exact
    /// regular expression they check). Implemented using fixed lookups.
    Static(StdLibParser),
    /// Parses an arbitrary regular expression. Implemented using dynamic
    /// lookups. More costly than the static library (`Static`), but more
    /// generic.
    ///
    /// # Resources
    ///
    /// Parsing dynamic regexes converts them into automata, whose transitions
    /// are then copied in the circuit. I.e., parsing a regex creates an
    /// overhead of as many Plonk rows as there are transitions. Calls are
    /// however cached, so that several parsing with the same `Regex` only load
    /// the transition table once.
    Dynamic(Regex),
}

impl From<&StdLibParser> for AutomatonParser {
    fn from(value: &StdLibParser) -> Self {
        AutomatonParser::Static(*value)
    }
}

impl From<StdLibParser> for AutomatonParser {
    fn from(value: StdLibParser) -> Self {
        AutomatonParser::from(&value)
    }
}

impl From<Regex> for AutomatonParser {
    fn from(value: Regex) -> Self {
        AutomatonParser::Dynamic(value)
    }
}

/// Scanner gate configuration.
#[derive(Clone, Debug)]
pub struct ScannerConfig<LibIndex, F> {
    // Static automaton columns.
    automata: FxHashMap<LibIndex, NativeAutomaton<F>>,
    q_automaton: Selector,
    state_col: Column<Advice>,
    letter_col: Column<Advice>,
    output_col: Column<Advice>,
    t_source: TableColumn,
    t_letter: TableColumn,
    t_target: TableColumn,
    t_output: TableColumn,

    // Dynamic automaton columns.
    q_dynamic: Selector,
    automaton_tag_col: Column<Fixed>,
    target_col: Column<Advice>,

    // Substring columns.
    q_substring: Selector,
    substring_tag_col: Column<Fixed>,
    index_col: Column<Advice>,
    byte_col: Column<Advice>,
}

type RegexCache<F> = HashMap<Regex, (NativeAutomaton<F>, u64)>;

/// Chip for scanning: automaton parsing and substring verification.
#[derive(Clone, Debug)]
pub struct ScannerChip<LibIndex, F>
where
    F: PrimeField,
{
    config: ScannerConfig<LibIndex, F>,
    native_gadget: NG<F>,
    /// Counter for generating unique positive tags for dynamic automaton
    /// lookups.
    dynamic_tag_counter: Rc<RefCell<u64>>,
    /// Cache mapping a Regex to its converted automaton and assigned tag.
    regex_cache: Rc<RefCell<RegexCache<F>>>,
    /// Counter for generating unique positive tags for substring lookups.
    substring_tag_counter: Rc<RefCell<u64>>,
    /// Cache mapping a sequence of cells to the tag assigned to it, so that
    /// repeated `check_subsequence` calls with the same `sequence` argument
    /// avoid copying it multiple times.
    sequence_cache: Rc<RefCell<HashMap<Vec<AssignedNative<F>>, u64>>>,
}

impl<LibIndex, F> Chip<F> for ScannerChip<LibIndex, F>
where
    LibIndex: Clone + Debug,
    F: PrimeField,
{
    type Config = ScannerConfig<LibIndex, F>;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<LibIndex, F> ComposableChip<F> for ScannerChip<LibIndex, F>
where
    LibIndex: Copy + Clone + Debug + Hash + Eq,
    F: PrimeField + Ord,
{
    type InstructionDeps = NG<F>;

    type SharedResources = (
        [Column<Advice>; NB_SCANNER_ADVICE_COLS],
        FxHashMap<LibIndex, Automaton>,
    );

    fn new(config: &ScannerConfig<LibIndex, F>, deps: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: deps.clone(),
            dynamic_tag_counter: Rc::new(RefCell::new(1)),
            regex_cache: Rc::new(RefCell::new(HashMap::new())),
            substring_tag_counter: Rc::new(RefCell::new(1)),
            sequence_cache: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> ScannerConfig<LibIndex, F> {
        let (advice_cols, automata) = shared_res;

        // Static automaton resources.
        let q_automaton = meta.complex_selector();

        let state_col = advice_cols[0];
        let letter_col = advice_cols[1];
        let output_col = advice_cols[2];
        let target_col = advice_cols[3];
        let t_source = meta.lookup_table_column();
        let t_letter = meta.lookup_table_column();
        let t_target = meta.lookup_table_column();
        let t_output = meta.lookup_table_column();

        let automata = NativeAutomaton::<F>::from_collection(automata);

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

        // Dynamic automaton resources.
        let q_dynamic = meta.complex_selector();
        // Tag column for isolating different dynamic automata. For soundness,
        // this column must be 0 in rows not belonging to any dynamic automaton
        // table, so it cannot be shared.
        let automaton_tag_col = meta.fixed_column();

        meta.enable_equality(state_col);
        meta.enable_equality(letter_col);
        meta.enable_equality(output_col);
        meta.enable_equality(target_col);

        // Self-referential dynamic lookup: rows where q_dynamic is ON must match
        // a row where q_dynamic is OFF (i.e., a table row). The tag isolates
        // different automata, similarly to how `check_subsequence` works.
        meta.lookup_any("dynamic automaton transition check", |meta| {
            let sel = meta.query_selector(q_dynamic);
            let not_sel = Expression::Constant(F::ONE) - sel;

            let tag = meta.query_fixed(automaton_tag_col, Rotation::cur());
            let source = meta.query_advice(state_col, Rotation::cur());
            let target = meta.query_advice(target_col, Rotation::cur());
            let letter = meta.query_advice(letter_col, Rotation::cur());
            let output = meta.query_advice(output_col, Rotation::cur());

            vec![
                (tag.clone(), not_sel.clone() * tag),
                (source.clone(), not_sel.clone() * source),
                (target.clone(), not_sel.clone() * target),
                (letter.clone(), not_sel.clone() * letter),
                (output.clone(), not_sel * output),
            ]
        });

        // Substring resources.
        let q_substring = meta.complex_selector();
        // Separate tag column for substring lookups. Must be separate from
        // automaton_tag_col to avoid phantom table entries across lookups.
        let substring_tag_col = meta.fixed_column();

        // Constants column used by assign_advice_from_constant to pin
        // dynamic automaton table entries at keygen time.
        let constants_col = meta.fixed_column();
        meta.enable_constant(constants_col);

        // Substring reuses advice_cols[0] and advice_cols[1] as index_col and
        // byte_col respectively.
        let index_col = advice_cols[0];
        let byte_col = advice_cols[1];

        // enable_equality for index_col and byte_col: state_col (=advice_cols[0])
        // and letter_col (=advice_cols[1]) are already equality-enabled above.

        meta.lookup_any("substring lookup", |meta| {
            let sel = meta.query_selector(q_substring);
            let not_sel = Expression::Constant(F::ONE) - sel;

            let tag = meta.query_fixed(substring_tag_col, Rotation::cur());
            let index = meta.query_advice(index_col, Rotation::cur());
            let byte = meta.query_advice(byte_col, Rotation::cur());

            vec![
                (tag.clone(), not_sel.clone() * tag),
                (index.clone(), not_sel.clone() * index),
                (byte.clone(), not_sel * byte),
            ]
        });

        ScannerConfig {
            automata,
            q_automaton,
            state_col,
            letter_col,
            output_col,
            t_source,
            t_letter,
            t_target,
            t_output,
            q_dynamic,
            automaton_tag_col,
            target_col,
            q_substring,
            substring_tag_col,
            index_col,
            byte_col,
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
    F: PrimeField + Ord,
{
    /// Parses `input` in-circuit w.r.t. a regular expression / transducer and
    /// outputs the sequence of integers it produces. The parser may either be
    /// part of a static library (faster to parse) or an arbitrary regex (more
    /// costly but supports any regex).
    pub fn parse(
        &self,
        layouter: &mut impl Layouter<F>,
        parser: AutomatonParser,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error>
    where
        LibIndex: From<StdLibParser>,
    {
        match parser {
            AutomatonParser::Static(automaton_index) => {
                self.parse_static(layouter, &automaton_index.into(), input)
            }
            AutomatonParser::Dynamic(regex) => self.parse_dynamic(layouter, &regex, input),
        }
    }
}

#[cfg(test)]
impl Regex {
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
        Regex::separated_cat(
            [
                hellos.terminated(Regex::one_blank()),
                worlds
                    .delimited(Regex::blanks(), Regex::blanks())
                    .delimited("(".into(), ")".into()),
                marks5,
                trail,
            ],
            Regex::blanks(),
        )
    }

    fn hard_coded_example1() -> Self {
        // `marker_regex` accepts any character, marking 'l' as 2, and
        // any other non-blank character different from 'h' as 1.
        let marker_regex = Regex::any_byte()
            .mark(&|b| {
                if b == b'l' {
                    Some(2)
                } else if !b"h\n\t ".contains(&b) {
                    Some(1)
                } else {
                    None
                }
            })
            .list();
        let holy = Regex::word("holy").terminated(Regex::word("y").list());
        let hell = Regex::word("hell");
        let marks = Regex::word("!").non_empty_list();
        let sentence = Regex::separated_cat([holy, hell, marks], Regex::blanks_strict());
        sentence.and(marker_regex)
    }
}

#[cfg(test)]
impl<F> FromScratch<F> for ScannerChip<usize, F>
where
    F: PrimeField + Ord,
{
    type Config = (P2RDecompositionConfig, ScannerConfig<usize, F>);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let max_bit_len = 8;
        let native_chip = NativeChip::new(&config.0.native_config, &());
        let core_decomposition_chip = P2RDecompositionChip::new(&config.0, &max_bit_len);
        let native_gadget = NG::<F>::new(core_decomposition_chip, native_chip);
        <ScannerChip<usize, F> as ComposableChip<F>>::new(&config.1, &native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let nb_advice_cols = std::cmp::max(NB_SCANNER_ADVICE_COLS, NB_ARITH_COLS);
        let advice_cols = (0..nb_advice_cols).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed_cols = (0..NB_ARITH_COLS + 4).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let automata = FxHashMap::from_iter(
            [
                Regex::hard_coded_example0().to_automaton(),
                Regex::hard_coded_example1().to_automaton(),
            ]
            .into_iter()
            .enumerate(),
        );

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_cols[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_cols[..NB_ARITH_COLS + 4].try_into().unwrap(),
                *instance_columns,
            ),
        );

        let scanner_config = ScannerChip::configure(
            meta,
            &(
                advice_cols[..NB_SCANNER_ADVICE_COLS].try_into().unwrap(),
                automata,
            ),
        );

        let pow2range_config = Pow2RangeChip::configure(meta, &advice_cols[1..=4]);

        let native_gadget_config = P2RDecompositionConfig {
            native_config,
            pow2range_config,
        };

        (native_gadget_config, scanner_config)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)?;
        self.load(layouter)
    }
}

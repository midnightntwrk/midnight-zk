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

//! A chip combining lookup-based parsing techniques such as automaton-based
//! parsing. The chip supports:
//!
//! - **Static automaton parsing** (`parse_static`): uses a fixed lookup table
//!   pre-loaded with transitions from a library of automata ([`StdLibParser`]).

pub(crate) mod automaton;
mod automaton_chip;
/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;
mod serialization;
pub(crate) mod static_specs;
mod substring;

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    hash::Hash,
    rc::Rc,
};

use automaton::Automaton;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn},
    poly::Rotation,
};
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
    utils::ComposableChip,
    CircuitField,
};

/// Maximal size of the alphabet of an automaton/regex, since input characters
/// are represented by `AssignedByte`. The parser (`scanner::parse_automaton`)
/// is using this information to store automaton final states in the transition
/// table, by encoding them as impossible transitions starting from the said
/// state, and labelled with letter `ALPHABET_MAX_SIZE`. This bound is also
/// needed to represent letters as u8.
const ALPHABET_MAX_SIZE: usize = 256;

/// Number of advice columns used per automaton lookup (source, letter, output).
const NB_AUTOMATON_COLS: usize = 3;
/// Number of advice columns used per substring lookup argument (packed
/// sequence+index, packed sub+index).
const NB_SUBSTRING_COLS: usize = 2;

/// Maximum bit-length for the longer sequence length in substring checks. This
/// value must be chosen lower or equal than `F::CAPACITY - 8`.
const PARSING_MAX_LEN_BITS: u32 = 64;

/// Number of advice columns for the scanner chip.
pub const NB_SCANNER_ADVICE_COLS: usize = {
    if NB_AUTOMATON_COLS > NB_SUBSTRING_COLS {
        NB_AUTOMATON_COLS
    } else {
        NB_SUBSTRING_COLS
    }
};

/// Number of shared fixed columns necessary for the scanner chip.
pub const NB_SCANNER_FIXED_COLS: usize = 1;

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
    F: CircuitField + Ord,
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
    F: CircuitField + Ord,
{
    fn from(value: Automaton) -> Self {
        (&value).into()
    }
}

impl<F> NativeAutomaton<F>
where
    F: CircuitField + Ord,
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

/// A sequence of assigned elements.
type Sequence<F> = Vec<AssignedNative<F>>;
/// Cache of assigned sequences passed as arguments to `check_subsequence`. Each
/// sequence is mapped to the list of `(idx, sub)` pairs it was called with.
/// Also stores the cumulative length of all `sub` associateed to this key.
type SequenceCache<F> = FxHashMap<Sequence<F>, (Vec<(AssignedNative<F>, Sequence<F>)>, usize)>;

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

    // Substring resources. The tag column is used for domain separation and cannot be shared.
    q_substring: Selector,
    index_col: Column<Fixed>,
    tag_col: Column<Fixed>,
}

/// Chip for scanning: automaton parsing and substring verification.
#[derive(Clone, Debug)]
pub struct ScannerChip<LibIndex, F>
where
    F: CircuitField,
{
    config: ScannerConfig<LibIndex, F>,
    native_gadget: NG<F>,

    /// Cache mapping a sequence of cells to the list of `(idx, sub)` pairs
    /// it was called with, so that repeated `check_bytes` calls with the same
    /// `sequence` argument share the table cost. Tags are assigned later
    /// during finalisation.
    sequence_cache: Rc<RefCell<SequenceCache<F>>>,
}

impl<LibIndex, F> Chip<F> for ScannerChip<LibIndex, F>
where
    LibIndex: Clone + Debug,
    F: CircuitField,
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
    F: CircuitField + Ord,
{
    type InstructionDeps = NG<F>;

    type SharedResources = (
        [Column<Advice>; NB_SCANNER_ADVICE_COLS],
        Column<Fixed>,
        FxHashMap<LibIndex, Automaton>,
    );

    fn new(config: &ScannerConfig<LibIndex, F>, deps: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: deps.clone(),
            sequence_cache: Rc::new(RefCell::new(FxHashMap::default())),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> ScannerConfig<LibIndex, F> {
        let (advice_cols, index_col, automata) = shared_res;

        // Static automaton resources.
        let q_automaton = meta.complex_selector();

        let state_col = advice_cols[0];
        let letter_col = advice_cols[1];
        let output_col = advice_cols[2];
        let t_source = meta.lookup_table_column();
        let t_letter = meta.lookup_table_column();
        let t_target = meta.lookup_table_column();
        let t_output = meta.lookup_table_column();

        // The fixed automaton of the configuration. Its set of states is offset by 1 to
        // ensure that 0 is not a reachable state (required due to how the table lookup
        // is filled).
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

        // Substring resources.
        let tag_col = meta.fixed_column();
        let q_substring = meta.complex_selector();

        // Each lookup argument operate on NB_SUBSTRING_COLS = 2 advice columns: 1 table
        // column + 1 query column. Queries are looked up in the table with the
        // following convention:
        //   1. sel=ON, index > 0: 1 table entry + 1 query for each lookup argument, in
        //      this row.
        //   2. sel=OFF, index > 0: 1 query. The table column is unconstrained. In
        //      practice, will never happen.
        //   3. sel=OFF, index = 0: tautology. Happens when managing other functions.
        meta.lookup_any("substring lookup", |meta| {
            let sel = meta.query_selector(q_substring);
            let not_sel = Expression::Constant(F::ONE) - sel.clone();
            let index = meta.query_fixed(*index_col, Rotation::cur());
            let tag = meta.query_fixed(tag_col, Rotation::cur());
            let shift = Expression::Constant(F::from(ALPHABET_MAX_SIZE as u64 + 1));

            let table = meta.query_advice(state_col, Rotation::cur());
            let query = meta.query_advice(letter_col, Rotation::cur());

            vec![
                (tag.clone(), sel.clone() * tag.clone()),
                (
                    query.clone(),
                    sel * (index * shift + table) + not_sel * query,
                ),
            ]
        });

        ScannerConfig {
            state_col,
            letter_col,
            output_col,
            automata: automata.clone(),
            q_automaton,
            t_source,
            t_letter,
            t_target,
            t_output,
            q_substring,
            index_col: *index_col,
            tag_col,
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

#[cfg(test)]
impl regex::Regex {
    // "hello hello [...] hello \( world , world , [...] , world \) !!!!!" with
    // 1. arbitrary spaces whenever there is one
    // 2. at least one "hello" and one "world"
    // 3. an arbitrary sequence of characters different from '!' at the end of the
    //    string.
    // The definition of the regex purposely performs some non succinct operations
    // to test several constructions of the library.
    fn hard_coded_example0() -> Self {
        use regex::Regex;
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
        use regex::Regex;
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
    F: CircuitField + Ord,
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
                regex::Regex::hard_coded_example0().to_automaton(),
                regex::Regex::hard_coded_example1().to_automaton(),
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
                fixed_cols[0],
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

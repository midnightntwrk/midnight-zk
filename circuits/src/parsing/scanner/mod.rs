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

//! A chip combining lookup-based parsing techniques. The chip supports:
//!
//! - **Static automaton parsing** (`ScannerChip::parse`): verifies that a byte
//!   sequence matches a regular expression, using a fixed lookup table
//!   pre-loaded with transitions from a library of automata ([`StdLibParser`]),
//!   and/or dynamically-provided regular expressions. See the `automaton_chip`
//!   module for details.
//!
//! - **Substring checks** (`ScannerChip::check_bytes`): verifies that a
//!   sub-sequence appears at a given position inside a larger sequence, using a
//!   dynamic lookup argument. Calls are deferred and batched at the end of
//!   circuit synthesis for efficiency. See the `substring` module for details.

/// ASN.1 DER encoding helpers, structure types, and circuit-level
/// tag/length interpretation functions.
pub mod asn1;
pub(crate) mod automaton;
mod automaton_chip;
/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;
mod serialization;
pub mod static_specs;
mod substring;
mod substring_varlen;
pub(crate) mod varlen;

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use automaton::Automaton;
use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use regex::Regex;
use rustc_hash::FxHashMap;
pub use static_specs::StdLibParser;

/// A test vector pairing an input with expected marker-grouped outputs.
#[cfg(test)]
pub(crate) type MarkerTestVector<'a> = (&'a [u8], &'a [(usize, &'a [u8])]);

/// A test vector pairing an input with the expected raw output sequence.
#[cfg(test)]
pub(crate) type OutputTestVector<'a> = (&'a [u8], &'a [usize]);

#[cfg(test)]
use {
    crate::field::decomposition::chip::P2RDecompositionConfig,
    crate::field::decomposition::pow2range::Pow2RangeChip, crate::field::native::NB_ARITH_COLS,
    crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance, regex::RegexInstructions,
};

use crate::{
    field::{
        decomposition::chip::P2RDecompositionChip, native::AssignedBit, AssignedNative, NativeChip,
        NativeGadget,
    },
    utils::ComposableChip,
    vec::vector_gadget::VectorGadget,
    CircuitField,
};

/// Maximal size of the alphabet of an automaton/regex (input bytes are in
/// `[0, 255]`). Also used to encode final states in the transition table as
/// dummy transitions labelled with `ALPHABET_MAX_SIZE` (see the
/// `automaton_chip` module), and as the packing shift for substring checks
/// (see the `substring` module).
const ALPHABET_MAX_SIZE: usize = 256;

/// Number of advice columns used per automaton lookup (source, letter, output).
const NB_AUTOMATON_COLS: usize = 3;
/// Number of advice columns used per substring lookup argument (packed
/// sequence+index, packed sub+index).
const NB_SUBSTRING_COLS: usize = 2;

/// Number of parallel lookups performed by automata based parsers.
const AUTOMATON_PARALLELISM: usize = 2;
/// Number of parallel query lookups for substring checks. The total advice
/// columns is `(1 + SUBSTRING_PARALLELISM) * NB_SUBSTRING_COLS`.
const SUBSTRING_PARALLELISM: usize = 3;

/// Maximum bit-length for the longer sequence length in substring checks. This
/// value must be chosen lower or equal than `F::CAPACITY - 9`.
const PARSING_MAX_LEN_BITS: u32 = 64;

/// Number of advice columns for the scanner chip.
pub const NB_SCANNER_ADVICE_COLS: usize = {
    let automaton = NB_AUTOMATON_COLS * AUTOMATON_PARALLELISM;
    let substring = SUBSTRING_PARALLELISM * NB_SUBSTRING_COLS;
    if automaton > substring {
        automaton
    } else {
        substring
    }
};
/// Number of shared fixed columns necessary for the scanner chip.
pub const NB_SCANNER_FIXED_COLS: usize = 1;

type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// A simple map from the automaton structure to handle field elements, and thus
/// precompute all transition operations on the prover code.
#[derive(Clone, Debug)]
pub struct NativeAutomaton<F> {
    /// The number of states of the automaton.
    pub nb_states: usize,
    /// The initial state of the automaton.
    pub initial_state: F,
    /// The final states of the automaton.
    pub final_states: BTreeSet<F>,
    /// When `transitions[source_state][letter] = (target_state, marker)`, it
    /// means that in state `source_state`, upon reading the byte `letter`, the
    /// automaton run moves to state `target_state` and marks `letter` with
    /// `marker`. If the entry is undefined, the automaton run gets stuck.
    pub transitions: BTreeMap<F, BTreeMap<F, (F, F)>>,
}

impl<F> From<&Automaton> for NativeAutomaton<F>
where
    F: CircuitField + Ord,
{
    fn from(value: &Automaton) -> Self {
        let mut transitions = BTreeMap::new();
        for (&source, inner) in &value.transitions {
            let native_inner: BTreeMap<F, (F, F)> = inner
                .iter()
                .map(|(&letter, &(target, marker))| {
                    (
                        F::from(letter as u64),
                        (F::from(target as u64), F::from(marker as u64)),
                    )
                })
                .collect();
            transitions.insert(F::from(source as u64), native_inner);
        }

        let initial_state = F::from(value.initial_state as u64);
        let final_states: BTreeSet<F> =
            (value.final_states.iter()).map(|s| F::from(*s as u64)).collect();

        // Self-loop transitions on the filler letter (ALPHABET_MAX_SIZE) for
        // the initial and final states. These allow `parse_varlen` to skip
        // filler elements in [`ScannerVec`] buffers, and are also loaded into
        // the fixed lookup table unconditionally.
        let filler = F::from(ALPHABET_MAX_SIZE as u64);
        transitions
            .entry(initial_state)
            .or_default()
            .insert(filler, (initial_state, F::ZERO));
        for &state in &final_states {
            transitions.entry(state).or_default().insert(filler, (state, F::ZERO));
        }

        NativeAutomaton {
            nb_states: value.nb_states,
            initial_state,
            final_states,
            transitions,
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
    /// Looks up the transition from `state` reading `letter`.
    fn get_transition(&self, state: &F, letter: &F) -> Option<(F, F)> {
        self.transitions.get(state).and_then(|inner| inner.get(letter)).copied()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A reference for parsing methods for the function `parse`. Either an entry of
/// the static automaton library (more efficient, but limited library), or a
/// dynamic regular expression (more costly, but supports arbitrary regexes).
pub enum AutomatonParser {
    /// Static automaton library, as defined in `parsing::static_specs` (see the
    /// documentation of each object of type `StdLibParser` to get the exact
    /// regular expression they check). The off-circuit conversion
    /// Regex->Automaton has been pre-computed and is serialised.
    Static(StdLibParser),
    /// Parses an arbitrary regular expression. Induces the same circuit logic
    /// and performances as `Static`, but the conversion Regex->Automaton will
    /// be performed by the prover (off-circuit).
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

/// A static library of serialised automata for parsing common regexes. The
/// automaton states start from 0 and may overlap one with each other.
type ParsingLibrary = FxHashMap<StdLibParser, Automaton>;
/// Set of automata (with offset states) called by [`ScannerChip::parse`] or
/// [`ScannerChip::parse_varlen`].
type AutomatonCache<F> = FxHashMap<AutomatonParser, NativeAutomaton<F>>;
/// A sequence of assigned elements.
type Sequence<F> = Vec<AssignedNative<F>>;

/// Optional per-element padding flags for variable-length subs. When present,
/// filler positions (flag = true) are masked to zero during packing.
type PaddingFlags<F> = Option<Vec<AssignedBit<F>>>;

/// A cached sub entry: (idx, index offsets, sub content, padding flags).
/// Index offsets are additional `(coefficient, value)` terms folded into the
/// packing linear combination alongside `idx`, saving a dedicated row per sub.
type CachedSub<F> = (
    AssignedNative<F>,
    Vec<(F, AssignedNative<F>)>,
    Sequence<F>,
    PaddingFlags<F>,
);

/// Cache of assigned sequences passed as arguments to `check_subsequence` or
/// `check_subsequence_varlen`. Each sequence (keyed by its cells) is mapped to
/// the list of sub entries and the cumulative sub length.
///
/// **Cell-identity assumption**: the cache key is based on
/// [`AssignedCell`](`midnight_proofs::circuit::AssignedCell`) identity (column
/// and row), not on the cell's value. This means two sequences holding the same
/// byte values but assigned at different circuit positions are distinct cache
/// entries. Conversely, any construction that reuses the *same* cells (e.g. a
/// zero-cost wrapper around an existing buffer) would share the entry. Callers
/// that introduce new ways to build sequences must ensure fresh cells are
/// produced if a distinct cache entry is intended.
type SequenceCache<F> = FxHashMap<Sequence<F>, (Vec<CachedSub<F>>, usize)>;

/// Scanner gate configuration.
#[derive(Clone, Debug)]
pub struct ScannerConfig {
    // Shared advice columns used by scanner operations.
    advice_cols: [Column<Advice>; NB_SCANNER_ADVICE_COLS],

    /// Pre-computed library of automata. If some are not used in the circuit,
    /// their table will not be loaded wastingly.
    static_library: ParsingLibrary,

    // Automaton circuit resources.
    q_automaton: Selector,
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
pub struct ScannerChip<F>
where
    F: CircuitField,
{
    config: ScannerConfig,
    native_gadget: NG<F>,
    vector_gadget: VectorGadget<F>,

    /// Unified cache of all resolved automata (both static library and dynamic
    /// regexes), with their states already offset. Populated on demand by
    /// `resolve_automaton` when `parse` is called for the first time with a
    /// given `AutomatonParser`.
    automaton_cache: Rc<RefCell<AutomatonCache<F>>>,
    /// Tracks the next available state offset. Starts at 1 (state 0 is
    /// reserved as the dummy state for soundness).
    max_state: Rc<RefCell<usize>>,

    /// Cache mapping a sequence of cells to the list of `(idx, sub)` pairs
    /// it was called with, so that repeated `check_bytes` calls with the same
    /// `sequence` argument share the table cost. Tags are assigned later
    /// during finalisation.
    sequence_cache: Rc<RefCell<SequenceCache<F>>>,
}

impl<F> Chip<F> for ScannerChip<F>
where
    F: CircuitField,
{
    type Config = ScannerConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F> ComposableChip<F> for ScannerChip<F>
where
    F: CircuitField + Ord,
{
    type InstructionDeps = NG<F>;

    type SharedResources = (
        [Column<Advice>; NB_SCANNER_ADVICE_COLS],
        Column<Fixed>,
        FxHashMap<StdLibParser, Automaton>,
    );

    fn new(config: &ScannerConfig, deps: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            vector_gadget: VectorGadget::new(deps),
            native_gadget: deps.clone(),
            automaton_cache: Rc::new(RefCell::new(FxHashMap::default())),
            max_state: Rc::new(RefCell::new(1)),
            sequence_cache: Rc::new(RefCell::new(FxHashMap::default())),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> ScannerConfig {
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(
                AUTOMATON_PARALLELISM > 0 && SUBSTRING_PARALLELISM > 0,
                "at least 1 lookup required for automata and substring checks"
            );
            assert!(
                PARSING_MAX_LEN_BITS <= F::CAPACITY - (u8::BITS + 1),
                "check_subsequence batching exceeds field capacity ({} / {})",
                PARSING_MAX_LEN_BITS + u8::BITS + 1,
                F::CAPACITY
            )
        }

        let (advice_cols, index_col, automata) = shared_res;

        // Enable equality on all advice columns.
        for &col in advice_cols {
            meta.enable_equality(col);
        }

        // Automaton resources (shared fixed lookup table).
        let q_automaton = meta.complex_selector();
        let t_source = meta.lookup_table_column();
        let t_letter = meta.lookup_table_column();
        let t_target = meta.lookup_table_column();
        let t_output = meta.lookup_table_column();

        // Automaton lookup by batch: AUTOMATON_PARALLELISM transitions per row.
        for batch in 0..AUTOMATON_PARALLELISM {
            meta.lookup(
                format!("automaton transition check (batch {batch})"),
                |meta| {
                    let q = meta.query_selector(q_automaton);
                    let base = NB_AUTOMATON_COLS * batch;
                    let [source, letter, output] = core::array::from_fn(|i| {
                        meta.query_advice(advice_cols[base + i], Rotation::cur())
                    });
                    let target = if batch + 1 < AUTOMATON_PARALLELISM {
                        meta.query_advice(advice_cols[base + NB_AUTOMATON_COLS], Rotation::cur())
                    } else {
                        meta.query_advice(advice_cols[0], Rotation::next())
                    };
                    vec![
                        (q.clone() * source, t_source),
                        (q.clone() * letter, t_letter),
                        (q.clone() * target, t_target),
                        (q * output, t_output),
                    ]
                },
            );
        }

        // Substring resources.
        let tag_col = meta.fixed_column();
        let q_substring = meta.complex_selector();

        // Substring lookup arguments (see the `substring` module for full details).
        //
        // There are `SUBSTRING_PARALLELISM` independent lookup arguments, each
        // operating on 2 advice columns: `advice_cols[2*batch]` (table byte)
        // and `advice_cols[2*batch + 1]` (packed query), plus 2 shared fixed
        // columns: index and tag.
        //
        // Example: checking `wor` appears in `hello world` at index 6 (batch 0):
        //
        //    fixed          advice
        //    tag | index    cols[2*i] | cols[2*i+1]
        //    -----------    -----------------------
        //     1  |  0          'h'    | 257*6 + 'w'    <- query for sub[0]
        //     1  |  1          'e'    | 257*7 + 'o'    <- query for sub[1]
        //     1  |  2          'l'    | 257*8 + 'r'    <- query for sub[2]
        //     1  |  3          'l'    | (padding)
        //     1  |  4          'o'    | (padding)
        //     1  |  5          ' '    | (padding)
        //     1  |  6          'w'    | (padding)
        //     1  |  7          'o'    | (padding)
        //     1  |  8          'r'    | (padding)
        //     1  |  9          'l'    | (padding)
        //     1  | 10          'd'    | (padding)
        //
        // The packed query `257 * (idx + i) + sub[i]` is pre-computed in
        // circuit (see `index_and_pack_sequence` in `substring`). The table
        // packing is done in the expression below:
        //
        //     table_packed = 257 * index + table_byte
        //
        // The lookup checks: (tag, packed_query) ∈ {(tag, table_packed)}.
        //
        // When sel=OFF, both sides reduce to (tag, query) — a tautology, so
        // rows not used by substring checks are unconstrained.
        for batch in 0..SUBSTRING_PARALLELISM {
            meta.lookup_any(format!("substring lookup (batch {batch})"), |meta| {
                let sel = meta.query_selector(q_substring);
                let not_sel = Expression::Constant(F::ONE) - sel.clone();
                let index = meta.query_fixed(*index_col, Rotation::cur());
                let tag = meta.query_fixed(tag_col, Rotation::cur());
                let shift = Expression::Constant(F::from(ALPHABET_MAX_SIZE as u64 + 1));

                let base = NB_SUBSTRING_COLS * batch;
                let table = meta.query_advice(advice_cols[base], Rotation::cur());
                let query = meta.query_advice(advice_cols[base + 1], Rotation::cur());

                vec![
                    (tag.clone(), sel.clone() * tag.clone()),
                    (
                        query.clone(),
                        sel * (index * shift + table) + not_sel * query,
                    ),
                ]
            });
        }

        ScannerConfig {
            advice_cols: *advice_cols,
            static_library: automata.clone(),
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

    /// Loads the automaton transition table and finalises all deferred
    /// substring checks. Must be called at the end of circuit synthesis.
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.load_automata_table(layouter)?;
        self.finalise_substring_checks(layouter)
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
impl<F> FromScratch<F> for ScannerChip<F>
where
    F: CircuitField + Ord,
{
    type Config = (P2RDecompositionConfig, ScannerConfig);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let max_bit_len = 8;
        let native_chip = NativeChip::new(&config.0.native_config, &());
        let core_decomposition_chip = P2RDecompositionChip::new(&config.0, &max_bit_len);
        let native_gadget = NG::<F>::new(core_decomposition_chip, native_chip);
        <ScannerChip<F> as ComposableChip<F>>::new(&config.1, &native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let nb_advice_cols = std::cmp::max(NB_SCANNER_ADVICE_COLS, NB_ARITH_COLS);
        let advice_cols = (0..nb_advice_cols).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed_cols = (0..NB_ARITH_COLS + 4).map(|_| meta.fixed_column()).collect::<Vec<_>>();

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
                FxHashMap::default(),
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

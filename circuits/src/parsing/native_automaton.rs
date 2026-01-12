//! Post-processing of (minimised) automata for circuit uses. This includes:
//!
//! 1. Parsing several bytes at once
//! 2. Converting a collection of automata into a single automaton with several
//!    initial states but a unique transition table.
//! 3. Converting the automaton data into native field elements.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    hash::Hash,
};

use ff::PrimeField;
#[cfg(test)]
use itertools::Itertools;
#[cfg(test)]
use rustc_hash::FxBuildHasher;
use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(test)]
use crate::parsing::automaton::Automaton;
use crate::parsing::{
    automaton::{Marker, ALPHABET_MAX_SIZE},
    AUTOMATON_CHUNK_SIZE,
};

/// Value used to represent empty bytes representing padding cells after a final
/// state is parsed.
pub(crate) const AUTOMATON_FINAL_PADDING: usize = ALPHABET_MAX_SIZE;

#[cfg(test)]
/// Transitions reading multiple bytes in a row. `None` represents a padding, in
/// case the size of the input is not a multiple of `AUTOMATON_CHUNK_SIZE`.
type PartiallyChunkedTransitions =
    FxHashMap<usize, FxHashMap<Vec<Option<u8>>, (usize, Vec<Marker>)>>;

/// Transitions reading `AUTOMATON_CHUNK_SIZE` bytes in a row.
type ChunkedTransitions = FxHashMap<
    usize,
    FxHashMap<[Option<u8>; AUTOMATON_CHUNK_SIZE], (usize, [Marker; AUTOMATON_CHUNK_SIZE])>,
>;

/// The native-field version of `ChunkedTransition`.
type NativeTransitions<F> =
    BTreeMap<F, BTreeMap<[F; AUTOMATON_CHUNK_SIZE], (F, [F; AUTOMATON_CHUNK_SIZE])>>;

#[derive(Debug, Clone)]
/// An automaton one or more bytes at the same time.
pub struct ChunkAutomaton {
    /// Upper bound on the number of states appearing in the automaton.
    pub nb_states: usize,
    /// The initial state of the automaton.
    pub initial_state: usize,
    /// The final states of the automaton.
    pub final_states: FxHashSet<usize>,
    /// Similar to the `transitions` field of `Automaton`, except that
    /// `1 + chunk_size` bytes are read at once.
    pub transitions: ChunkedTransitions,
}

/// A simple map from the automaton structure to handle field elements, and thus
/// precompute all transition operations on the prover code.
#[derive(Clone, Debug)]
pub struct NativeAutomaton<F> {
    /// Upper bound on the number of states of the automaton.
    nb_states: usize,
    /// The initial state of the automaton.
    pub initial_state: F,
    /// The final states of the automaton.
    pub final_states: BTreeSet<F>,
    /// When `transitions[(source_state,letter)] = (target_state,marker)`, it
    /// means that in state `source_state`, upon reading the byte `letter`, the
    /// automaton run moves to state `target_state` and marks `letter` with
    /// `marker`. If the entry is undefined, the automaton run gets stuck.
    pub transitions: NativeTransitions<F>,
}

#[cfg(test)]
impl Automaton {
    /// Takes a regular `Automaton`, and transforms its transition table to read
    /// `chunk_size` input bytes at each step.
    ///
    /// # Panics
    ///
    /// If `chunk_size > AUTOMATON_CHUNK_SIZE` or `chunk_size == 0`.
    pub(crate) fn chunked(&self) -> ChunkAutomaton {
        let mut transitions = (self.transitions.iter())
            .map(|(source, successors)| {
                let new_successors = (successors.iter())
                    .map(|(byte, (target, marker))| (vec![Some(*byte)], (*target, vec![*marker])))
                    .collect::<FxHashMap<_, _>>();
                (*source, new_successors)
            })
            .collect::<FxHashMap<_, _>>();

        #[allow(clippy::reversed_empty_ranges)]
        for _ in 2..=AUTOMATON_CHUNK_SIZE {
            let mut incremented_transitions: PartiallyChunkedTransitions =
                FxHashMap::with_capacity_and_hasher(transitions.capacity(), FxBuildHasher);
            let mut increment = |source: usize,
                                 bytes: &[Option<u8>],
                                 new_byte: Option<u8>,
                                 target: usize,
                                 markers: &[Marker],
                                 new_marker: Marker| {
                let mut new_bytes = bytes.to_vec();
                new_bytes.push(new_byte);
                let mut new_markers = markers.to_vec();
                new_markers.push(new_marker);
                incremented_transitions
                    .entry(source)
                    .or_default()
                    .insert(new_bytes, (target, new_markers));
            };

            for (source, successors) in &transitions {
                for (bytes, (target, markers)) in successors {
                    if let Some(next_steps) = self.transitions.get(target) {
                        // Appending the successors of `target` to the current transition.
                        for (byte, (next, marker)) in next_steps {
                            increment(*source, bytes, Some(*byte), *next, markers, *marker);
                        }
                    }
                    if self.final_states.contains(target) {
                        // We are reaching a final state, meaning the run must have the
                        // possibility to stop there, in addition to the above transition
                        // extensions. Therefore, filling with specific padding
                        // bytes.
                        increment(*source, bytes, None, *target, markers, Marker::from(0))
                    }
                }
            }
            transitions = incremented_transitions;
        }

        // Converting the final vectors into arrays.
        let transitions: ChunkedTransitions = transitions
            .iter()
            .map(|(source, succ)| {
                let new_succ = succ
                    .iter()
                    .map(|(letters, (target, markers))| {
                        (
                            letters.clone().try_into().unwrap(),
                            (*target, markers.clone().try_into().unwrap()),
                        )
                    })
                    .collect::<FxHashMap<_, _>>();
                (*source, new_succ)
            })
            .collect::<FxHashMap<_, _>>();

        ChunkAutomaton {
            nb_states: self.nb_states,
            initial_state: self.initial_state,
            final_states: self.final_states.clone(),
            transitions,
        }
    }
}

#[cfg(test)]
impl ChunkAutomaton {
    /// Converts an input (vector of raw bytes) in a form that can be read by a
    /// `ChunkAutomaton`.
    fn chunk_and_pad_input(&self, input: &[u8]) -> Vec<[Option<u8>; AUTOMATON_CHUNK_SIZE]> {
        (input.iter().map(|b| Some(*b)).chunks(AUTOMATON_CHUNK_SIZE))
            .into_iter()
            .map(|c| {
                c.pad_using(AUTOMATON_CHUNK_SIZE, |_| None)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<_>>()
    }

    /// For a given state and a (padded) chunk of input letters, returns the
    /// next state in the transition table of `self`, if any, and the markers
    /// for each byte of `letters` (except padding bytes).
    fn get(
        &self,
        state: usize,
        letters: &[Option<u8>; AUTOMATON_CHUNK_SIZE],
    ) -> Option<(usize, Vec<Marker>)> {
        self.transitions.get(&state).and_then(|succ| {
            succ.get(letters).map(|(target, markers)| {
                let real_markers = (markers.iter().zip(letters.iter()))
                    .filter_map(|(m, a)| if a.is_some() { Some(*m) } else { None })
                    .collect::<Vec<_>>();
                (*target, real_markers)
            })
        })
    }

    /// Executes an automaton for a given sequence of bytes. Returns a vector of
    /// states (corresponding to the states of the run), a vector of bytes (the
    /// output of markers for this input), and a boolean indicating whether the
    /// run was stuck.
    pub(crate) fn run(&self, input: &[u8]) -> (Vec<usize>, Vec<Marker>, bool) {
        let input = self.chunk_and_pad_input(input);
        let mut iter = input.iter();
        let mut current_state = self.initial_state;
        let mut output = Vec::with_capacity(input.len());
        let mut states = Vec::with_capacity(input.len() + 1);
        let mut letter = iter.next();
        states.push(current_state);
        // Iterates over the letters of the input and moves accross the states
        // accordingly.
        while let Some(a) = letter {
            match self.get(current_state, a) {
                // Interrupted run.
                None => return (states, Vec::new(), true),
                // The run goes on.
                Some((state, marker)) => {
                    current_state = state;
                    states.push(current_state);
                    output.extend(marker);
                    letter = iter.next();
                }
            }
        }
        (states, output, false)
    }
}

impl ChunkAutomaton {
    /// Converts a `ChunkAutomaton` transition into a `NativeAutomaton` one.
    fn encode_transition<F: PrimeField>(
        source: usize,
        letters: &[Option<u8>],
        target: usize,
        markers: &[Marker],
    ) -> (F, [F; AUTOMATON_CHUNK_SIZE], F, [F; AUTOMATON_CHUNK_SIZE]) {
        (
            F::from(source as u64),
            letters
                .iter()
                .map(|b| F::from(b.map(u64::from).unwrap_or(AUTOMATON_FINAL_PADDING as u64)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            F::from(target as u64),
            markers
                .iter()
                .map(|m| F::from(u8::from(*m) as u64))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        )
    }

    /// Shifts the value of all states of `self` by a constant offset.
    fn offset_states(&self, offset: usize) -> Self {
        let transitions = (self.transitions.clone().into_iter())
            .map(|(source, succ)| {
                let new_succ = (succ.into_iter())
                    .map(|(letters, (target, markers))| (letters, (target + offset, markers)))
                    .collect::<FxHashMap<_, _>>();
                (source + offset, new_succ)
            })
            .collect::<FxHashMap<_, _>>();
        Self {
            nb_states: self.nb_states,
            initial_state: self.initial_state + offset,
            final_states: self.final_states.iter().map(|s| s + offset).collect(),
            transitions,
        }
    }
}

impl<F> From<&ChunkAutomaton> for NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from(automaton: &ChunkAutomaton) -> Self {
        let mut transitions: NativeTransitions<F> = BTreeMap::new();
        for (source, successors) in automaton.transitions.iter() {
            for (letters, (target, markers)) in successors.iter() {
                let (source, letters, target, markers) =
                    ChunkAutomaton::encode_transition(*source, letters, *target, markers);
                transitions.entry(source).or_default().insert(letters, (target, markers));
            }
        }
        Self {
            nb_states: automaton.nb_states,
            initial_state: F::from(automaton.initial_state as u64),
            final_states: (automaton.final_states.iter())
                .map(|s| F::from(*s as u64))
                .collect::<BTreeSet<_>>(),
            transitions,
        }
    }
}

impl<F> From<ChunkAutomaton> for NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from(value: ChunkAutomaton) -> Self {
        (&value).into()
    }
}

impl<F> NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    /// Converts an indexed collection of automata to a collection of native
    /// automata. Each automaton comes with a `usize` indicating how many bytes
    /// it will read at a byte. Regular automata read 1 byte at a time; and the
    /// more bytes are simultaneously read, the bigger the transition table,
    /// but also the fewer rows are needed to parse an input.
    pub(crate) fn from_collection<LibIndex>(
        automata: &FxHashMap<LibIndex, ChunkAutomaton>,
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
                offset += na.nb_states;
                (*name, na)
            })
            .collect::<FxHashMap<_, _>>()
    }
}

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
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};

use crate::parsing::automaton::{Automaton, Marker, ALPHABET_MAX_SIZE};

/// Element that is used to pad incomplete sequences of parsed bytes. For
/// example, if an automaton is reading an input of 10 bytes, 4 bytes at a time,
/// the inputs will need to be padded by 2. The chosen value is done so that it
/// is not a valid `u8`.
const AUTOMATON_CHUNK_PADDING: usize = ALPHABET_MAX_SIZE;

/// Transitions reading multiple bytes in a row.
type ChunkedTransition = FxHashMap<usize, FxHashMap<Vec<Option<u8>>, (usize, Vec<Marker>)>>;

#[derive(Debug, Clone)]
/// An automaton one or more bytes at the same time.
pub struct ChunkAutomaton {
    /// How many bytes are read by automaton transition (1 is a regular
    /// automaton).
    pub chunk_size: u32,
    /// Upper bound on the number of reachable states.
    pub nb_states: usize,
    /// The initial state of the automaton.
    pub initial_state: usize,
    /// The final states of the automaton.
    pub final_states: FxHashSet<usize>,
    /// Similar to the `transitions` field of `Automaton`, except that
    /// `1 + chunk_size` bytes are read at once.
    pub transitions: ChunkedTransition,
}

impl Automaton {
    pub fn chunked(self, chunk_size: u32) -> ChunkAutomaton {
        assert!(
            chunk_size != 0,
            "Automata have to read at least 1 byte at a time"
        );
        let mut transitions = (self.transitions.iter())
            .map(|(source, successors)| {
                let new_successors = (successors.iter())
                    .map(|(byte, (target, marker))| (vec![Some(*byte)], (*target, vec![*marker])))
                    .collect::<FxHashMap<_, _>>();
                (*source, new_successors)
            })
            .collect::<FxHashMap<_, _>>();

        for _ in 1..chunk_size {
            let mut incremented_transitions: ChunkedTransition =
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
                    if self.final_states.contains(target) {
                        increment(*source, bytes, None, *target, markers, Marker::from(0))
                    }
                    if let Some(next_steps) = self.transitions.get(target) {
                        for (byte, (next, marker)) in next_steps {
                            increment(*source, bytes, Some(*byte), *next, markers, *marker)
                        }
                    }
                }
            }
            transitions = incremented_transitions;
        }

        ChunkAutomaton {
            chunk_size,
            nb_states: self.nb_states,
            initial_state: self.initial_state,
            final_states: self.final_states,
            transitions,
        }
    }
}

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

impl<F: PrimeField> From<&ChunkAutomaton> for NativeAutomaton<F> {
    fn from(automaton: &ChunkAutomaton) -> Self {
        assert!(
            automaton.chunk_size * u8::BITS <= F::CAPACITY,
            "cannot store"
        );
        todo!()
    }
}

impl<F> From<&Automaton> for NativeAutomaton<F>
where
    F: PrimeField + Ord,
{
    fn from(value: &Automaton) -> Self {
        let mut transitions = BTreeMap::new();
        for (&source, successors) in value.transitions.iter() {
            for (&byte, &(target, marker)) in successors {
                transitions.insert(
                    (F::from(source as u64), F::from(byte as u64)),
                    (F::from(target as u64), F::from(u8::from(marker) as u64)),
                );
            }
        }
        NativeAutomaton {
            initial_state: F::from(value.initial_state as u64),
            final_states: (value.final_states.iter())
                .map(|s| F::from(*s as u64))
                .collect::<BTreeSet<_>>(),
            transitions,
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
    pub(crate) fn from_collection<LibIndex>(
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

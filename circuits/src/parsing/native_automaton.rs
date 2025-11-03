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

use crate::parsing::automaton::Automaton;


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

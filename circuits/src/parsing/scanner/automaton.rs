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

// This module implements a basic library for the conversion of regular
// expressions (as defined in `regex.rs`) into deterministic finite automata
// (DFA). It proceeds as follows:
//
//  - `Regex` -> `RawAutomaton` (non-deterministic automaton). This does not
//    enforce minimality, or determinism (i.e., multiple transitions from the
//    same state may be labelled with the same byte, or no byte at all).
//
//  - `RawAutomaton` -> `Automaton` (deterministic automaton). Uses the standard
//    powerset construction to construct a normalised automaton whose
//    transitions are represented by a `HashMap`. Dead states are also removed
//    with `RawAutomaton::remove_dead_states`.
//
//  - `Automaton.minimise` (minimisation). Implements Hopcroft's algorithm to
//    compute the Nerode's congruence of the automaton. It intuitively detects
//    states that are indistinguishable, and merges them to yield a smaller
//    transition table.
//
// The module also implements a couple of tests with a minimal alphabet (only
// bytes 0,1,2 are allowed) to check the validity of the constructions.

use std::{collections::hash_map::Entry, fmt::Debug, hash::Hash, iter::once};

use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};

/// Maximal size of the alphabet of an automaton/regex, since input characters
/// are represented by `AssignedByte`. The parser (`automaton_chip::parse`) is
/// using this information to store automaton final states in the transition
/// table, by encoding them as impossible transitions starting from the said
/// state, and labelled with letter `ALPHABET_MAX_SIZE`. This bound is also
/// needed to represent letters as u8.
pub const ALPHABET_MAX_SIZE: usize = 256;

/// A letter from the automaton alphabet. Includes output markers.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Letter {
    /// The actual byte represented by the letter.
    pub char: u8,
    /// The potential marker of the letter. By convention, 0 means no marker.
    pub marker: usize,
}

impl From<u8> for Letter {
    fn from(value: u8) -> Self {
        Letter {
            char: value,
            marker: 0,
        }
    }
}

impl From<&u8> for Letter {
    fn from(value: &u8) -> Self {
        (*value).into()
    }
}

impl Letter {
    /// Encodes a `Letter` bijectively as a usize, in order to use them more
    /// easily as vector indexes. The size of the encoding is polynomial in the
    /// number of different markers and the alphabet size.
    pub fn encode(&self, alphabet_size: usize, markers: &[usize]) -> usize {
        let marker = markers.iter().enumerate().find(|(_, &m)| m == self.marker).unwrap().0;
        marker * alphabet_size + self.char as usize
    }

    /// Inverse function of `Letter::encode`.
    pub fn decode(letter_encoding: usize, alphabet_size: usize, markers: &[usize]) -> Self {
        Letter {
            char: (letter_encoding % alphabet_size) as u8,
            marker: markers[letter_encoding / alphabet_size],
        }
    }

    /// Maximal output of the function `Letter::encode`.
    pub fn encoding_bound(alphabet_size: usize, markers: &[usize]) -> usize {
        alphabet_size * markers.len()
    }
}

/// A type for non-deterministic finite automata with a parametric type to
/// represent its states.
#[derive(Clone, Debug)]
pub(super) struct RawAutomaton {
    /// Indicator of whether the automaton is deterministic.
    deterministic: bool,
    /// Indicator of whether the automaton is complete.
    complete: bool,
    /// The initial state of the automaton.
    initial_state: usize,
    /// The final states of the automaton.
    final_states: FxHashSet<usize>,
    /// The set of transitions, where `self.transitions[state]` is the vector of
    /// successors (i.e., pairs (letter, target state)) of the state `state`.
    /// The vector will always have one entry per state (even if no transitions
    /// start from this state). In particular, `self.transition.len()` is the
    /// number of states of `self`.
    ///
    /// At this stage, this transition table is simply a
    /// collection of transitions with no check of redundancy or
    /// determinism. This will be handled during the conversion into the
    /// more structured type `Automaton`.
    transitions: Vec<Vec<(Letter, usize)>>,
    /// All markers effectively used in the automaton.
    markers: FxHashSet<usize>,
}

/// Type for representing reachability graphs for automata, that is, its set of
/// transitions without letters.
type ReachGraph = Vec<FxHashSet<usize>>;

/// A normalised model of a deterministic (but not necessarily complete) finite
/// automaton operating on bytes. The set of states is implicitly represented by
/// the range `0..nb_states`.
#[derive(Clone, Debug)]
pub struct Automaton {
    /// Upper bound on the number of reachable states.
    pub nb_states: usize,
    /// The initial state of the automaton.
    pub initial_state: usize,
    /// The final states of the automaton.
    pub final_states: FxHashSet<usize>,
    /// `transitions.get(state,byte)` returns the transition target and its
    /// marker upon reading input `byte` in state `state`. A key may be
    /// undefined, in which case it means the automaton jumps into an
    /// implicit deadlock state.
    ///
    /// Note: For this hashmap, we use a fast but non cryptographically secure
    /// hasher (`FxBuildHasher`). This has no effect on soundness, apart from
    /// the `serialization` module relying on this hasher's determinism for
    /// testing purposes. Still, one could theoretically construct an automaton
    /// inducing a lot of collisions, making its circuit configuration
    /// abnormally slow. This however has no effect on the verifier time, and
    /// does not affect users that only access the parsers we provide
    /// through the standard library.
    pub transitions: FxHashMap<(usize, u8), (usize, usize)>,
}

// Basic automaton constructions.
impl RawAutomaton {
    /// Creates an empty automaton with a unique default state.
    pub(super) fn empty() -> Self {
        Self {
            deterministic: true,
            complete: false,
            initial_state: 0,
            final_states: FxHashSet::default(),
            transitions: vec![vec![]],
            markers: FxHashSet::default(),
        }
    }

    /// Creates an automaton recognising only the empty word.
    pub(super) fn epsilon() -> Self {
        Self {
            deterministic: true,
            complete: false,
            initial_state: 0,
            final_states: FxHashSet::from_iter([0]),
            transitions: vec![vec![]],
            markers: FxHashSet::default(),
        }
    }

    /// An automaton that accepts a finite concatenation of disjunctions of
    /// bytes. The alphabet size can be specified, which effectively filters
    /// out any transition involving a byte outside of the alphabet.
    pub(super) fn byte_concat(word: &[Vec<Letter>], alphabet_size: usize) -> Self {
        let mut transitions = word
            .iter()
            .map(Vec::len)
            .map(Vec::with_capacity)
            .chain(once(vec![]))
            .collect::<Vec<_>>();
        let mut markers = FxHashSet::default();
        for (position, byte_range) in word.iter().enumerate() {
            for byte in byte_range {
                if (byte.char as usize) < alphabet_size {
                    markers.insert(byte.marker);
                    transitions[position].push((*byte, position + 1));
                }
            }
        }
        Self {
            deterministic: true,
            complete: false,
            initial_state: 0,
            final_states: FxHashSet::from_iter([word.len()]),
            transitions,
            markers,
        }
    }

    /// Creates an automaton accepting any unmarked word.
    pub(super) fn universal(alphabet_size: usize) -> Self {
        assert!(
            alphabet_size <= ALPHABET_MAX_SIZE,
            "attempt to construct an automaton with an alphabet of size {alphabet_size} (will overflow u8)"
        );
        Self {
            deterministic: true,
            complete: true,
            initial_state: 0,
            final_states: FxHashSet::from_iter([0]),
            transitions: Vec::from_iter([(0..alphabet_size)
                .map(|b| ((b as u8).into(), 0))
                .collect::<Vec<_>>()]),
            markers: FxHashSet::default(),
        }
    }

    /// Creates an automaton recognising the same language as `self` + the empty
    /// word epsilon. As this operation is quite common, saving even one state
    /// in this construction can have an observable effect on the load of the
    /// final minimisation of a big regex.
    ///
    /// Since the modification to the automaton are often small, this function
    /// operates by mutating the argument to avoid cloning the entire structure.
    pub(super) fn make_optional(self) -> Self {
        // If the initial state is already final, the automaton already accepts epsilon
        // and there is nothing to do.
        if !self.final_states.contains(&self.initial_state) {
            if self.loop_on_initial() {
                // If there exists a cycle of transitions from the initial state to itself, we
                // add a fresh state with the same outgoing transitions. The previous initial
                // state is not removed, but the fresh state becomes the new initial state, and
                // is also final to accept epsilon while avoiding cycles.
                let initial_state = self.transitions.len();
                let mut final_states = self.final_states;
                let mut transitions = self.transitions;
                final_states.insert(initial_state);
                transitions.push(transitions[self.initial_state].clone());
                Self {
                    initial_state,
                    final_states,
                    transitions,
                    ..self
                }
            } else {
                let mut final_states = self.final_states;
                // If the initial state cannot reach itself non-trivially, marking it as a final
                // state only adds epsilon to the language.
                final_states.insert(self.initial_state);
                Self {
                    final_states,
                    ..self
                }
            }
        } else {
            self
        }
    }
}

// Functions for graph analysis in automata.

/// Computes the reverse graph of a simplified automaton graph.
fn reverse_graph(graph: &ReachGraph) -> ReachGraph {
    let mut backward_edges = vec![FxHashSet::default(); graph.len()];
    for (source, succ) in graph.iter().enumerate() {
        for &target in succ {
            backward_edges[target].insert(source);
        }
    }
    backward_edges
}

impl RawAutomaton {
    /// Computes the simplified reachability graph of an automaton, i.e., the
    /// transitions without letters. Computing once and for all a simplified
    /// graph tends to make the code more efficient when the transition table
    /// has to be traversed many times, since there are often 10~100 transitions
    /// between the same two states.
    fn simplified_graph(&self) -> ReachGraph {
        let mut forward_edges = vec![FxHashSet::default(); self.transitions.len()];
        for (source, succ) in self.transitions.iter().enumerate() {
            for (_, target) in succ {
                forward_edges[source].insert(*target);
            }
        }
        forward_edges
    }

    /// Computes the set of states of an automaton that are both reachable from
    /// the initial state, and can reach a final state.
    fn live_states(&self) -> FxHashSet<usize> {
        let forward_edges = self.simplified_graph();
        let backward_edges = reverse_graph(&forward_edges);
        let mut visited =
            FxHashSet::with_capacity_and_hasher(self.transitions.len(), FxBuildHasher);
        let mut pending = Vec::with_capacity(self.transitions.len());

        // Computing forward reachable states.
        pending.push(self.initial_state);
        while let Some(state) = pending.pop() {
            if visited.insert(state) {
                pending.extend(forward_edges[state].iter());
            }
        }
        // Refining with backward reachable states.
        let mut live = FxHashSet::with_capacity_and_hasher(self.transitions.len(), FxBuildHasher);
        let reachable = visited.clone();
        pending.clear();
        visited.clear();
        pending.extend(&self.final_states);
        while let Some(state) = pending.pop() {
            if visited.insert(state) && reachable.contains(&state) {
                live.insert(state);
                pending.extend(backward_edges[state].iter());
            }
        }
        live
    }

    /// Checks if the graph contains a self loop on `self.initial_state`. Under
    /// the assumption that all states of the automaton are reachable (invariant
    /// of `Regex::to_automaton_serialized`), it suffices to check whether there
    /// exists a transition pointing to the initial state.
    fn loop_on_initial(&self) -> bool {
        self.transitions
            .iter()
            .any(|succ| succ.iter().any(|(_, target)| *target == self.initial_state))
    }

    /// Checks whether final states have no successors.
    fn nothing_after_final(&self) -> bool {
        self.final_states.iter().all(|&state| self.transitions[state].is_empty())
    }
}

// Post processing of automata handling the aftermath of a suboptimal operation.
impl RawAutomaton {
    /// Updates the set of transitions of an automaton accordingly to an update
    /// function. If the update function returns `None` on a given state, all
    /// transitions involving it are removed. The set of markers is then
    /// recomputed to reflect any removals.
    ///
    /// The function additionally takes the minimal value of the updated
    /// states (`offset`) to simplify construction of the transition table.
    fn filter_map_transitions(
        transitions: &[Vec<(Letter, usize)>],
        f: impl Fn(usize) -> Option<usize>,
        new_nb_states: usize,
        offset: usize,
    ) -> (Vec<Vec<(Letter, usize)>>, FxHashSet<usize>) {
        let mut new_transitions = vec![vec![]; new_nb_states];
        let mut markers = FxHashSet::default();
        for (source, succ) in transitions.iter().enumerate() {
            for (letter, target) in succ {
                f(source).map(|new_source| {
                    f(*target).map(|new_target| {
                        markers.insert(letter.marker);
                        new_transitions[new_source - offset].push((*letter, new_target));
                    })
                });
            }
        }
        (new_transitions, markers)
    }

    /// Removes non reachable states, or states that are not backward-reachable
    /// from the final states. Preserves determinism but *not* completeness,
    /// since dead states are removed; therefore the field `complete` is set to
    /// `false`.
    ///
    /// Also updates the `markers` field to account for some markers potentially
    /// disappearing from the transition table.
    fn remove_dead_states(self) -> Self {
        // The goal is to restrict the states and transitions of `self` to those
        // appearing in `live_states`.
        let live_states = self.live_states();
        // Handling this case separately, so that in the rest of the code, we can assume
        // that at least the initial state is live.
        if live_states.is_empty() {
            return Self::empty();
        }
        // Maps bijectively each live state to an integer in `0..live_states.len()`.
        let renaming = live_states
            .iter()
            .enumerate()
            .map(|(index, &elt)| (elt, index))
            .collect::<FxHashMap<_, _>>();
        let initial_state = *renaming.get(&self.initial_state).unwrap();
        let final_states = self
            .final_states
            .iter()
            .filter_map(|state| renaming.get(state).copied())
            .collect::<FxHashSet<_>>();
        let (transitions, markers) = RawAutomaton::filter_map_transitions(
            &self.transitions,
            |state| renaming.get(&state).copied(),
            live_states.len(),
            0,
        );

        // The automaton may still be complete in the rare cases, but checking
        // completeness probably is likely more costly than just re-completing the
        // automaton in the (very few) cases where it is required. So the flag is set to
        // `false` for simplicity.
        Self {
            deterministic: self.deterministic,
            complete: false,
            initial_state,
            final_states,
            transitions,
            markers,
        }
    }

    /// Checks if an automaton is deterministic. If the field `deterministic` is
    /// set to true, nothing is done; otherwise, this function scans the
    /// transition table to rule out a potential false negative.
    ///
    /// If a successful check is performed, the `determinisitc` field is
    /// updated.
    pub(super) fn check_determinism(self) -> Self {
        Self {
            deterministic: self.deterministic
                || self.transitions.iter().all(|succ| {
                    let mut seen = FxHashSet::with_capacity_and_hasher(succ.len(), FxBuildHasher);
                    succ.iter().all(|(letter, _)| seen.insert(letter))
                }),
            ..self
        }
    }
}

// Implementation of determinisation.
impl RawAutomaton {
    /// Performs the powerset construction for `self`, assuming
    /// `self.transition` as a transition table, and all states of `initials` as
    /// initial state. Then assigns the final result to `self`.
    ///
    /// Note: if `completion` is set to false, the automaton is guaranteed not
    /// to have dead states if `self` did not have any either.
    fn powerset_construction(
        self,
        initials: &[usize],
        completion: bool,
        alphabet_size: usize,
    ) -> Self {
        // States of the new deterministic automaton are represented by sets of states
        // of `self`. These sets are represented by bitsets.
        let mut initial_state = vec![false; self.transitions.len()];
        initials.iter().for_each(|&s| initial_state[s] = true);
        let mut state_counter = 0;

        // A Map recording the visited states of the new automaton, mapping them
        // injectively to an integer for renaming purpose at the end.
        let mut visited =
            FxHashMap::with_capacity_and_hasher(self.transitions.len(), FxBuildHasher);

        // The list of states that remain to be handled by the transition generation.
        let mut pending = Vec::with_capacity(self.transitions.len());
        pending.push(initial_state);

        // Storage for the transitions and final states of the new automaton.
        let mut power_transitions = Vec::with_capacity(self.transitions.len());
        let mut final_states =
            FxHashSet::with_capacity_and_hasher(self.final_states.len(), FxBuildHasher);
        let markers = Vec::from_iter(self.markers.clone());

        while let Some(power_state) = pending.pop() {
            if let Entry::Vacant(entry) = visited.entry(power_state.clone()) {
                // A never-encountered state of the new automaton. So, we check whether it is
                // final (i.e., if the bitset contains a final state), and
                // increment the counter.
                if self.final_states.iter().any(|state| power_state[*state]) {
                    final_states.insert(state_counter);
                }
                entry.insert(state_counter);
                state_counter += 1;

                // Generation of the transitions starting from `power_state` in the new
                // automaton. For each letter, `power_state` is potentially mapped to the
                // set of states `target` such that a transition `(source,letter,target)`
                // exists in `self` with `source` in `power_state`.
                let mut successors = if completion {
                    // In case completion is required, we initialise a successor for all possible
                    // marked Letter.
                    (0..Letter::encoding_bound(alphabet_size, &markers))
                        .map(|i| (i, vec![false; self.transitions.len()]))
                        .collect::<FxHashMap<_, _>>()
                } else {
                    // Otherwise, the capacity of the HashMap is chosen so that it cover most common
                    // cases (letters marked 0), and marked letters will require a reallocation.
                    FxHashMap::with_capacity_and_hasher(alphabet_size, FxBuildHasher)
                };
                for (source, b) in power_state.iter().enumerate() {
                    if *b {
                        // Marking all successors of `source` in `self.transitions` as true in the
                        // powerset successor of `power_state`.
                        for (letter, target) in &self.transitions[source] {
                            successors
                                .entry(letter.encode(alphabet_size, &markers))
                                .or_insert(vec![false; self.transitions.len()])[*target] = true
                        }
                    }
                }
                successors.iter().for_each(|(&letter_encoding, target)| {
                    let letter = Letter::decode(letter_encoding, alphabet_size, &markers);
                    power_transitions.push((power_state.clone(), letter, target.clone()));
                    pending.push(target.clone());
                })
            }
        }

        // Replacing powerset transitions with their numbered version.
        let mut transitions = vec![vec![]; state_counter];
        for (source, letter, target) in &power_transitions {
            let (source, target) = visited
                .get(source)
                .zip(visited.get(target))
                .expect("determinisation did not label states correctly");
            transitions[*source].push((*letter, *target));
        }
        Self {
            deterministic: true,
            complete: self.complete || completion,
            initial_state: 0,
            final_states,
            transitions,
            markers: self.markers,
        }
    }

    /// Computes a deterministic version of an automaton, using the powerset
    /// construction.
    pub(super) fn determinise(self, completion: bool, alphabet_size: usize) -> Self {
        if self.deterministic && (!completion || self.complete) {
            self
        } else {
            let initial_state = &[self.initial_state];
            self.powerset_construction(initial_state, completion, alphabet_size)
        }
    }
}

// Implementation of automaton combination operations.
impl RawAutomaton {
    /// Computes the union of a collection of automata.
    ///
    /// The automaton is obtained by alpha-renaming all states of the different
    /// automata to avoid collisions (a state `s` of automata number `i` will be
    /// represented by `s + offsets[i]`). Then the final automaton is simply
    /// obtained by performing a powerstate construction whose initial state
    /// is the set of all initial states of the original automaton.
    pub(super) fn union(automata: &[Self], alphabet_size: usize) -> Self {
        if automata.len() == 1 {
            // Avoids determinising automaton in this case. Happens often due to the
            // pre-processing performed by `Regex::flatten_union`.
            return automata[0].clone();
        }
        let mut union_automaton = RawAutomaton::empty();
        let mut union_initial_states = Vec::with_capacity(automata.len());
        for automaton in automata {
            let nb_states = union_automaton.transitions.len();
            let (transitions, markers) = RawAutomaton::filter_map_transitions(
                &automaton.transitions,
                |state| Some(state + nb_states),
                automaton.transitions.len(),
                nb_states,
            );
            union_initial_states.push(automaton.initial_state + nb_states);
            union_automaton
                .final_states
                .extend(automaton.final_states.iter().map(|state| state + nb_states));
            union_automaton.markers.extend(markers);
            union_automaton.transitions.extend(transitions);
        }
        union_automaton.powerset_construction(&union_initial_states, false, alphabet_size)
    }

    /// Computes an automaton for the concatenation of an arbitrary number of
    /// languages.
    ///
    /// Renames states of the automata to ensure they are disjoint and, in
    /// general, simply plugs the final states of each automata to the
    /// initial state of the subsequent one. Removes some dead states when
    /// these final states have no successors.
    pub(super) fn concat(automata: &[Self]) -> Self {
        let mut concat_automaton = RawAutomaton::epsilon();
        // A storage for dead states to be eliminated during post-processing. Dead
        // states are generated:
        // - when an initial state has no cycle to itself in an automaton, it will
        //   become a dead state after concatenation, and can safely be removed.
        // - when concatenating an automaton whose final states have no outgoing
        //   transitions, transitions pointing to these final states can be redirected
        //   to the initial state of the next automaton. The old final states can then
        //   be removed.
        let mut garbage = FxHashSet::with_capacity_and_hasher(automata.len(), FxBuildHasher);
        let mut loop_on_initial = false;

        // The `rev()` is important for correctness. Each step concatenates the language
        // of `automaton` to the language of `concat_automaton`, which is done by
        // copying the outgoing transitions of `concat_automaton.initial_state`
        // to each final state of `automaton`. In particular, proceeding in the
        // forward order would miss some transitions when some initial states
        // happen to be final as well.
        for automaton in automata.iter().rev() {
            let nb_states = concat_automaton.transitions.len();
            let (mut transitions, _) = RawAutomaton::filter_map_transitions(
                &automaton.transitions,
                |state| Some(state + nb_states),
                automaton.transitions.len(),
                nb_states,
            );
            if automaton.nothing_after_final() {
                // In this branch, an optimisation can be done to save one state and one
                // transition (redirect transitions pointing to the final states of `automaton`
                // towards `concat_automaton.initial_state`).
                for succ in transitions.iter_mut() {
                    for (_, target) in succ {
                        if automaton.final_states.contains(&(*target - nb_states)) {
                            garbage.insert(*target);
                            *target = concat_automaton.initial_state;
                        }
                    }
                }
                concat_automaton.transitions.extend(transitions);
                loop_on_initial = automaton.loop_on_initial();
                concat_automaton.initial_state = automaton.initial_state + nb_states;
            } else {
                concat_automaton.transitions.extend(transitions);
                // Copying outgoing transitions from `concat_automaton.initial` to each final
                // state of `automaton`.
                for state in &automaton.final_states {
                    let outgoing =
                        concat_automaton.transitions[concat_automaton.initial_state].clone();
                    concat_automaton.transitions[state + nb_states].extend(outgoing);
                }
                // If the initial state of `concat_automaton` is also final, the final states of
                // `automaton` have to be added as final states of `concat_automaton`.
                if concat_automaton.final_states.contains(&concat_automaton.initial_state) {
                    concat_automaton
                        .final_states
                        .extend(automaton.final_states.iter().map(|s| s + nb_states));
                }

                // Updating the initial state and garbage collecting the previous one if
                // necessary.
                if !loop_on_initial {
                    garbage.insert(concat_automaton.initial_state);
                }
                loop_on_initial = automaton.loop_on_initial();
                concat_automaton.initial_state = automaton.initial_state + nb_states;
            }
        }

        // Renames the states of `concat_automaton` that are not to be removed, using a
        // continuous range of integer.
        let renaming = (0..concat_automaton.transitions.len())
            .filter(|source| !garbage.contains(source))
            .enumerate()
            .map(|(new_source, old_source)| (old_source, new_source))
            .collect::<FxHashMap<_, _>>();
        let (transitions, markers) = RawAutomaton::filter_map_transitions(
            &concat_automaton.transitions,
            |state| renaming.get(&state).copied(),
            renaming.len(),
            0,
        );
        let initial_state = *renaming.get(&concat_automaton.initial_state).unwrap();
        let final_states = (concat_automaton.final_states.iter())
            .filter_map(|state| renaming.get(state).copied())
            .collect::<FxHashSet<_>>();
        RawAutomaton {
            // False in general, but true in many practical cases. Will be double checked in the
            // next instruction.
            deterministic: false,
            complete: automata.iter().all(|a| a.complete),
            final_states,
            initial_state,
            markers,
            transitions,
        }
        .check_determinism()
    }

    /// Computes an automaton for the intersection of two languages. The
    /// intersection takes markers into account: two copies of letter `a`
    /// with different (non-0) markers are considered as different letters.
    /// However, `a` marked with 0 will be unified with `a` with a non-0
    /// marker.
    ///
    /// Apart from that, the intersection is a classical carthesian-product
    /// construction, i.e., it is simply an automaton whose states are pairs of
    /// states of the initial automata. A pair `(s1,s2)` is encoded as `s1 * n +
    /// s2`, where `n` is the number of states of `rhs`.
    pub(super) fn inter(&self, rhs: &Self) -> Self {
        let mut raw_transitions =
            Vec::with_capacity(self.transitions.len() * rhs.transitions.len());
        let mut markers = FxHashSet::default();

        // Tracks if the resulting automaton is deterministic and complete (may not be
        // due to the `join` operation below, since it may change some markers).
        let mut deterministic = self.deterministic && rhs.deterministic;
        let mut complete = self.complete && rhs.complete;

        // If two transitions have the same letter, the closure below adds the product
        // transition to the accumulator. Transitions that have the same letter, but
        // different markers, are only merged if one of the markers is zero (in which
        // case the non-zero marker is used).
        let mut join = |(source1, letter1, target1): (usize, Letter, usize),
                        (source2, letter2, target2): (usize, Letter, usize)|
         -> bool {
            if letter1.char == letter2.char
                && (letter1.marker == letter2.marker || letter1.marker == 0 || letter2.marker == 0)
            {
                let marker = std::cmp::max(letter1.marker, letter2.marker);
                let tr = (
                    (source1, source2),
                    Letter {
                        char: letter1.char,
                        marker,
                    },
                    (target1, target2),
                );

                // Only case where determinism might be violated.
                if deterministic && letter1.marker != letter2.marker {
                    deterministic = false
                };
                // Only case where completion might be violated.
                if complete && letter1.marker != letter2.marker {
                    complete = false
                }
                // Adding the marker and the transition.
                markers.insert(marker);
                raw_transitions.push(tr);
                true
            } else {
                false
            }
        };

        // Joining all reachable pairs of states in the product automaton.
        let mut visited = FxHashSet::with_capacity_and_hasher(
            std::cmp::max(self.transitions.len(), rhs.transitions.len()),
            FxBuildHasher,
        );
        let mut pending = Vec::with_capacity(self.transitions.len() * rhs.transitions.len());
        pending.push((self.initial_state, rhs.initial_state));
        while let Some((source1, source2)) = pending.pop() {
            if visited.insert((source1, source2)) {
                for (letter1, target1) in &self.transitions[source1] {
                    for (letter2, target2) in &rhs.transitions[source2] {
                        let tr1 = (source1, *letter1, *target1);
                        let tr2 = (source2, *letter2, *target2);
                        if join(tr1, tr2) {
                            pending.push((*target1, *target2))
                        }
                    }
                }
            }
        }

        // Renaming the states using a continuous range.
        let renaming = (visited.iter().enumerate())
            .map(|(new_source, old_source)| ((old_source.0, old_source.1), new_source))
            .collect::<FxHashMap<_, _>>();
        let mut transitions = vec![vec![]; renaming.len()];
        for (source, letter, target) in &raw_transitions {
            transitions[renaming[source]].push((*letter, renaming[target]));
        }
        // Computing the initial state.
        let initial_state = renaming[&(self.initial_state, rhs.initial_state)];
        // Computing the final states.
        let mut final_states = FxHashSet::default();
        for s1 in self.final_states.iter() {
            for s2 in rhs.final_states.iter() {
                if visited.contains(&(*s1, *s2)) {
                    final_states.insert(renaming[&(*s1, *s2)]);
                }
            }
        }

        RawAutomaton {
            deterministic,
            complete,
            initial_state,
            final_states,
            transitions,
            markers,
        }
        .remove_dead_states()
        .check_determinism()
    }
}

impl RawAutomaton {
    /// Computes an automaton for the complement of a language.
    /// Assumes that all states are numbered from 0 to `self.nb_states - 1`, and
    /// that the automaton is deterministic and complete. Mutates the
    /// argument.
    pub(super) fn complement(self) -> Self {
        assert!(
            self.deterministic && self.complete,
            "(bug) complement can only be performed on deterministic and complete automata"
        );
        let final_states = (0..self.transitions.len())
            .filter(|i| !self.final_states.contains(i))
            .collect::<FxHashSet<_>>();
        Self {
            final_states,
            ..self
        }
        .remove_dead_states()
    }

    /// Computes an automaton for the iteration (Kleene star) of a language.
    /// Only considers a non-null number of iterations. Mutates the
    /// argument, by copying all outgoing transitions from the initial
    /// state, to each of the final states.
    pub(super) fn strict_repeat(self) -> Self {
        let mut transitions = self.transitions;
        let outgoing_from_initial = transitions[self.initial_state].clone();
        for state in &self.final_states {
            transitions[*state].extend(outgoing_from_initial.clone());
            // Removing potential duplicates.
            transitions[*state] = (transitions[*state].iter().copied())
                .collect::<FxHashSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        }
        Self {
            deterministic: false,
            transitions,
            ..self
        }
        .check_determinism()
    }

    /// Removes final states and redirects any transition pointing to them to
    /// the a given state of `self` instead. Assumes there are no outgoing
    /// transitions from final states. Also makes the initial state final.
    fn redirect_final_to_initial(self) -> Self {
        let mut transitions = self.transitions;
        // Redirecting any transitions pointing to a final state, to the initial state.
        for succ in transitions.iter_mut() {
            for (_, target) in succ {
                if self.final_states.contains(target) {
                    *target = self.initial_state
                }
            }
        }
        // Removing final states (but not the initial state, if it is final).
        let renaming = (transitions.iter().enumerate())
            .filter(|(source, _)| {
                !self.final_states.contains(source) || *source == self.initial_state
            })
            .enumerate()
            .map(|(new_source, (old_source, _))| (old_source, new_source))
            .collect::<FxHashMap<_, _>>();
        let initial_state = renaming[&self.initial_state];
        let final_states = FxHashSet::from_iter([initial_state]);
        let (transitions, markers) = RawAutomaton::filter_map_transitions(
            &transitions,
            |state| renaming.get(&state).copied(),
            transitions.len() - self.final_states.len(),
            0,
        );
        Self {
            deterministic: self.deterministic,
            complete: self.complete,
            final_states,
            initial_state,
            markers,
            transitions,
        }
    }

    /// Computes an automaton for the iteration (Kleene star) of a language,
    /// including 0 iterations. Mutates the argument. A smaller automaton can be
    /// computed using `self.redirect_final_to_initial()` when there are no
    /// loops on the initial state nor outgoing transitions from the final
    /// states.
    pub(super) fn weak_repeat(self) -> Self {
        if self.nothing_after_final()
            && (!self.loop_on_initial() || self.final_states.contains(&self.initial_state))
        {
            // In this branch, we can replace the final states by the initial state.
            // Reducing the number of states lightens future determinisation and
            // minimisation.
            self.redirect_final_to_initial()
        } else {
            // Otherwise, the optimisation in unsound. So we just default to applying a
            // non-trivial repeat or returning epsilon.
            self.strict_repeat().make_optional()
        }
    }
}

// Implementation of automaton minimisation.
impl RawAutomaton {
    /// Computes the Nerode equivalence classes for the set of states of an
    /// automaton, i.e., two states are equivalent if they accept exactly the
    /// same inputs. The implementation represents sets of states by boolean
    /// vectors. The function also returns the size of the effective
    /// alphabet.
    fn nerode_congruence(&self, alphabet_size: usize, markers: &[usize]) -> Vec<Vec<bool>> {
        let mut final_states = vec![false; self.transitions.len()];
        self.final_states.iter().for_each(|&i| final_states[i] = true);
        let non_final_states = final_states.iter().map(|&b| !b).collect::<Vec<_>>();

        // The initial coarse partition which will be refined into Nerode's congruence.
        // It simply contains (at most) two classes, which are the (non-empty sets among
        // the) set of final states and its complement.
        let mut partition = [final_states, non_final_states]
            .into_iter()
            .filter(|vec| vec.iter().any(|b| *b))
            .collect::<Vec<_>>();

        // The set of distinguishers that will be used as criterion to refined the
        // partition.
        let mut distinguishers = partition.clone();
        while let Some(dist) = distinguishers.pop() {
            // For each alphabet letter, computes the set of states that can reach a set in
            // the distinguisher by reading this letter. See `alphabet.rs` for details about
            // the encoding of `Letter` as `usize`.
            let mut predecessors = vec![
                vec![false; self.transitions.len()];
                Letter::encoding_bound(alphabet_size, markers)
            ];
            for (source, succ) in self.transitions.iter().enumerate() {
                for (a, target) in succ {
                    if dist[*target] {
                        predecessors[a.encode(alphabet_size, markers)][source] = true;
                    }
                }
            }

            // For each predecessor set (up to duplicates), refine the partition (in
            // short, intersect it with all classes of the partition). The set of
            // distinguishers is updated accordingly to Hopcroft's criterion.
            //
            // Note: The conversion to a HashSet removes duplicates in the iteration (not
            // doing so worsened performances an order of magnitude in prior
            // implementations).
            for pred in predecessors.iter().collect::<FxHashSet<_>>() {
                let mut partition_temp = Vec::with_capacity(partition.len() * 2);
                while let Some(class) = partition.pop() {
                    // Compute the refinement of the partition class (intersection
                    // and complement with the distinguisher).
                    let (inter, minus): (Vec<_>, Vec<_>) =
                        pred.iter().zip(class.iter()).map(|(&p, &c)| (p && c, !p && c)).unzip();
                    let inter_size = inter.iter().filter(|b| **b).count();
                    let minus_size = minus.iter().filter(|b| **b).count();
                    if inter_size != 0 && minus_size != 0 {
                        // Non trivial refinement: the partition class `class` is
                        // refined.
                        partition_temp.push(inter.clone());
                        partition_temp.push(minus.clone());
                        match distinguishers.iter().enumerate().find(|(_, d)| **d == class) {
                            Some((i, _)) => {
                                // `class` was already a distinguisher: refine it as
                                // well.
                                distinguishers.swap_remove(i);
                                distinguishers.push(inter);
                                distinguishers.push(minus);
                            }
                            None => {
                                // `class` was not a distinguisher: add the smallest
                                // set among the intersection / complement as a new
                                // distinguisher.
                                if inter_size <= minus_size {
                                    distinguishers.push(inter);
                                } else {
                                    distinguishers.push(minus);
                                }
                            }
                        }
                    } else {
                        // No interaction between the distinguisher and this
                        // partition class: no change needed.
                        partition_temp.push(class);
                    }
                }
                // The now-empty `partition` is refilled with the refined classes.
                partition.append(&mut partition_temp)
            }
        }
        partition
    }

    /// Implementation of minimisation using the Nerode's congruence. It simply
    /// numbers each equivalence class, and generates the transitions between
    /// the different classes accordingly. Correctness assumes the automaton is
    /// deterministic.
    ///
    /// Will only be called once, just before converting the `RawAutomaton` to
    /// `Automaton`. Additionally calls are performed when serializing, since it
    /// may compress the resulting `RawAutomaton` which will be serialized
    /// anyway.
    pub(super) fn minimise(self, alphabet_size: usize) -> Self {
        assert!(
            self.deterministic,
            "minimisation is only possible on deterministic automata"
        );
        let partition = self
            .nerode_congruence(alphabet_size, &Vec::from_iter(self.markers.clone()))
            .into_iter()
            .enumerate()
            .collect::<Vec<_>>();
        let initial_state = partition.iter().find(|(_, v)| v[self.initial_state]).unwrap().0;
        let mut final_states =
            FxHashSet::with_capacity_and_hasher(self.final_states.len(), FxBuildHasher);
        partition.iter().for_each(|(index, class)| {
            let elt = class.iter().enumerate().find(|&(_, &b)| b).unwrap().0;
            if self.final_states.contains(&elt) {
                final_states.insert(*index);
            }
        });
        let mut transitions = vec![vec![]; partition.len()];
        for (index1, class1) in &partition {
            let source = class1.iter().enumerate().find(|(_, &b)| b).unwrap().0;
            for (letter, target) in &self.transitions[source] {
                let index2 = (partition.iter().find(|(_, class)| class[*target])).unwrap().0;
                transitions[*index1].push((*letter, index2));
            }
        }
        Self {
            deterministic: true,
            initial_state,
            final_states,
            transitions,
            ..self
        }
    }
}

impl RawAutomaton {
    /// Exhibits a path from the initial state to a given state in the
    /// automaton. Panics if such a path does not exist, or if the automaton
    /// is not deterministic (ignoring output-determinism).
    fn witness_reachability(&self, state: usize) -> Vec<u8> {
        // `reachability[s]` contains a minimal sequence of `Letter` that can be read to
        // reach `state` from `s`.
        let mut reachability = vec![None; self.transitions.len()];
        reachability[state] = Some(vec![]);
        // `pending` contains some states that have recently been assigned a path in
        // `reachability`.
        let mut pending = vec![state];
        // Main loop, extending paths backwards from pending states.
        while let Some(pending_state) = pending.pop() {
            if reachability[self.initial_state].is_some() {
                break;
            }
            for (source, succ) in self.transitions.iter().enumerate() {
                for (letter, target) in succ {
                    if *target == pending_state && reachability[source].is_none() {
                        let path = reachability[pending_state].as_ref().unwrap();
                        let extended_path =
                            once(letter.char).chain(path.iter().copied()).collect::<Vec<_>>();
                        reachability[source] = Some(extended_path);
                        pending.push(source);
                    }
                }
            }
        }
        reachability[self.initial_state]
            .clone()
            .expect("(bug) witness_reachability has been called on an unreachable state {state}")
    }

    /// Conversion into a minimal deterministic automaton. Mutates the argument
    /// to determinise it.
    pub(super) fn normalise(self) -> Automaton {
        let alphabet_size = (self.transitions.iter())
            .map(|succ| {
                (succ.iter().map(|(letter, _)| letter.char as usize + 1)).max().unwrap_or(0)
            })
            .max()
            .unwrap_or(0);
        let base = self.determinise(false, alphabet_size).minimise(alphabet_size);

        let mut transitions =
            FxHashMap::with_capacity_and_hasher(base.transitions.len(), FxBuildHasher);
        for (source, succ) in base.transitions.iter().enumerate() {
            for (letter, target) in succ {
                if let Some((target2, marker2)) =
                    transitions.insert((source, letter.char), (*target, letter.marker))
                {
                    if letter.marker == marker2 {
                        panic!(
                            "(bug) determinisation was incorrect: source state {source} was pointing to both targets {target} and {target2} after letter {} (marked {})",
                            letter.char,
                            letter.marker)
                    } else {
                        let bugged_path = base.witness_reachability(source);
                        panic!(
                            "a non output-deterministic language has been specified. After reading the string:\n\n{}\n\n(i.e., bytes [{:?}])\nit is unclear whether character '{}' (byte {}) should be marked {} or {}",
                            String::from_utf8_lossy(&bugged_path),
                            bugged_path,
                            letter.char as char,
                            letter.char,
                            letter.marker,
                            marker2
                        )
                    }
                }
            }
        }
        Automaton {
            nb_states: base.transitions.len(),
            initial_state: base.initial_state,
            final_states: base.final_states,
            transitions,
        }
    }
}

impl Automaton {
    /// Renames the states by off-setting states by a constant number. Can be
    /// useful when handling several independent automaton at the same time (to
    /// ensure their state numbers do not overlap).
    pub fn offset_states(&self, offset: usize) -> Self {
        Self {
            nb_states: self.nb_states + offset,
            initial_state: self.initial_state + offset,
            final_states: self.final_states.iter().map(|s| s + offset).collect::<FxHashSet<_>>(),
            transitions: self
                .transitions
                .iter()
                .map(|((source, letter), (target, marker))| {
                    ((*source + offset, *letter), (*target + offset, *marker))
                })
                .collect::<FxHashMap<_, _>>(),
        }
    }
}

#[cfg(test)]
impl Automaton {
    /// Executes an automaton for a given sequence of bytes. Returns a vector of
    /// states (corresponding to the states of the run), a vector of bytes (the
    /// output of markers for this input), and a boolean indicating whether the
    /// run was stuck.
    pub(super) fn run(&self, input: &[u8]) -> (Vec<usize>, Vec<usize>, bool) {
        let mut iter = input.iter();
        let mut current_state = self.initial_state;
        let mut output = Vec::with_capacity(input.len());
        let mut states = Vec::with_capacity(input.len() + 1);
        let mut letter = iter.next();
        states.push(current_state);
        // Iterates over the letters of the input and moves accross the states
        // accordingly.
        while let Some(a) = letter {
            match self.transitions.get(&(current_state, *a)).copied() {
                // Interrupted run.
                None => return (states, Vec::new(), true),
                // The run goes on.
                Some((state, marker)) => {
                    current_state = state;
                    states.push(current_state);
                    output.push(marker);
                    letter = iter.next();
                }
            }
        }
        (states, output, false)
    }
}

#[cfg(test)]
pub(super) mod tests {
    use itertools::Itertools;

    use crate::parsing::regex::{Regex, RegexInstructions};

    /// Tests whether a given regular expression accepts or rejects two sets of
    /// corresponding strings. Takes the alphabet size as a parameter to allow
    /// for more readable tests with a restricted byte alphabet.
    pub(crate) fn automaton_one_test(
        index: usize,
        alphabet_size: usize,
        regex: &Regex,
        accepted: &[(&[u8], &[usize])],
        rejected: &[&[u8]],
        print_automaton: bool,
    ) {
        accepted.iter().for_each(|(s,o)|
            assert!(s.len() == o.len(),
            "[test {index}] There is probably a typo in the tests vectors: the input ({:?}, length = {}) and the expected output ({:?}, length = {}) have different lengths.", 
            s, s.len(), o, o.len())
        );
        println!("\n\n** TEST no {index}\n** alphabet size = {alphabet_size}");
        let automaton = regex.to_automaton_param(alphabet_size);
        if print_automaton {
            println!("** automaton {:?}", automaton)
        }
        accepted.iter().for_each(|&(s,o)| {
            println!(
                "\n -> testing on input string \"{}\" (bytes: [{}])", String::from_utf8_lossy(s),
                s.iter().map(|b| b.to_string()).join(", ")
            );
            let (v,output,interrupted) = automaton.run(s);
            if interrupted {
                panic!("input was unexpectedly rejected after being stuck after {} transitions", v.len()-1)
            }
            else {
                let counter = v.len() - 1;
                let state = v[counter];
                let f = automaton.final_states.contains(&state);
                if f {
                    if o.len() == output.len() && o.iter().zip_eq(output.iter()).all(|(o1,o2)| o1 == o2) {
                        println!("... which is accepted and marked:\n{:?}\nas expected. The automaton reached the final state {} in {} transitions.", output, state, counter)
                    } else {
                        panic!("[test {index}]: the input {:?} is accepted as expected, but it is marked:\n{:?}\nwhereas the following markers were expected:\n{:?}\nThe automaton reached the final state {} in {} transitions.", s, output, o, state, counter)
                    }
                } else {
                    panic!("input was unexpectedly rejected (automaton run ended up in the non-final state {} after {} transitions)", state, counter)
                }
            }
        });
        rejected.iter().for_each(|&s| {
            println!(
                "\n -> testing on input string \"{}\" (bytes: [{}])", String::from_utf8_lossy(s),
                s.iter().map(|b| b.to_string()).join(", ")
            );
            let (v,output,interrupted) = automaton.run(s);
            if interrupted {
                println!("... which is rejected as expected (the automaton run was stuck after {} transitions).", v.len())
            } else {
                let counter = v.len() - 1;
                let state = v[counter];
                    let f = automaton.final_states.contains(&state);
                    if f {
                        panic!("input was unexpectedly accepted (reached final state {} after {} transitions and outputs {:?}).", state, counter, output)
                    } else {
                        println!("... which is rejected as expected (the automaton run ended up in the non-final state {} after {} transitions).", state, counter)
                    }
            }
        });
        println!(">> Test nb {index} is finished!\n==========");
    }

    #[test]
    fn automaton_test() {
        let zero: Regex = 0.into();
        let one: Regex = 1.into();
        let two: Regex = 2.into();

        let regex0 = one.clone();
        let accepted0: &[(&[u8], &[usize])] = &[(&[1], &[0])];
        let rejected0: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 1], &[2]];

        let regex1 = one.clone().terminated(two.clone());
        let accepted1: &[(&[u8], &[usize])] = &[(&[1, 2], &[0; 2])];
        let rejected1: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 1], &[1, 2, 0]];

        let regex2 = Regex::cat([one.clone(), two.clone().list(), zero.clone()]);
        let accepted2: &[(&[u8], &[usize])] = &[
            (&[1, 0], &[0; 2]),
            (&[1, 2, 0], &[0; 3]),
            (&[1, 2, 2, 0], &[0; 4]),
            (&[1, 2, 2, 2, 0], &[0; 5]),
        ];
        let rejected2: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 1], &[1, 0, 2], &[1, 2]];

        let regex3 = Regex::cat([
            one.clone(),
            two.clone().non_empty_list(),
            zero.clone().list(),
        ]);
        let accepted3: &[(&[u8], &[usize])] = &[
            (&[1, 2, 0], &[0; 3]),
            (&[1, 2], &[0; 2]),
            (&[1, 2, 2, 0], &[0; 4]),
            (&[1, 2, 2, 2, 0], &[0; 5]),
        ];
        let rejected3: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 0], &[1, 1], &[1, 0, 2], &[1, 2, 1]];

        let regex4 = one.clone().minus(one.clone());
        let accepted4: &[(&[u8], &[usize])] = &[];
        let rejected4: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 0], &[1, 1], &[1, 0, 2], &[1, 2]];

        let regex5 = Regex::any().minus(zero.clone().or(one.clone()).list());
        let accepted5: &[(&[u8], &[usize])] = &[
            (&[2], &[0]),
            (&[0, 2], &[0; 2]),
            (&[2, 1], &[0; 2]),
            (&[0, 2, 1], &[0; 3]),
            (&[0, 2, 2, 1, 2], &[0; 5]),
            (&[2, 1, 2, 0, 1, 1], &[0; 6]),
        ];
        let rejected5: &[&[u8]] = &[
            &[],
            &[1],
            &[0, 1],
            &[1, 1],
            &[0, 1, 1],
            &[0, 1, 0, 1, 1],
            &[1, 1, 1, 0, 1, 1],
        ];

        let regex6 = regex5
            .clone()
            .minus(Regex::any().minus(Regex::any_byte().minus(two.clone()).list()));
        let accepted6: &[(&[u8], &[usize])] = &[];
        let rejected6: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 0], &[1, 1], &[1, 0, 2], &[1, 2]];

        let regex7 = Regex::any_byte()
            .minus(Regex::byte_from([2]))
            .list()
            .minus(Regex::byte_from([0]));
        let accepted7: &[(&[u8], &[usize])] = &[
            (&[], &[]),
            (&[0, 1], &[0; 2]),
            (&[0, 0], &[0; 2]),
            (&[1, 0], &[0; 2]),
            (&[1, 1], &[0; 2]),
            (&[0, 1, 0, 1, 0], &[0; 5]),
        ];
        let rejected7: &[&[u8]] = &[
            &[0],
            &[2],
            &[0, 1, 2],
            &[1, 2],
            &[0, 2, 1],
            &[1, 1, 2, 1, 1],
            &[1, 1, 1, 0, 1, 2],
        ];

        let regex8 = one.clone().non_empty_list().mark_bytes([1], 1).separated_list(two.clone());
        let accepted8: &[(&[u8], &[usize])] = &[
            (&[], &[]),
            (&[1, 1], &[1, 1]),
            (&[1, 1, 2, 1, 1], &[1, 1, 0, 1, 1]),
            (&[1, 2, 1, 1, 1, 2, 1], &[1, 0, 1, 1, 1, 0, 1]),
            (&[1, 2, 1, 2, 1, 2, 1], &[1, 0, 1, 0, 1, 0, 1]),
        ];
        let rejected8: &[&[u8]] = &[
            &[0],
            &[2],
            &[0, 1, 2],
            &[1, 2],
            &[0, 2, 1],
            &[1, 1, 2, 2, 1, 1],
            &[1, 2, 1, 2, 1, 2, 0],
        ];

        // Tests with a small alphabet to debug automata constructions.
        let regex = [
            (regex0, accepted0, rejected0),
            (regex1, accepted1, rejected1),
            (regex2, accepted2, rejected2),
            (regex3, accepted3, rejected3),
            (regex4, accepted4, rejected4),
            (regex5, accepted5, rejected5),
            (regex6, accepted6, rejected6),
            (regex7, accepted7, rejected7),
            (regex8, accepted8, rejected8),
        ];
        regex.iter().enumerate().for_each(|(index, (regex, accepted, rejected))| {
            automaton_one_test(index, 3, regex, accepted, rejected, true)
        });
    }
}

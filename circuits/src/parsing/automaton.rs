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
        let marker = markers
            .iter()
            .enumerate()
            .find(|(_, &m)| m == self.marker)
            .unwrap()
            .0;
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
        let mut transitions = Vec::from_iter(
            word.iter()
                .map(Vec::len)
                .map(Vec::with_capacity)
                .chain(once(vec![])),
        );
        let mut markers = FxHashSet::with_capacity_and_hasher(2, FxBuildHasher);
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
            "attempt to construct an automaton with an alphabet of size {alphabet_size} (will overflow u8"
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
    /// has be traversed many times, since there are often 10~100 transitions
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
        self.final_states
            .iter()
            .all(|&state| self.transitions[state].is_empty())
    }
}

// Post processing of automata handling the aftermath of a suboptimal operation.
impl RawAutomaton {
    /// Updates the set of transitions of an automaton accordingly to an update
    /// function. If the update function returns `None` on a given state, all
    /// transitions involving it are removed. Also recomputes the set of markers
    /// in case some are removed.
    ///
    /// Also takes as argument the minimal value of the updated states
    /// (`offset`) to compute a transition table more easily.
    fn filter_map_transitions(
        transitions: &[Vec<(Letter, usize)>],
        f: impl Fn(usize) -> Option<usize>,
        new_nb_states: usize,
        offset: usize,
    ) -> (Vec<Vec<(Letter, usize)>>, FxHashSet<usize>) {
        let mut new_transitions = vec![vec![]; new_nb_states];
        let mut markers = FxHashSet::with_capacity_and_hasher(2, FxBuildHasher);
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

        Self {
            deterministic: self.deterministic,
            complete: false, // `false` most of the time.
            initial_state,
            final_states,
            transitions,
            markers,
        }
    }

    /// Checks if an automaton is deterministic. If the field `deterministic` or
    /// `epsilon_transition` are set to true, nothing is done; otherwise, this
    /// function scans the transition table to rule out a potential false
    /// negative.
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
        // States of the new deterministic automaton are represented by sets of states
        // of `base`. These sets are represented by boolean vectors of length
        // `base.nb_states`, where each index indicates whether the set contains a given
        // state of `base`.
        let mut initial_state = vec![false; base.nb_states];
        initial_state[base.initial_state] = true;
        let mut state_counter = 0;

        // A Map recording the visited states of the new automaton, mapping them
        // injectively to an integer for renaming purpose at the end.
        let mut visited = HashMap::new();

        // The list of states that remain to be handled by the transition-generation
        // loop.
        let mut pending = vec![initial_state];

        // Storage for the transitions and final states of the new automaton.
        let mut transitions = Vec::with_capacity(base.transitions.len());
        let mut final_states = HashSet::new();

        while let Some(power_state) = pending.pop() {
            if !visited.contains_key(&power_state) {
                visited.insert(power_state.clone(), state_counter);
                // In this branch, we handle a never-encountered state the new automaton.
                // So, we check whether it is final (i.e., if the set of states of `base` it
                // represents contains a final state of `base`), and increment the state
                // counter.
                if base.final_states.iter().any(|state| power_state[*state]) {
                    final_states.insert(state_counter);
                }
                state_counter += 1;

                // Generation of the transitions starting from `power_state` in the new
                // automaton. For each letter `letter`, `power_set` is mapped to the set of
                // states `target` such that a transition `(source,Some(letter),target)`
                // exists in `base`, with `source` in `power_set`.
                let mut successors = vec![
                    vec![false; base.nb_states];
                    Letter::encoding_bound(alphabet_size, markers)
                ];
                base.transitions
                    .iter()
                    .for_each(|(source, letter, target)| {
                        let letter = letter.unwrap();
                        if power_state[*source] {
                            successors[letter.encode(alphabet_size, markers)][*target] = true
                        }
                    });
                successors
                    .iter()
                    .enumerate()
                    .for_each(|(letter_encoding, target)| {
                        let letter = Letter::decode(letter_encoding, alphabet_size, markers);
                        transitions.push((power_state.clone(), letter, target.clone()));
                        pending.push(target.clone());
                    })
            }
        }

        // Replacing powerset transitions with their numbered version.
        let transitions = transitions
            .iter()
            .map(
                |(source, letter, target)| match (visited.get(source), visited.get(target)) {
                    (None, _) | (_, None) => {
                        panic!("determinisation did not label states correctly")
                    }
                    (Some(source), Some(target)) => (*source, Some(*letter as Letter), *target),
                },
            )
            .collect::<Vec<_>>();
        RawAutomaton {
            nb_states: state_counter,
            deterministic_and_complete: true,
            epsilon_transitions: false,
            initial_state: 0,
            final_states,
            transitions,
        }
    }
}

// Implementation of automaton combination operations.
impl<State> RawAutomaton<State>
where
    State: Copy + Clone + Eq + Hash + Debug,
{
    /// Computes the union of a collection of automata. Calling this function
    /// over a collection of size `N` leads to a smaller automaton (before
    /// minimisation) than calling the function `N-1` in a binary way.
    pub(super) fn union(automata: &[Self]) -> RawAutomaton<Vec<Option<State>>> {
        let n = automata.len();
        let (capacity, nb_states) =
            automata
                .iter()
                .fold((n, 0), |(accu_tr, accu_states), automaton| {
                    (
                        accu_tr + automaton.transitions.len(),
                        accu_states + automaton.nb_states,
                    )
                });

        // Computes the embedding of a state of one automaton of `automata` inside the
        // new automaton (whose states represent the disjoint union of all previous
        // automata).
        let combined_state = |index: usize, state: &State| -> Vec<Option<State>> {
            let mut res = vec![None; n];
            res[index] = Some(*state);
            res
        };
        // Initial state of the new automaton. It will be linked to the initial states
        // of all automata of `automata` by epsilon transitions.
        let initial_state = vec![None; n];
        let mut transitions = Vec::with_capacity(capacity);
        let mut final_states = HashSet::new();

        for (index, automaton) in automata.iter().enumerate() {
            // Pushing an epsilon transition from the new initial state to the initial state
            // of automaton number `index`.
            transitions.push((
                initial_state.clone(),
                None,
                combined_state(index, &automaton.initial_state),
            ));
            // Adding all transitions of automaton number `index`.
            for (source, letter, target) in &automaton.transitions {
                transitions.push((
                    combined_state(index, source),
                    *letter,
                    combined_state(index, target),
                ));
            }
            // Adding all final states of automaton number `index`.
            for state in &automaton.final_states {
                final_states.insert(combined_state(index, state));
            }
        }
        RawAutomaton {
            nb_states,
            deterministic_and_complete: false,
            epsilon_transitions: true,
            initial_state,
            final_states,
            transitions,
        }
    }

    /// Computes an automaton for the concatenation of two languages.
    pub(super) fn concat<S>(
        &self,
        rhs: &RawAutomaton<S>,
    ) -> RawAutomaton<(Option<State>, Option<S>)>
    where
        S: Copy + Clone + Eq + Hash + Debug,
    {
        let mut transitions = Vec::with_capacity(
            self.transitions.len() + rhs.transitions.len() + self.final_states.len(),
        );
        self.transitions
            .iter()
            .for_each(|(source, letter, target)| {
                transitions.push(((Some(*source), None), *letter, (Some(*target), None)))
            });
        rhs.transitions.iter().for_each(|(source, letter, target)| {
            transitions.push(((None, Some(*source)), *letter, (None, Some(*target))))
        });
        let initial_state = (Some(self.initial_state), None);
        self.final_states.iter().for_each(|&state| {
            transitions.push(((Some(state), None), None, (None, Some(rhs.initial_state))));
        });
        let final_states = rhs
            .final_states
            .iter()
            .map(|&state| (None, Some(state)))
            .collect::<HashSet<_>>();
        RawAutomaton {
            nb_states: self.nb_states + rhs.nb_states,
            deterministic_and_complete: false,
            epsilon_transitions: true,
            initial_state,
            final_states,
            transitions,
        }
    }

    // Computes an automton for the intersection of two languages. Requires that
    // they do not contain epsilon transitions. The intersection takes markers into
    // account: two copies of letter `a` with different (non-0) markers are
    // considered as different letters. However, `a` marked with 0 will be unified
    // with `a` with a non-0 marker.
    //
    // Apart from that, the intersection is a classical carthesian-product
    // construction.
    pub(super) fn inter<S>(&self, rhs: &RawAutomaton<S>) -> RawAutomaton<(State, S)>
    where
        S: Copy + Clone + Eq + Hash + Debug,
    {
        assert!(
            !self.epsilon_transitions && !rhs.epsilon_transitions,
            "(bug) intersection cannot operate with epsilon transitions."
        );

        let mut transitions = Vec::with_capacity(self.transitions.len() * rhs.transitions.len());
        let mut final_states = Vec::with_capacity(self.final_states.len() * rhs.final_states.len());
        // If two transitions have the same letter, the closure below adds the product
        // transition to the accumulator. Transitions that have the same letter, but
        // different markers, are only merged if one of the markers is zero (in which
        // case the non-zero marker is used).
        let mut join =
            |(source1, letter1, target1): (State, Option<Letter>, State),
             (source2, letter2, target2): (S, Option<Letter>, S)| {
                let letter1 = letter1.unwrap();
                let letter2 = letter2.unwrap();
                if letter1.char == letter2.char
                    && (letter1.marker == letter2.marker
                        || letter1.marker == 0
                        || letter2.marker == 0)
                {
                    transitions.push((
                        (source1, source2),
                        Some(Letter {
                            char: letter1.char,
                            marker: std::cmp::max(letter1.marker, letter2.marker),
                        }),
                        (target1, target2),
                    ));
                }
            };
        for tr1 in self.transitions.iter() {
            for tr2 in rhs.transitions.iter() {
                join(*tr1, *tr2)
            }
        }
        for s1 in self.final_states.iter() {
            for s2 in rhs.final_states.iter() {
                final_states.push((*s1, *s2));
            }
        }
        RawAutomaton {
            nb_states: self.nb_states * rhs.nb_states,
            deterministic_and_complete: false, /* Even when all intersected automata are
                                                * deterministic, `join` may introduce
                                                * non-determinism to do the marker merging. */
            epsilon_transitions: false,
            initial_state: (self.initial_state, rhs.initial_state),
            final_states: HashSet::from_iter(final_states),
            transitions,
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

        }
    }
}

// Implementation of automaton minimisation.
impl Automaton {
    // Computes the Nerode equivalence classes for the set of states of an
    // automaton, i.e., two states are equivalent if they accept exactly the same
    // inputs. The implementation represents sets of states by boolean vectors. The
    // function also returns the size of the effective alphabet.
    fn nerode_congruence(&self, alphabet_size: usize, markers: &[usize]) -> Vec<Vec<bool>> {
        let mut final_states = vec![false; self.state_bound];
        self.final_states
            .iter()
            .for_each(|&i| final_states[i] = true);
        let non_final_states = final_states.iter().map(|&b| !b).collect::<Vec<_>>();

        // The initial coarse partition which will be refined into Nerode's congruence.
        // It simply contains (at most) two classes, which are the (non-empty sets among
        // the) set of final states and its complement.
        let mut partition = [final_states, non_final_states]
            .iter()
            .filter(|vec| vec.iter().any(|b| *b))
            .cloned()
            .collect::<Vec<_>>();

        // The set of distinguishers that will be used as criterion to refined the
        // partition.
        let mut distinguishers = partition.clone();
        while let Some(dist) = distinguishers.pop() {
            // For each alphabet letter, computes the set of states that can reach a set in
            // the distinguisher by reading this letter. See `alphabet.rs` for details about
            // the encoding of `Letter` as `usize`.
            let mut predecessors =
                vec![vec![false; self.state_bound]; Letter::encoding_bound(alphabet_size, markers)];
            for ((source, a), (target, marker)) in self.transitions.iter() {
                let encoding = Letter {
                    char: *a,
                    marker: *marker,
                }
                .encode(alphabet_size, markers);
                if dist[*target] {
                    predecessors[encoding][*source] = true;
                }
            }
            // For each letter, use the predecessor set to refine the partition (in short,
            // intersect it with all classes of the partition). The set of distinguishers is
            // updated accordingly to Hopcroft's criterion.
            for pred in predecessors {
                let mut partition_temp = Vec::with_capacity(partition.len() * 2);
                while let Some(class) = partition.pop() {
                    // Compute the refinement of the partition class (intersection
                    // and complement with the distinguisher).
                    let (inter, minus): (Vec<_>, Vec<_>) = pred
                        .iter()
                        .zip(class.iter())
                        .map(|(&p, &c)| (p && c, !p && c))
                        .unzip();
                    let inter_size = inter.iter().filter(|b| **b).count();
                    let minus_size = minus.iter().filter(|b| **b).count();
                    if inter_size != 0 && minus_size != 0 {
                        // Non trivial refinement: the partition class `class` is
                        // refined.
                        partition_temp.push(inter.clone());
                        partition_temp.push(minus.clone());
                        match distinguishers
                            .iter()
                            .enumerate()
                            .find(|(_, d)| **d == class)
                        {
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

    // Implementation of minimisation using the Nerode's congruence. It simply
    // numbers each equivalence class, and generates the transitions between the
    // different classes accordingly.
    fn minimise(&self, alphabet_size: usize, markers: &[usize]) -> Self {
        let partition = self
            .nerode_congruence(alphabet_size, markers)
            .iter()
            .cloned()
            .enumerate()
            .collect::<Vec<_>>();
        let state_bound = partition.len();
        let initial_state = partition
            .iter()
            .find(|(_, v)| v[self.initial_state])
            .unwrap()
            .0;
        let mut final_states = HashSet::new();
        partition.iter().for_each(|(index, class)| {
            let elt = class.iter().enumerate().find(|&(_, &b)| b).unwrap().0;
            if self.final_states.contains(&elt) {
                final_states.insert(*index);
            }
        });
        let mut transitions: HashMap<(usize, u8), (usize, usize)> = HashMap::new();
        for (index1, class1) in partition.clone() {
            let source = class1.iter().enumerate().find(|&(_, &b)| b).unwrap().0;
            for letter in 0..alphabet_size {
                self.transitions
                    .get(&(source, letter as u8))
                    .iter()
                    .for_each(|&&(target, marker)| {
                        let index2 = partition.iter().find(|(_, class)| class[target]).unwrap().0;
                        transitions.insert((index1, letter as u8), (index2, marker));
                    });
            }
        }
        Self {
            state_bound,
            initial_state,
            final_states,
            transitions,
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
                        let extended_path = once(letter.char)
                            .chain(path.iter().copied())
                            .collect::<Vec<_>>();
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
    pub(super) fn normalise(&mut self) -> Automaton {
        let mut markers = HashSet::new();
        let mut alphabet_size = 0;
        self.transitions.iter().for_each(|(_, letter_option, _)| {
            letter_option.iter().for_each(|letter| {
                markers.insert(letter.marker);
                alphabet_size = std::cmp::max(alphabet_size, 1 + letter.char as usize)
            })
        });
        let markers = markers.iter().copied().collect::<Vec<_>>();
        self.determinise(alphabet_size, &markers);
        *self = self.normalise_states();
        let mut transitions = HashMap::new();
        self.transitions
            .iter()
            .for_each(|(source, letter, target)| match letter {
                None => panic!("(bug) determinisation failed to remove an epsilon transition. The automaton is:\n{:?}\n\n", self),
                Some(letter) => {
                    match transitions.insert((*source, letter.char), (*target, letter.marker)) {
                        None => (),
                        Some((target2, marker2)) => {
                            if letter.marker == marker2 {
                                panic!("(bug) determinisation was incorrect: source state {source} was pointing to both targets {target} and {target2} after letter {} (marked {})", letter.char, letter.marker)
                            } else {
                                let bugged_path = self.witness_reachability(*source);
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
                },
            });
        Automaton {
            state_bound: self.nb_states,
            initial_state: self.initial_state,
            final_states: self.final_states.clone(),
            transitions,
        }
        .minimise(alphabet_size, &markers)
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
            final_states: self
                .final_states
                .iter()
                .map(|s| s + offset)
                .collect::<FxHashSet<_>>(),
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

        let regex8 = one
            .clone()
            .non_empty_list()
            .mark_bytes([1], 1)
            .separated_list(two.clone());
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
        regex
            .iter()
            .enumerate()
            .for_each(|(index, (regex, accepted, rejected))| {
                automaton_one_test(index, 3, regex, accepted, rejected, true)
            });
    }
}

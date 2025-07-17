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
//    with `RawAutomaton::normalise_states`.
//
//  - `Automaton.minimise` (minimisation). Implements Hopcroft's algorithm to
//    compute the Nerode's congruence of the automaton. It intuitively detects
//    states that are indistinguishable, and merges them to yield a smaller
//    transition table.
//
// The module also implements a couple of tests with a minimal alphabet (only
// bytes 0,1,2 are allowed) to check the validity of the constructions.

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    iter::once,
};

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
            .find(|(_, m)| **m == self.marker)
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
pub(super) struct RawAutomaton<State> {
    /// Upper bound on the number of reachable states.
    nb_states: usize,
    /// Indicator of whether the automaton is deterministic and complete.
    deterministic_and_complete: bool,
    /// Indicator of whether the automaton contains epsilon transitions.
    epsilon_transitions: bool,
    /// The initial state of the automaton.
    initial_state: State,
    /// The final states of the automaton.
    final_states: HashSet<State>,
    /// The set of transitions, including epsilon-transitions. At this stage,
    /// this transition table is simply a collection of transitions with no
    /// check of redundancy or determinism. This will be handled during the
    /// conversion into the more structured type `Automaton`.
    transitions: Vec<(State, Option<Letter>, State)>,
}

/// A normalised model of a deterministic (but not necessarily complete) finite
/// automaton operating on bytes. The set of states is implicitly represented by
/// the range `0..nb_states`.
#[derive(Clone, Debug)]
pub struct Automaton {
    /// Strict upper bound on the maximal reachable state. I.e., it is
    /// guaranteed that all states appearing in `self.transitions` are lower
    /// than `self.state_bound`.
    pub state_bound: usize,
    /// The initial state of the automaton.
    pub initial_state: usize,
    /// The final states of the automaton.
    pub final_states: HashSet<usize>,
    /// `transitions.get(state,byte)` returns the transition target and its
    /// marker upon reading input `byte` in state `state`. A key may be
    /// undefined, in which case it means the automaton jumps into an
    /// implicit deadlock state.
    pub transitions: HashMap<(usize, u8), (usize, usize)>,
}

impl RawAutomaton<usize> {
    /// Creates an empty automaton with a unique default state.
    pub(super) fn empty() -> RawAutomaton<usize> {
        Self {
            nb_states: 1,
            deterministic_and_complete: false,
            epsilon_transitions: false,
            initial_state: 0,
            final_states: HashSet::new(),
            transitions: Vec::new(),
        }
    }

    /// Creates an automaton recognising only the empty word.
    pub(super) fn epsilon() -> RawAutomaton<usize> {
        Self {
            nb_states: 1,
            deterministic_and_complete: false,
            epsilon_transitions: false,
            initial_state: 0,
            final_states: HashSet::from_iter([0]),
            transitions: Vec::new(),
        }
    }

    /// Creates an automaton accepting any word of 1 byte belonging to
    /// `letters`. The alphabet size can be specified, which effectively filters
    /// out any transition involving a byte outside of the alphabet.
    pub(super) fn singleton(letters: &[u8], alphabet_size: usize) -> RawAutomaton<usize> {
        Self {
            nb_states: 2,
            deterministic_and_complete: false,
            epsilon_transitions: false,
            initial_state: 0,
            final_states: HashSet::from([1]),
            transitions: {
                letters
                    .iter()
                    .map_while(|&i| {
                        if (i as usize) < alphabet_size {
                            Some((0, Some(i.into()), 1))
                        } else {
                            None
                        }
                    })
                    .collect()
            },
        }
    }

    /// Creates an automaton accepting any word.
    pub(super) fn universal(alphabet_size: usize) -> RawAutomaton<usize> {
        assert!(
            alphabet_size <= ALPHABET_MAX_SIZE,
            "attempt to construct an automaton with an alphabet of size {alphabet_size} (will overflow u8"
        );
        Self {
            nb_states: 1,
            deterministic_and_complete: true,
            epsilon_transitions: false,
            initial_state: 0,
            final_states: HashSet::from_iter([0]),
            transitions: (0..alphabet_size)
                .map(|b| (0, Some((b as u8).into()), 0))
                .collect::<Vec<_>>(),
        }
    }
}

impl<State> RawAutomaton<State>
where
    State: Copy + Clone + Eq + Hash + Debug,
{
    // Marks all transitions of an automaton with a given marker.
    //
    // Note: Safety check: panics if an already marked transition is found. Should
    // already be enforced by the invariant that nested markers are rejected
    // when constructing regular expression in `regex.rs`.
    pub(super) fn add_marker(self, index: usize) -> Self {
        let transitions = self
            .transitions
            .iter()
            .map(|(source, letter, target)| {
                (
                    *source,
                    letter.map(|a| {
                        assert!(a.marker == 0, "(bug) non-nested markers were not enforced");
                        Letter { marker: index, ..a }
                    }),
                    *target,
                )
            })
            .collect::<Vec<_>>();
        Self {
            transitions,
            ..self
        }
    }
}

impl<State> RawAutomaton<State>
where
    State: Clone + Eq + Hash + Debug,
{
    // Adds the set of successors of a given state inside an accumulator, except
    // those belonging to `visited`.
    fn add_next_states(&self, accu: &mut Vec<State>, visited: &HashSet<State>, state: &State) {
        self.transitions.iter().for_each(|(source, _, target)| {
            if *source == *state && !visited.contains(target) {
                accu.push(target.clone());
            }
        });
    }

    // Adds the set of predecessors of a given state inside an accumulator, except
    // those belonging to `visited`.
    fn add_prev_states(&self, accu: &mut Vec<State>, visited: &HashSet<State>, state: &State) {
        self.transitions.iter().for_each(|(source, _, target)| {
            if *target == *state && !visited.contains(source) {
                accu.push(source.clone());
            }
        });
    }

    // Computing forward reachable states from the initial state.
    fn reachable_states(&self) -> HashSet<State> {
        let mut reach_states = HashSet::new();
        let mut pending_states = Vec::with_capacity(self.nb_states);
        pending_states.push(self.initial_state.clone());

        while let Some(current_state) = pending_states.pop() {
            if reach_states.insert(current_state.clone()) {
                self.add_next_states(&mut pending_states, &reach_states, &current_state);
            }
        }
        reach_states
    }

    // Inserts in the accumulator `accu` all transitions of the form `(state,a,s)`,
    // where a sequence of transitions
    //
    // state -> s1 -> ... -> sn -> s
    //
    // exists in `self`, with all these transitions being epsilon transitions,
    // except sn -> s which is labelled by `a`. The function additionally returns a
    // boolean indicating whether a final state of `self` is epsilon-reachable from
    // `state`.
    fn epsilon_closure(
        &self,
        accu: &mut HashSet<(State, Option<Letter>, State)>,
        state: &State,
    ) -> bool {
        let mut visited = HashSet::new();
        let mut pending_states = Vec::with_capacity(self.nb_states);
        pending_states.push(state);
        visited.insert(state);
        let mut is_final = false;

        while let Some(current_state) = pending_states.pop() {
            is_final = is_final || self.final_states.contains(current_state);
            self.transitions
                .iter()
                .for_each(|(source, letter, target)| {
                    if source == current_state {
                        match *letter {
                            None => {
                                if visited.insert(target) {
                                    pending_states.push(target);
                                }
                            }
                            Some(a) => {
                                accu.insert((state.clone(), Some(a), target.clone()));
                            }
                        }
                    }
                });
        }
        is_final
    }

    // Computes the set of states of an automaton that are both reachable from the
    // initial state, and can reach a final state.
    fn live_states(&self) -> HashSet<State> {
        let reach_states = self.reachable_states();
        let mut back_reach_states = HashSet::new();
        let mut visited = HashSet::new();
        let mut pending_states = Vec::with_capacity(self.nb_states);

        // Computing backward reachable states from final states.
        self.final_states
            .iter()
            .for_each(|s| pending_states.push(s.clone()));
        while let Some(current_state) = pending_states.pop() {
            if visited.insert(current_state.clone())
                && reach_states.contains(&current_state.clone())
            {
                back_reach_states.insert(current_state.clone());
                self.add_prev_states(&mut pending_states, &visited, &current_state);
            }
        }
        back_reach_states
    }
}

impl<State> RawAutomaton<State>
where
    State: Clone + Eq + Hash + Debug,
{
    /// Converts the set of states into `usize`. Allows in particular to ensure
    /// states now have the Hash trait. Also, removes non reachable states, or
    /// states that are not backward-reachable from the final states. Preserves
    /// determinism but *not* completeness, since dead states are removed;
    /// therefore the field `deterministic_and_complete` is set to `false`.
    pub(super) fn normalise_states(&self) -> RawAutomaton<usize> {
        let mut states_numbering = HashMap::new();
        let mut counter: usize = 0;
        let live_states = self.live_states();
        live_states.iter().for_each(|state| {
            states_numbering.insert(state, counter);
            counter += 1
        });
        if counter == 0 {
            return RawAutomaton::empty();
        }
        let initial_state = *states_numbering.get(&self.initial_state).unwrap();
        let final_states = self
            .final_states
            .iter()
            .filter_map(|state| states_numbering.get(state).copied())
            .collect::<HashSet<_>>();
        let transitions = self
            .transitions
            .iter()
            .filter_map(|(source, letter, target)| {
                states_numbering.get(source).and_then(|source| {
                    states_numbering
                        .get(target)
                        .map(|target| (*source, *letter, *target))
                })
            })
            .collect::<Vec<_>>();
        RawAutomaton {
            nb_states: counter,
            deterministic_and_complete: false, /* Only reachable and backward-reachable states
                                                * are kept, hence
                                                * the automaton may not be complete. */
            epsilon_transitions: self.epsilon_transitions,
            initial_state,
            final_states,
            transitions,
        }
    }
}

// Implementation of determinisation.
impl<State> RawAutomaton<State>
where
    State: Copy + Clone + Eq + Hash + Debug,
{
    // Mutates the argument into an equivalent automaton without epsilon
    // transitions.
    //
    // Note: the result may contain non-backward-reachable states.
    pub(super) fn remove_epsilon_transitions(&mut self) {
        if !self.epsilon_transitions {
            return;
        }
        let mut transitions = HashSet::new();
        let mut final_states = self.final_states.clone();
        let mut pending = self.transitions.clone();
        while let Some((source, _, _)) = pending.pop() {
            pending = pending
                .iter()
                .filter(|(s, _, _)| source != *s)
                .copied()
                .collect::<Vec<_>>();
            if self.epsilon_closure(&mut transitions, &source) {
                final_states.insert(source);
            }
        }
        let transitions = transitions.iter().copied().collect::<Vec<_>>();
        self.final_states = final_states;
        self.transitions = transitions;
        self.epsilon_transitions = false;
    }

    // Computes a deterministic version of an automaton. Uses the standard
    // powerset automaton construction, and then renames the states as `usize`.
    // Mutates the argument to remove epsilon transitions.
    //
    // Note: the final automaton is a deterministic *and complete* automaton. In
    // particular, calling `normalise_states` afterwards will break this property.
    fn determinise_raw(&mut self, alphabet_size: usize, markers: &[usize]) -> RawAutomaton<usize> {
        // The determinisation operates with integer states for simplicity, and is only
        // valid if there is no epsilon transitions anymore.
        self.remove_epsilon_transitions();
        let base = self.normalise_states();

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
        }
    }
}

impl RawAutomaton<usize> {
    // Computes a deterministic version of an automaton. Less redundant than
    // `determinise_raw` since it can check whether the automaton is already
    // deterministic. Also, mutates the argument so that cloning is not needed when
    // the input is already deterministic and complete.
    pub(super) fn determinise(&mut self, alphabet_size: usize, markers: &[usize]) {
        assert!(
            !self.deterministic_and_complete || !self.epsilon_transitions,
            "(bug) [deterministic] and [epsilon_transitions] fields are not correctly enforced. {:?}",
            self
        );
        if !self.deterministic_and_complete {
            *self = self.determinise_raw(alphabet_size, markers);
        }
    }

    // Computes an automaton for the complement of a language.
    // Assumes that all states are numbered from 0 to `self.nb_states - 1`, and that
    // the automaton is deterministic and complete. Mutates the argument.
    pub(super) fn complement(&mut self) {
        assert!(
            self.deterministic_and_complete,
            "(bug) complement can only be performed on deterministic and complete automata"
        );
        self.final_states = (0..self.nb_states)
            .filter(|i| !self.final_states.contains(i))
            .collect::<HashSet<_>>();
    }

    // Computes an automaton for the iteration (Kleene star) of a language. Putting
    // `strict` as true requires that at least one iteration is done, whereas
    // `strict` set as false always allows for the empty word (epsilon) to be
    // accepted.
    //
    // Assumes that all states are numbered from 0 to `self.nb_states - 1`. Mutates
    // the argument.
    pub(super) fn repeat(&mut self, strict: bool) {
        let old_initial_state = self.initial_state;
        self.initial_state = self.nb_states;
        self.nb_states += 1;
        self.final_states
            .iter()
            .for_each(|&state| self.transitions.push((state, None, self.initial_state)));
        self.transitions
            .push((self.initial_state, None, old_initial_state));
        self.epsilon_transitions = true;
        self.deterministic_and_complete = false;
        if !strict {
            self.final_states.insert(self.initial_state);
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
            let elt = class.iter().enumerate().find(|(_, &b)| b).unwrap().0;
            if self.final_states.contains(&elt) {
                final_states.insert(*index);
            }
        });
        let mut transitions: HashMap<(usize, u8), (usize, usize)> = HashMap::new();
        for (index1, class1) in partition.clone() {
            let source = class1.iter().enumerate().find(|(_, &b)| b).unwrap().0;
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

impl RawAutomaton<usize> {
    // Exhibits a path from the initial state to a given state in the automaton.
    // Panics if such a path does not exist, or if the automaton is not
    // deterministic (ignoring output-determinism).
    fn witness_reachability(&self, state: usize) -> Vec<u8> {
        // `reachability[s]` contains a minimal sequence of `Letter` that can be read to
        // reach `state` from `s`.
        let mut reachability = vec![None; self.nb_states];
        reachability[state] = Some(vec![]);
        // `pending` contains some states that have recently been assigned a path in
        // `reachability`.
        let mut pending = vec![state];
        // Main loop, extending paths backwards from pending states.
        while let Some(pending_state) = pending.pop() {
            if reachability[self.initial_state].is_some() {
                break;
            }
            for (source, letter, target) in &self.transitions {
                if *target == pending_state && reachability[*source].is_none() {
                    let letter = letter.expect("(bug) witness_reachability has been called on an automaton with epsilon transitions");
                    let path = reachability[pending_state].as_ref().unwrap();
                    let extended_path = once(letter.char)
                        .chain(path.iter().copied())
                        .collect::<Vec<_>>();
                    reachability[*source] = Some(extended_path);
                    pending.push(*source);
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
            state_bound: self.state_bound + offset,
            initial_state: self.initial_state + offset,
            final_states: self
                .final_states
                .iter()
                .map(|s| s + offset)
                .collect::<HashSet<_>>(),
            transitions: self
                .transitions
                .iter()
                .map(|((source, letter), (target, marker))| {
                    ((*source + offset, *letter), (*target + offset, *marker))
                })
                .collect::<HashMap<_, _>>(),
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
        let mut output = Vec::new();
        let mut states = Vec::new();
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

    // Tests whether a given regular expression accepts or rejects two sets of
    // corresponding strings. Takes the alphabet size as a parameter to allow for
    // more readable tests with a restricted byte alphabet.
    pub(crate) fn automaton_one_test(
        index: usize,
        alphabet_size: usize,
        regex: &Regex,
        accepted: &[(&[u8], &[usize])],
        rejected: &[&[u8]],
    ) {
        accepted.iter().for_each(|(s,o)|
            assert!(s.len() == o.len(),
            "[test {index}] There is probably a typo in the tests vectors: the input ({:?}, length = {}) and the expected output ({:?}, length = {}) have different lengths.", 
            s, s.len(), o, o.len())
        );
        let automaton = regex.to_automaton_param(alphabet_size);
        println!(
            "\n\n** TEST no {index}\n** alphabet size = {alphabet_size}\n** automaton {:?}",
            automaton
        );
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
        ];
        regex
            .iter()
            .enumerate()
            .for_each(|(index, (regex, accepted, rejected))| {
                automaton_one_test(index, 3, regex, accepted, rejected)
            });
    }
}

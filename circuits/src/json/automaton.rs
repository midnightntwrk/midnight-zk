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
    hash::Hash,
};

use super::RegexLetter;

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
    /// The set of transitions, including epsilon-transitions.
    transitions: Vec<(State, Option<RegexLetter>, State)>,
}

/// A simple model of a deterministic (but not complete) finite automaton
/// operating on bytes. The set of states is implicitly represented by the range
/// `0..nb_states`.
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
    /// `transitions[state][letter]` gives the transition target when in state
    /// `state`, reading input `letter`. Can be undefined, in which case it
    /// means the automaton jumps into an implicit deadlock state.
    pub transitions: HashMap<(usize, RegexLetter), usize>,
}

impl RawAutomaton<usize> {
    // Creates an empty automaton with a unique default state.
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

    // Creates an automaton recognising only the empty word.
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

    // Creates an automaton recognising a singleton language: `Some(a)` makes it
    // accept {a} and `None` makes it accept any word of length 1.
    pub(super) fn singleton(
        letter: Option<RegexLetter>,
        alphabet_size: usize,
    ) -> RawAutomaton<usize> {
        Self {
            nb_states: 2,
            deterministic_and_complete: false,
            epsilon_transitions: false,
            initial_state: 0,
            final_states: HashSet::from([1]),
            transitions: {
                match letter {
                    None => (0..alphabet_size)
                        .map(|i| (0, Some(i as RegexLetter), 1))
                        .collect::<Vec<_>>(),
                    Some(_) => vec![(0, letter, 1)],
                }
            },
        }
    }
}

impl<State> RawAutomaton<State>
where
    State: Copy + Clone + Eq + Hash + std::fmt::Debug,
{
    // Adds the set of successors of a given state inside an accumulator, except
    // those belonging to `visited`.
    fn add_next_states(&self, accu: &mut Vec<State>, visited: &HashSet<State>, state: &State) {
        self.transitions.iter().for_each(|(source, _, target)| {
            if *source == *state && !visited.contains(target) {
                accu.push(*target);
            }
        });
    }

    // Adds the set of predecessors of a given state inside an accumulator, except
    // those belonging to `visited`.
    fn add_prev_states(&self, accu: &mut Vec<State>, visited: &HashSet<State>, state: &State) {
        self.transitions.iter().for_each(|(source, _, target)| {
            if *target == *state && !visited.contains(source) {
                accu.push(*source);
            }
        });
    }

    // Computing forward reachable states from the initial state.
    fn reachable_states(&self) -> HashSet<State> {
        let mut reach_states = HashSet::new();
        let mut pending_states = Vec::with_capacity(self.nb_states);
        pending_states.push(self.initial_state);

        while let Some(current_state) = pending_states.pop() {
            if reach_states.insert(current_state) {
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
        accu: &mut HashSet<(State, Option<RegexLetter>, State)>,
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
                                accu.insert((*state, Some(a), *target));
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
            .for_each(|s| pending_states.push(*s));
        while let Some(current_state) = pending_states.pop() {
            if visited.insert(current_state) && reach_states.contains(&current_state) {
                back_reach_states.insert(current_state);
                self.add_prev_states(&mut pending_states, &visited, &current_state);
            }
        }
        back_reach_states
    }
}

// Implementation of determinisation and state normalisation.
impl<State> RawAutomaton<State>
where
    State: Copy + Clone + Eq + Hash + std::fmt::Debug,
{
    // Converts the set of states into `usize`. Allows in particular to ensure
    // states now have the Copy and Hash traits. Also, removes non reachable
    // states, or non-backward-reachable states from the final states. Preserves
    // determinism but *not* completeness, since dead states are removed; therefore
    // the field `deterministic_and_complete`
    // is set to `false`.
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

    // Mutates the argument into an equivalent automaton without epsilon
    // transitions.
    //
    // Note: the result may contain non-backward-reachable states.
    fn remove_epsilon_transitions(&mut self) {
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
    // "set-of-states" automaton construction, and then renames the states to make
    // them integers. Mutates the argument to remove epsilon transitions.
    //
    // Note: the final automaton is a deterministic *and complete* automaton. In
    // particular, calling `normalise_states` usually breaks completeness (and
    // completeness is needed, e.g., for the `complement` operation).
    fn determinise_raw(&mut self, alphabet_size: usize) -> RawAutomaton<usize> {
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
                let mut successors = vec![vec![false; base.nb_states]; alphabet_size];
                base.transitions
                    .iter()
                    .for_each(|(source, letter, target)| {
                        if power_state[*source] {
                            successors[letter.unwrap() as usize][*target] = true
                        }
                    });
                successors.iter().enumerate().for_each(|(letter, target)| {
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
                    (Some(source), Some(target)) => (*source, Some(*letter as u8), *target),
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
    State: Copy + Clone + Eq + Hash + std::fmt::Debug,
{
    // Puts two automata "side-by-side", without connecting their states, and with
    // an empty set of final states. The initial state is `(None,None)` but is not
    // connected to the rest of the automaton, this function is only meant to be
    // used as a precomputation for other automaton methods. The `with_capacity`
    // argument indicates the expected number of transitions of the final automaton.
    fn weak_union<S>(
        &self,
        rhs: &RawAutomaton<S>,
        with_capacity: usize,
    ) -> RawAutomaton<(Option<State>, Option<S>)>
    where
        S: Copy + Clone + Eq + Hash,
    {
        let mut transitions = Vec::with_capacity(with_capacity);
        self.transitions
            .iter()
            .for_each(|(source, letter, target)| {
                transitions.push(((Some(*source), None), *letter, (Some(*target), None)))
            });
        rhs.transitions.iter().for_each(|(source, letter, target)| {
            transitions.push(((None, Some(*source)), *letter, (None, Some(*target))))
        });
        RawAutomaton {
            nb_states: self.nb_states + rhs.nb_states,
            deterministic_and_complete: false,
            epsilon_transitions: self.epsilon_transitions || rhs.epsilon_transitions,
            initial_state: (None, None),
            final_states: HashSet::new(),
            transitions,
        }
    }

    // Computes an automaton for the union of two languages.
    pub(super) fn union<S>(&self, rhs: &RawAutomaton<S>) -> RawAutomaton<(Option<State>, Option<S>)>
    where
        S: Copy + Clone + Eq + Hash,
    {
        let mut base = self.weak_union(rhs, self.transitions.len() + rhs.transitions.len() + 2);
        base.nb_states += 1;
        base.transitions
            .push(((None, None), None, (Some(self.initial_state), None)));
        base.transitions
            .push(((None, None), None, (None, Some(rhs.initial_state))));
        base.final_states = (self.final_states.iter().map(|&state| (Some(state), None)))
            .chain(rhs.final_states.iter().map(|&state| (None, Some(state))))
            .collect::<HashSet<_>>();
        base.epsilon_transitions = true;
        base.deterministic_and_complete = false;
        base
    }

    // Computes an automaton for the concatenation of two languages.
    pub(super) fn concat<S>(
        &self,
        rhs: &RawAutomaton<S>,
    ) -> RawAutomaton<(Option<State>, Option<S>)>
    where
        S: Copy + Clone + Eq + Hash + std::fmt::Debug,
    {
        let mut base = self.weak_union(
            rhs,
            self.transitions.len() + rhs.transitions.len() + self.final_states.len(),
        );
        base.initial_state = (Some(self.initial_state), None);
        self.final_states.iter().for_each(|&state| {
            base.transitions
                .push(((Some(state), None), None, (None, Some(rhs.initial_state))));
        });
        base.final_states = rhs
            .final_states
            .iter()
            .map(|&state| (None, Some(state)))
            .collect::<HashSet<_>>();
        base.epsilon_transitions = true;
        base.deterministic_and_complete = false;
        base
    }
}

impl RawAutomaton<usize> {
    // Computes a deterministic version of an automaton. Less redundant than
    // `determinise_raw` since it can check whether the automaton is already
    // deterministic. Also, mutates the argument so that cloning is not needed when
    // the input is already deterministic and complete.
    pub(super) fn determinise(&mut self, alphabet_size: usize) {
        debug_assert!(
            !self.deterministic_and_complete || !self.epsilon_transitions,
            "[deterministic] and [epsilon_transitions] fields are not correctly enforced. {:?}",
            self
        );
        if !self.deterministic_and_complete {
            *self = self.determinise_raw(alphabet_size);
        }
    }

    // Computes an automaton for the complement of a language.
    // Assumes that all states are numbered from 0 to `self.nb_states - 1`, and that
    // the automaton is deterministic and complete. Mutates the argument.
    pub(super) fn complement(&mut self) {
        assert!(self.deterministic_and_complete);
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
    fn nerode_congruence(&self) -> (Vec<Vec<bool>>, usize) {
        let alphabet_size = self
            .transitions
            .iter()
            .map(|((_, a), _)| 1 + *a as usize)
            .max()
            .unwrap_or(0);
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
            // the distinguisher by reading this letter.
            let mut predecessors = vec![vec![false; self.state_bound]; alphabet_size];
            for ((source, a), target) in self.transitions.iter() {
                if dist[*target] {
                    predecessors[*a as usize][*source] = true;
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
        (partition, alphabet_size)
    }

    // Implementation of minimisation using the Nerode's congruence. It simply
    // numbers each equivalence class, and generates the transitions between the
    // different classes accordingly.
    fn minimise(&self) -> Self {
        let (partition, alphabet_size) = self.nerode_congruence();
        let partition = partition.iter().cloned().enumerate().collect::<Vec<_>>();
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
        let mut transitions = HashMap::new();
        for (index1, class1) in partition.clone() {
            let source = class1.iter().enumerate().find(|(_, &b)| b).unwrap().0;
            for letter in 0..alphabet_size {
                self.transitions
                    .get(&(source, letter.try_into().unwrap()))
                    .iter()
                    .for_each(|&&target| {
                        let index2 = partition.iter().find(|(_, class)| class[target]).unwrap().0;
                        transitions.insert((index1, letter.try_into().unwrap()), index2);
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
    /// Conversion into a minimal deterministic automaton. Mutates the argument
    /// to normalise it.
    pub(super) fn normalise(&mut self, alphabet_size: usize) -> Automaton {
        self.determinise(alphabet_size);
        *self = self.normalise_states();
        let mut transitions = HashMap::new();
        self.transitions
            .iter()
            .for_each(|(source, letter, target)| match letter {
                None => panic!("determinisation failed to remove an epsilon transition. The automaton is:\n{:?}\n\n", self),
                Some(letter) => {match transitions.insert((*source, *letter), *target) {
                    None => (),
                    Some(target2) => panic!("determinisation was incorrect: source state {source} was pointing to both targets {target} and {target2} after letter {letter}")
                }},
            });
        Automaton {
            state_bound: self.nb_states,
            initial_state: self.initial_state,
            final_states: self.final_states.clone(),
            transitions,
        }
        .minimise()
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
                .map(|((source, letter), target)| ((*source + offset, *letter), *target + offset))
                .collect::<HashMap<_, _>>(),
        }
    }
}

#[cfg(test)]
impl Automaton {
    /// Executes an automaton for a given sequence of bytes. Returns a vector of
    /// states, corresponding to the states of the run, and a boolean indicating
    /// whether the run was stuck.
    pub(super) fn run(&self, input: &[u8]) -> (Vec<usize>, bool) {
        let mut iter = input.iter();
        let mut current_state = self.initial_state;
        let mut states = Vec::new();
        let mut letter = iter.next();
        states.push(current_state);
        // Iterates over the letters of the input and moves accross the states
        // accordingly.
        while letter.is_some() {
            match self
                .transitions
                .get(&(current_state, *letter.unwrap()))
                .copied()
            {
                // Interrupted run.
                None => return (states, true),
                // The run goes on.
                Some(state) => {
                    current_state = state;
                    states.push(current_state);
                    letter = iter.next();
                }
            }
        }
        (states, false)
    }
}

#[cfg(test)]
pub(super) mod tests {
    use itertools::Itertools;

    use crate::json::regex::{Regex, RegexInstructions};

    // Tests whether a given regular expression accepts or rejects two sets of
    // corresponding strings. Takes the alphabet size as a parameter to allow for
    // more readable tests with a restricted byte alphabet.
    pub(crate) fn automaton_one_test(
        index: usize,
        alphabet_size: usize,
        regex: &Regex,
        accepted: &[&[u8]],
        rejected: &[&[u8]],
    ) {
        let automaton = regex.to_automaton_param(alphabet_size);
        println!(
            "\n\n** TEST no {index}\n** alphabet size = {alphabet_size}\n** {:?}\n** converted to {:?}",
            regex, automaton
        );
        accepted.iter().for_each(|&s| {
            println!(
                "\n -> testing on input string \"{}\" (bytes: [{}])", String::from_utf8_lossy(s),
                s.iter().map(|b| b.to_string()).join(", ")
            );
            let (v,interrupted) = automaton.run(s);
            if interrupted {
                panic!("input was unexpectedly rejected after being stuck after {} transitions", v.len())
            }
            else {
                let counter = v.len();
                let state = v[counter-1];
                let f = automaton.final_states.contains(&state);
                if f {
                    println!("... which is accepted as expected (the automaton reached the final state {} in {} transitions).", state, counter)
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
            let (v,interrupted) = automaton.run(s);
            if interrupted {
                println!("... which is rejected as expected (the automaton run was stuck after {} transitions).", v.len())
            } else {
                let counter = v.len();
                let state = v[counter-1];
                    let f = automaton.final_states.contains(&state);
                    if f {
                        panic!("input was unexpectedly accepted (reached final state {} after {} transitions).", state, counter)
                    } else {
                        println!("... which is rejected as expected (the automaton run ended up in the non-final state {} after {} transitions).", state, counter)
                    }
            }
        });
    }

    #[test]
    fn automaton_test() {
        let regex0 = Regex::once(1);
        let accepted0: &[&[u8]] = &[&[1]];
        let rejected0: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 1], &[2]];

        let regex1 = Regex::once(1).terminated(Regex::once(2));
        let accepted1: &[&[u8]] = &[&[1, 2]];
        let rejected1: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 1], &[1, 2, 0]];

        let regex2 = Regex::cat([Regex::once(1), Regex::list(Regex::once(2)), Regex::once(0)]);
        let accepted2: &[&[u8]] = &[&[1, 0], &[1, 2, 0], &[1, 2, 2, 0], &[1, 2, 2, 2, 0]];
        let rejected2: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 1], &[1, 0, 2], &[1, 2]];

        let regex3 = Regex::cat([
            Regex::once(1),
            Regex::non_empty_list(Regex::once(2)),
            Regex::list(Regex::once(0)),
        ]);
        let accepted3: &[&[u8]] = &[&[1, 2, 0], &[1, 2], &[1, 2, 2, 0], &[1, 2, 2, 2, 0]];
        let rejected3: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 0], &[1, 1], &[1, 0, 2], &[1, 2, 1]];

        let regex4 = Regex::minus(Regex::once(1), Regex::once(1));
        let accepted4: &[&[u8]] = &[];
        let rejected4: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 0], &[1, 1], &[1, 0, 2], &[1, 2]];

        let regex5 = Regex::minus(
            Regex::list(Regex::once_any()),
            Regex::list(Regex::or([Regex::once(0), Regex::once(1)])),
        );
        let accepted5: &[&[u8]] = &[
            &[2],
            &[0, 2],
            &[2, 1],
            &[0, 2, 1],
            &[0, 2, 2, 1, 2],
            &[2, 1, 2, 0, 1, 1],
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

        let regex6 = Regex::minus(
            regex5.clone(),
            Regex::minus(
                Regex::list(Regex::once_any()),
                Regex::list(Regex::minus(Regex::once_any(), Regex::once(2))),
            ),
        );
        let accepted6: &[&[u8]] = &[];
        let rejected6: &[&[u8]] = &[&[0], &[], &[0, 1], &[1, 0], &[1, 1], &[1, 0, 2], &[1, 2]];

        let regex7 = Regex::minus(
            Regex::list(Regex::minus(Regex::once_any(), Regex::once(2))),
            Regex::once(0),
        );
        let accepted7: &[&[u8]] = &[&[], &[0, 1], &[0, 0], &[1, 0], &[1, 1], &[0, 1, 0, 1, 0]];
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

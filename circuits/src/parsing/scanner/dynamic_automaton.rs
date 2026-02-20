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

//! Dynamic automaton parsing: uses dynamic (self-referential) lookups to parse
//! arbitrary regular expressions at runtime.

use std::{collections::BTreeMap, hash::Hash};

use crate::CircuitField;
use midnight_proofs::{
    circuit::{Layouter, Region},
    plonk::Error,
};

use super::{NativeAutomaton, Regex, ScannerChip, ALPHABET_MAX_SIZE};
use crate::{
    field::AssignedNative, instructions::AssignmentInstructions,
    parsing::scanner::DYNAMIC_AUTOMATON_PADDING, types::AssignedByte,
};

impl<F> NativeAutomaton<F>
where
    F: Ord + CircuitField,
{
    /// Extracts all transitions in chain order, suitable for loading as a
    /// dynamic lookup table. When possible, a transition with target state `s`
    /// is followed by a transition with source state `s`. When the chain
    /// breaks, a padding row is inserted. Final-state rows are appended at the
    /// end.
    ///
    /// Returns `(source, letter, marker)` triples.
    fn dynamic_transition_table(&self) -> Vec<(F, F, F)> {
        // Build a mutable structure where we can pop transitions per state.
        let mut remaining: BTreeMap<F, Vec<(F, F, F)>> = BTreeMap::new();
        for (&source, inner) in &self.transitions {
            let entries: Vec<(F, F, F)> = inner
                .iter()
                .map(|(&letter, &(target, marker))| (letter, target, marker))
                .collect();
            remaining.insert(source, entries);
        }

        let total: usize = remaining.values().map(|v| v.len()).sum();
        let mut table = Vec::with_capacity(total + remaining.len() + self.final_states.len());
        let mut current_state = self.initial_state;
        let padding = F::from(DYNAMIC_AUTOMATON_PADDING as u64);

        loop {
            if let Some(entries) = remaining.get_mut(&current_state) {
                if let Some((letter, target, marker)) = entries.pop() {
                    table.push((current_state, letter, marker));
                    current_state = target;
                    continue;
                }
            }
            // Chain break: padding row.
            table.push((current_state, padding, F::ZERO));
            match remaining.iter().find(|(_, v)| !v.is_empty()) {
                Some((&s, _)) => current_state = s,
                None => break,
            }
        }

        // Final-state check rows. After each of them, one needs to insert a row that
        // starts with a 0 and that cannot be interpreted as a valid transition.
        for &state in &self.final_states {
            table.push((state, F::from(ALPHABET_MAX_SIZE as u64), F::ZERO));
            table.push((F::ZERO, F::ZERO, F::ZERO));
        }
        table
    }
}

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: CircuitField + Ord,
{
    /// Load the full transition table of a dynamic automaton using the
    /// chain-ordered output of `dynamic_transition_table`. Each row contains
    /// (source, letter, output) as constants. Also returns which field element
    /// has to be added in the final row to check for final states.
    fn assign_dynamic_automaton_table(
        &self,
        layouter: &mut impl Layouter<F>,
        automaton: &NativeAutomaton<F>,
    ) -> Result<(), Error> {
        let table = automaton.dynamic_transition_table();
        layouter.assign_region(
            || "dynamic automaton table",
            |mut region| {
                for (offset, &(source, letter, output)) in table.iter().enumerate() {
                    region.assign_advice_from_constant(
                        || "dyn table source",
                        self.config.state_col,
                        offset,
                        source,
                    )?;
                    region.assign_advice_from_constant(
                        || "dyn table letter",
                        self.config.letter_col,
                        offset,
                        letter,
                    )?;
                    region.assign_advice_from_constant(
                        || "dyn table output",
                        self.config.output_col,
                        offset,
                        output,
                    )?;
                }
                Ok(())
            },
        )
    }

    /// Applies one transition of a dynamic automaton run. Analogous to
    /// `apply_one_transition` but uses the dynamic lookup columns
    /// (`q_dynamic`) instead of the fixed table.
    ///
    /// Assumes `state` is already assigned at `state_col[offset]`. Enables
    /// `q_dynamic`, copies the letter, computes the transition, writes
    /// `output_col` at the current offset, then writes the next state at
    /// `state_col[offset+1]`.
    fn apply_one_dynamic_transition(
        &self,
        region: &mut Region<'_, F>,
        automaton: &NativeAutomaton<F>,
        state: &mut AssignedNative<F>,
        letter: &AssignedByte<F>,
        markers: &mut Vec<AssignedNative<F>>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_dynamic.enable(region, *offset)?;

        // Assigning input letter at the current offset.
        let letter_native = AssignedNative::from(letter);
        letter_native.copy_advice(
            || "dyn parse letter",
            region,
            self.config.letter_col,
            *offset,
        )?;

        // Gets the next state and outputs from the transition table (off-circuit).
        let target_opt_value = state
            .value()
            .zip(letter_native.value())
            .map(|(s, l)| automaton.get_transition(s, l));
        target_opt_value.error_if_known_and(|o| o.is_none())?;
        let target_value = target_opt_value.map(|o| o.unwrap());
        let next_state_value = target_value.map(|t| t.0);
        let next_output_value = target_value.map(|t| t.1);

        // Assigning the output.
        let output = region.assign_advice(
            || "dyn parse output",
            self.config.output_col,
            *offset,
            || next_output_value,
        )?;
        markers.push(output);

        // Next state at the next row.
        *offset += 1;
        *state = region.assign_advice(
            || "dyn parse next state",
            self.config.state_col,
            *offset,
            || next_state_value,
        )?;
        Ok(())
    }

    /// Analogous to `assert_final_state` but for the dynamic lookup.
    fn assert_dynamic_final_state(
        &self,
        region: &mut Region<'_, F>,
        invalid_letter: AssignedNative<F>,
        zero: AssignedNative<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_dynamic.enable(region, *offset)?;
        invalid_letter.copy_advice(
            || format!("dyn final letter ({})", ALPHABET_MAX_SIZE),
            region,
            self.config.letter_col,
            *offset,
        )?;
        zero.copy_advice(
            || "dyn final output (0)",
            region,
            self.config.output_col,
            *offset,
        )?;
        *offset += 1;
        zero.copy_advice(
            || "dyn final target (0)",
            region,
            self.config.state_col,
            *offset,
        )?;
        Ok(())
    }

    /// Parses `input` against the automaton derived from `regex`, using dynamic
    /// lookups. Unlike [`parse_static`], this method does not require the
    /// automaton to be baked into the circuit configuration. Instead, each
    /// distinct `regex` is lazily converted into a [`NativeAutomaton`],
    /// assigned as a dynamic lookup table (selector OFF rows), and then the
    /// parse run is constrained via lookup rows (selector ON). A caching
    /// mechanism ensures that a given regex is only converted and loaded
    /// once.
    pub(super) fn parse_dynamic(
        &self,
        layouter: &mut impl Layouter<F>,
        regex: &Regex,
        input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        // Cache lookup: obtain automaton and whether the table needs to
        // be assigned (i.e. this is the first time we see this regex).
        let (automaton, table_needs_assignment) = {
            let mut cache = self.regex_cache.borrow_mut();
            if let Some(aut) = cache.get(regex) {
                // Cache hit.
                (aut.clone(), false)
            } else {
                // Cache miss.
                let raw_automaton = regex.to_automaton();
                let offset = {
                    let mut max_state = self.dynamic_max_state.borrow_mut();
                    let val = *max_state as usize;
                    *max_state += raw_automaton.nb_states as u64;
                    val
                };
                let native: NativeAutomaton<F> = raw_automaton.offset_states(offset).into();
                cache.insert(regex.clone(), native.clone());
                (native, true)
            }
        };

        // Assign the table rows if this is a new automaton.
        if table_needs_assignment {
            self.assign_dynamic_automaton_table(layouter, &automaton)?;
        }

        // Pre-assign constants.
        let invalid_letter: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(ALPHABET_MAX_SIZE as u64))?;
        let zero: AssignedNative<F> = self.native_gadget.assign_fixed(layouter, F::ZERO)?;

        // Assign the parse run (q_dynamic ON rows).
        layouter.assign_region(
            || "dynamic parsing layout",
            |mut region| {
                let mut offset = 0;
                let mut markers = Vec::with_capacity(input.len());

                let mut state = region.assign_advice_from_constant(
                    || "dyn initial state",
                    self.config.state_col,
                    offset,
                    automaton.initial_state,
                )?;

                for letter in input {
                    self.apply_one_dynamic_transition(
                        &mut region,
                        &automaton,
                        &mut state,
                        letter,
                        &mut markers,
                        &mut offset,
                    )?;
                }

                self.assert_dynamic_final_state(
                    &mut region,
                    invalid_letter.clone(),
                    zero.clone(),
                    &mut offset,
                )?;

                Ok(markers)
            },
        )
    }
}

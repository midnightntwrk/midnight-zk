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

//! Module implementing chips and gadgets to process JSON objects.

mod base64_chip;
mod data_types;
mod native_automaton;
mod parser_gadget;
mod specs;

/// A module to convert regular expressions to finite automata that can be used
/// as basis for circuit gates.
mod automaton;
/// A module containing the definitions of the automata that will be loaded in
/// the standard library.
pub mod automaton_chip;

/// Number of bytes that are read at each automaton transition.
///
/// The default value is 1, and already exhibits gut performances. Choosing a
/// value greater than 1 (in practice: 2) may severly increase the size of the
/// lookup table representing the automaton. Typical examples stay in the domain
/// of k=10~12 when `AUTOMATON_CHUNK_SIZE` is 1, but may typically require k=17
/// when `AUTOMATON_CHUNK_SIZE` is 2. The advantage is that the number of
/// circuit rows needed to parse an input is cut by a multiplicative factor of
/// `AUTOMATON_CHUNK_SIZE`.
///
/// Increasing this value is only meaningful for forks of this repository only
/// managing examples where:
/// 1. The main function `parsing::automaton_chip::parse` needs to be called
///    many times; and
/// 2. All automata involved in `parsing::specs` induce a moderate increase of
///    `k` when increasing `AUTOMATON_CHUNK_SIZE`. The deciding factor is the
///    number of substrings of length `AUTOMATON_CHUNK_SIZE` that may appear in
///    a word accepted by the automaton.
const AUTOMATON_CHUNK_SIZE: usize = 1;

/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;
/// A module to serialize automata as sequences of bytes.
mod serialization;

mod table;

pub use base64_chip::*;
pub use data_types::{DateFormat, Separator};
pub use native_automaton::NativeAutomaton;
pub use parser_gadget::*;
pub use specs::{spec_library, StdLibParser};

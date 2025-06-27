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

mod automaton_chip;
mod base64_chip;
mod data_types;
mod parser_gadget;

/// A module to convert regular expressions to finite automata that can be used
/// as basis for circuit gates.
pub mod automaton;
/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;

/// A letter from the automaton alphabet.
pub type RegexLetter = u8;
/// Maximal size of the alphabet, since input characters are represented by
/// `AssignedByte`. The parser (`automaton_chip::parse`) is using this
/// information to store automaton final states in the transition table, by
/// encoding them as impossible transitions starting from the said state, and
/// labelled with letter `REGEX_ALPHABET_MAX_SIZE`.
pub const REGEX_ALPHABET_MAX_SIZE: usize = 256;

mod table;

pub use automaton_chip::AutomatonChip;
pub use base64_chip::*;
pub use data_types::{DateFormat, Separator};
pub use parser_gadget::*;

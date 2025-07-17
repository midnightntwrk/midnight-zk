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
mod parser_gadget;
mod specs;

/// A module to convert regular expressions to finite automata that can be used
/// as basis for circuit gates.
pub mod automaton;
/// A module containing the definitions of the automata that will be loaded in
/// the standard library.
pub mod automaton_chip;
/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;

mod table;

pub use base64_chip::*;
pub use data_types::{DateFormat, Separator};
pub use parser_gadget::*;
pub use specs::{spec_library, StdLibParser};

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

use std::hash::Hash;

use ff::PrimeField;
use midnight_proofs::{
    circuit::Layouter,
    plonk::Error,
};

use super::{Regex, ScannerChip};
use crate::{field::AssignedNative, types::AssignedByte};

impl<LibIndex, F> ScannerChip<LibIndex, F>
where
    LibIndex: Eq + Hash,
    F: PrimeField + Ord,
{
    /// Parses `input` in-circuit w.r.t. a dynamically-provided regular
    /// expression and outputs the sequence of integers it produces.
    pub(super) fn parse_dynamic(
        &self,
        _layouter: &mut impl Layouter<F>,
        _regex: &Regex,
        _input: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        unimplemented!("dynamic automaton parsing will be implemented in a subsequent commit")
    }
}

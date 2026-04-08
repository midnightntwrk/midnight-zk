// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

use crate::{field::AssignedNative, verifier::SelfEmulation};

/// In-circuit verifier trace of a proof.
#[derive(Debug)]
pub struct VerifierTrace<S: SelfEmulation> {
    pub(crate) advice_commitments: Vec<S::AssignedPoint>,
    pub(crate) vanishing: super::vanishing::Committed<S>,
    pub(crate) lookups: Vec<super::lookup::Committed<S>>,
    pub(crate) trashcans: Vec<super::trash::Committed<S>>,
    pub(crate) permutations: super::permutation::Committed<S>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) theta: AssignedNative<S::F>,
    pub(crate) trash_challenge: AssignedNative<S::F>,
    pub(crate) y: AssignedNative<S::F>,
}

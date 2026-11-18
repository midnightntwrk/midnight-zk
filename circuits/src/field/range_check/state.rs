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

//! The assertions and decompositions recorded by the chips built on a
//! [RangeCheckConfig](super::RangeCheckConfig), shared through it.

use std::collections::HashMap;

use crate::{CircuitField, types::AssignedNative};

/// The state shared by the chips built on a configuration.
#[derive(Debug, Default)]
pub(super) struct State<F: CircuitField> {
    /// The assertions and decompositions recorded outside of any cost-model
    /// measurement window.
    pub(super) pending: Pending<F>,
    /// Cost model only: the assertions and decompositions recorded inside a
    /// cost-model measurement window, see
    /// [RangeCheckChip::load](super::RangeCheckChip::load).
    pub(super) pending_in_cost_window: Pending<F>,
    /// Whether the sentinel row is placed.
    pub(super) sentinel_placed: bool,
    /// Whether the chip is loaded.
    pub(super) loaded: bool,
}

/// Assertions and decompositions recorded and not yet laid out.
///
/// They are kept in recording order.
#[derive(Debug, Default)]
pub(super) struct Pending<F: CircuitField> {
    /// The assertions `x ∈ [0, 2^n)`, as `(x, n)`.
    pub(super) checks: Vec<(AssignedNative<F>, usize)>,
    /// The decompositions.
    pub(super) decompositions: Vec<Decomposition<F>>,
    /// The position in `checks` of the assertion on each element.
    ///
    /// An element asserted several times, directly or through its clones,
    /// keeps a single assertion, of its tightest bound.
    pub(super) index: HashMap<AssignedNative<F>, usize>,
}

/// A decomposition of `x` in little-endian limbs of `size` bits:
///
/// - `x = sum_i 2^(size i) limbs[i]`,
/// - `limbs[i] ∈ [0, 2^size)` for every `i`.
#[derive(Debug)]
pub(super) struct Decomposition<F: CircuitField> {
    pub(super) x: AssignedNative<F>,
    pub(super) limbs: Vec<AssignedNative<F>>,
    pub(super) size: usize,
}

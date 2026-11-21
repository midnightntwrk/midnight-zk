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

//! Parallel CPU paths of the prover (feature `prover-par`).
//!
//! Each function here computes exactly the values of the stock function it
//! replaces at its call site, bit for bit, whatever the thread count: no
//! random draw and no transcript operation happens in this module, so the
//! proof bytes do not depend on the feature.
#![allow(dead_code)]

pub(crate) mod columns;
pub(crate) mod invert;
pub(crate) mod layout;
pub(crate) mod open;
pub(crate) mod product;
#[cfg(test)]
mod testing;

// Size floors: below a floor the call site keeps the stock routine, where
// splitting into tasks costs more than the threads save.

/// Columns shorter than this are delta-encoded by the stock code.
pub(crate) const DELTA_MIN_LEN: usize = 1 << 14;

/// Chunks per pool thread in [`columns::parallelize`], so threads that finish
/// early take more.
pub(crate) const PARALLELIZE_CHUNKS_PER_THREAD: usize = 4;

/// [`columns::parallelize`] keeps the stock cut when its chunks would be
/// shorter than this.
pub(crate) const PARALLELIZE_MIN_CHUNK: usize = 1 << 10;

/// Polynomials shorter than this are divided by the stock `divide_by_roots`
/// and `kate_division`. Below it, the scan that joins the blocks costs about
/// as much as the stock loop.
pub(crate) const DIVISION_MIN_LEN: usize = 1 << 15;

/// Inner products of polynomials shorter than this use the stock helper of the
/// KZG multi-open. Below it, the smaller tasks cost more than the better
/// balance gains.
pub(crate) const INNER_PRODUCT_MIN_LEN: usize = 1 << 19;

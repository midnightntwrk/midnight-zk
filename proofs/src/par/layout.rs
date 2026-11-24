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

//! Region layout for a proving key without one from keygen (a key read
//! from bytes). The first proof stores the layout its shape pass measured in
//! `ProvingKey::region_starts_cache`; later proofs place their regions at the
//! stored starts and skip the shape pass.
//!
//! Invariant: in the shape pass of [`SimpleFloorPlanner`], a region's start
//! depends only on the columns, row counts and constants of the regions
//! before it. So each region is checked as it is assigned
//! ([`FloorPlanner::synthesize_checking_layout`]), not the layout as a whole:
//! a circuit that differs from the stored layout anywhere (region count,
//! columns, rows, constants, or a synthesis error) is detected. The prover
//! then discards the witness and reruns the stock shape pass, and keeps the
//! stored layout for later matching proofs.
//!
//! A region whose cells differ between the shape pass and the assignment is
//! caught by the first proof, which then stores no layout.
//!
//! [`SimpleFloorPlanner`]: crate::circuit::SimpleFloorPlanner

use std::sync::OnceLock;

use ff::Field;

use crate::{
    circuit::{
        RegionStart,
        layouter::{MeasuredLayout, SyncDeps},
    },
    plonk::{Assignment, Circuit, Column, Error, Fixed, FloorPlanner},
};

#[cfg(test)]
thread_local! {
    /// Proofs on this thread that failed the layout check.
    static RETRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Takes and clears the count of `RETRIES`.
#[cfg(test)]
pub(crate) fn take_retries() -> usize {
    RETRIES.with(|r| r.replace(0))
}

/// Synthesizes `circuit` into `cs` with the keygen layout, else with the
/// layout in `cache` if the circuit matches it, else (after `reset` empties
/// `cs`) with the stock shape pass. An empty `cache` stores the measured
/// layout.
pub(crate) fn synthesize<F, CS, C>(
    cs: &mut CS,
    reset: impl FnOnce(&mut CS),
    circuit: &C,
    config: C::Config,
    constants: Vec<Column<Fixed>>,
    keygen: Option<&[RegionStart]>,
    cache: &OnceLock<MeasuredLayout>,
) -> Result<(), Error>
where
    F: Field,
    CS: Assignment<F> + SyncDeps,
    C: Circuit<F>,
{
    if keygen.is_some() {
        return C::FloorPlanner::synthesize_with_cached_regions(
            cs, circuit, config, constants, keygen,
        );
    }
    if let Some(layout) = cache.get() {
        if C::FloorPlanner::synthesize_checking_layout(
            cs,
            circuit,
            config.clone(),
            constants.clone(),
            layout,
        ) {
            return Ok(());
        }
        #[cfg(test)]
        RETRIES.with(|r| r.set(r.get() + 1));
        reset(cs);
        return C::FloorPlanner::synthesize_with_cached_regions(
            cs, circuit, config, constants, None,
        );
    }
    if let Some(measured) =
        C::FloorPlanner::synthesize_measuring_layout(cs, circuit, config, constants)?
    {
        // A concurrent first proof may have stored its layout already.
        let _ = cache.set(measured);
    }
    Ok(())
}

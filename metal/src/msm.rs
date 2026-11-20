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

//! The G1 MSM: sppark's Pippenger MSM ported to Metal. The kernels are in
//! `shaders/msm.metal`, the curve formulas in `shaders/include/g1.h`. The host
//! side is ported from sppark `msm/pippenger.cuh` (Copyright Supranational
//! LLC, Apache-2.0, <https://github.com/supranational/sppark>, commit
//! 08033103c14ff3c742e710b9463dde42acc0f058).
//!
//! The path is chosen from public facts before any scalar is read: a
//! registered SRS table ([`register_srs`]) holding the caller's points, or,
//! only with an explicit threshold, the one-shot path on the caller's points.
//!
//! The device computes `MSM(s + r) - MSM(r)` with `r` a fixed public vector
//! (`shaders/include/msm.h`): without it, a scalar repeated many times sends
//! most points of a window to one bucket and serialises that thread. While
//! the device runs, the stock CPU MSM computes a share of the points whose
//! size depends only on `n` and the path.
//!
//! Every base the device uses must be in G1: the signed digits and the mask
//! give `sum s_i P_i` only when `q P_i = O`. The stock CPU MSM needs no such
//! check. A table is checked once at registration; the one-shot path checks
//! every base at every call.
//!
//! Host values derived from the scalars live in [`secret::Secret`] guards, and
//! threads that ran `blst` arithmetic on them scrub their stack
//! ([`secret::scrub_stack`]).
//!
//! Lock order: the registry, then the device (`ctx::lock`), then a table's
//! points or mask cache.
//!
//! Departures from sppark: grid-wide barriers become dispatch boundaries (the
//! sort is four kernels); warp shuffles become SIMD-group functions, and every
//! pipeline's SIMD width is checked to be 32; each bucket is one grid thread
//! instead of persistent warps; the window plan is a measured table; a chunk is
//! capped so a command buffer stays near 0.5 s; the mask is added on the
//! device in `msm_digits`.
use std::sync::Arc;

use blst::{blst_p1, blst_p1_affine};

use crate::{
    G1AffineLimbs, G1JacobianLimbs, Scalar,
    account::{self, Class, Reason},
    ctx::{self, Error},
};

/// Records into the [`msm_g1_stages`] report; empty outside `test-support`.
macro_rules! trace {
    ($trace:expr, |$st:ident| $body:expr) => {
        if let Some($st) = $trace.as_deref_mut() {
            #[cfg(any(test, feature = "test-support"))]
            $body;
            #[cfg(not(any(test, feature = "test-support")))]
            match *$st {}
        }
    };
}

mod checks;
mod collect;
mod effective;
mod par;
mod pipeline;
mod plan;
mod registry;
mod secret;
mod split;

pub(crate) use effective::{effective_need, effective_size_reaches};
#[cfg(any(test, feature = "test-support"))]
pub use registry::one_shot_g1_checks;
use registry::{ONE_SHOT, Store, TABLES_SERVED, Table};
pub use registry::{SrsHandle, msm_counts, register_srs, srs_handles, srs_stale};
use secret::{Secret, scrub_stack};
use split::{Points, split};

/// A device XYZZ record (`g1::Xyzz`): `X, Y, ZZZ, ZZ`, six limbs each.
type Xyzz = [u64; 24];

// The host types the code reinterprets.
const _: () = {
    use std::mem::{align_of, size_of};
    assert!(size_of::<midnight_curves::Fq>() == size_of::<Scalar>());
    assert!(align_of::<midnight_curves::Fq>() == align_of::<Scalar>());
    assert!(size_of::<midnight_curves::G1Affine>() == size_of::<G1AffineLimbs>());
    assert!(align_of::<midnight_curves::G1Affine>() == align_of::<G1AffineLimbs>());
    assert!(size_of::<blst_p1_affine>() == size_of::<G1AffineLimbs>());
    assert!(align_of::<blst_p1_affine>() <= align_of::<G1AffineLimbs>());
    assert!(size_of::<midnight_curves::G1Projective>() == size_of::<blst_p1>());
};

/// The decline reason of a base outside G1.
pub(crate) const BASES_REASON: Reason = Reason::BasesNotInSubgroup;

// ---------------------------------------------------------------------------
// Admission.

/// A registered table that serves an MSM ([`lookup`]).
pub(crate) struct Pinned(Arc<Table>);

/// What [`lookup`] found for an MSM's bases.
pub(crate) enum Lookup {
    /// A registered table serves them.
    Table(Pinned),
    /// A registered table holds them, but a point of the prefix is not in G1.
    NotInG1,
    /// No registered table serves them (none was registered, or it was stale).
    Unregistered,
}

/// The table that serves an MSM of `n` scalars on `bases`: lookup by address
/// and length, comparison of every point (a mismatch, or a panic in the
/// comparison, drops the table), then the table's G1 check. Reads no scalar.
pub(crate) fn lookup(bases: &[G1AffineLimbs], n: usize) -> Lookup {
    match registry::serving_table(bases, n) {
        Some(t) if n > t.first_bad => Lookup::NotInG1,
        Some(t) => Lookup::Table(Pinned(t)),
        None => Lookup::Unregistered,
    }
}

// ---------------------------------------------------------------------------
// Dispatch.

/// `sum scalars[i] * bases[i]` on the pinned `table`, or on the one-shot path
/// without one. Never panics (a panic below is a `panic` decline) and scrubs
/// the calling thread's stack before returning.
pub(crate) fn msm_g1(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    table: Option<Pinned>,
) -> Option<G1JacobianLimbs> {
    if scalars.is_empty() || scalars.len() != bases.len() {
        account::decline(Class::Msm, Reason::Shape);
        return None;
    }
    let ran = par::catch(|| dispatch(scalars, bases, table.map(|p| p.0), None));
    scrub_stack();
    match ran {
        Some(Ok((r, ns))) => {
            account::served(Class::Msm, ns);
            // the result leaves; the guard `r` zeroes its own copy
            Some(*r)
        }
        Some(Err(Fail::Bases)) => {
            account::decline(Class::Msm, BASES_REASON);
            None
        }
        Some(Err(Fail::Ctx(e))) => {
            account::decline(Class::Msm, Reason::of(&e));
            None
        }
        None => {
            account::decline(Class::Msm, Reason::Panic);
            None
        }
    }
}

/// Why [`dispatch`] did not serve a call.
enum Fail {
    /// A base the device would use is not a point of G1.
    Bases,
    /// The device context failed.
    Ctx(Error),
}

impl From<Error> for Fail {
    fn from(e: Error) -> Fail {
        Fail::Ctx(e)
    }
}

/// The result of a served MSM (a guard) and its GPU time in nanoseconds.
type Served = (Secret<G1JacobianLimbs>, u64);

/// The table path on the pinned `table`, or the one-shot path without one.
fn dispatch(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    table: Option<Arc<Table>>,
    trace: Trace<'_>,
) -> Result<Served, Fail> {
    match table {
        Some(t) => table_path(scalars, bases, t, trace),
        None => one_shot_path(scalars, bases, trace),
    }
}

/// The MSM on the pinned table `t`; the first MSM on a table uploads it.
fn table_path(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    t: Arc<Table>,
    mut trace: Trace<'_>,
) -> Result<Served, Fail> {
    debug_assert!(scalars.len() <= t.first_bad);
    let mut s = ctx::lock()?;
    t.upload(s.ctx())?;
    TABLES_SERVED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    trace!(trace, |st| st.table = true);
    let store = par::read(&t.store);
    let Store::Device(points) = &*store else {
        return Err(Error::Device("msm: the table was not uploaded".into()).into());
    };
    let r = split(
        &mut s,
        Points::Table(points),
        scalars,
        bases,
        Some(&t.masks),
        trace,
    )?;
    drop(store);
    // end the session before the table may be freed (this may be the last
    // reference if its handle was dropped meanwhile)
    drop(s);
    drop(t);
    Ok(r)
}

/// The MSM on the caller's points after the G1 check of every base.
fn one_shot_path(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    trace: Trace<'_>,
) -> Result<Served, Fail> {
    #[cfg(any(test, feature = "test-support"))]
    registry::G1_CHECKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if !checks::all_in_g1(bases) {
        return Err(Fail::Bases);
    }
    ONE_SHOT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut s = ctx::lock()?;
    Ok(split(
        &mut s,
        Points::Host(bases),
        scalars,
        bases,
        None,
        trace,
    )?)
}

// ---------------------------------------------------------------------------
// The test entry.

/// Where [`msm_g1_stages`] collects its report.
#[cfg(any(test, feature = "test-support"))]
type Trace<'a> = Option<&'a mut MsmStages>;
/// Always `None`: only the test entry reports.
#[cfg(not(any(test, feature = "test-support")))]
type Trace<'a> = Option<&'a mut std::convert::Infallible>;

/// The path and the plan of one MSM ([`msm_g1_stages`]): public facts only.
#[cfg(any(test, feature = "test-support"))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MsmStages {
    /// Window bits of the device share.
    pub wbits: u32,
    /// Chunks (command buffers) of each device MSM pass.
    pub batches: u32,
    /// Device passes: 2, or 1 when the table had `MSM(r)` cached.
    pub passes: u32,
    /// Whether a registered table served the call.
    pub table: bool,
    /// Points of the device share (`n` when the CPU takes no share).
    pub device_points: u64,
}

/// [`crate::msm_g1`] without the thresholds, reporting the path and plan. Not
/// counted in [`crate::stats`] or [`crate::declines`]; not a stable interface.
#[doc(hidden)]
#[cfg(any(test, feature = "test-support"))]
pub fn msm_g1_stages(
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
) -> Option<(G1JacobianLimbs, MsmStages)> {
    if scalars.is_empty() || scalars.len() != bases.len() || scalars.len() > 1 << crate::MAX_MSM_LOG
    {
        return None;
    }
    if !crate::device() || !crate::field::all_reduced(scalars) {
        return None;
    }
    let mut st = MsmStages::default();
    let ran = par::catch(|| {
        let table = match lookup(bases, scalars.len()) {
            Lookup::Table(p) => Some(p.0),
            Lookup::NotInG1 => return Err(Fail::Bases),
            Lookup::Unregistered => None,
        };
        dispatch(scalars, bases, table, Some(&mut st))
    });
    scrub_stack();
    let (r, _) = ran?.ok()?;
    Some((*r, st))
}

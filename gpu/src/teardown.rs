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

//! Explicit teardown of device state, and the retirement of the device
//! after a device call whose error path could not confirm that its
//! stream drained.
//!
//! A copy that may still read or write the caller's host memory must be
//! ended, so the failed-drain path resets the CUDA context and retires
//! the device for the rest of the process: [`device_disabled`] and
//! [`erasure_failed`] are sticky, every later device call of this crate
//! declines (see [`declined_after_teardown`]), and the process is never
//! exited or aborted from here. A caller that runs as a daemon checks
//! the state and exits itself.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};

#[cfg(midnight_gpu_cuda)]
unsafe extern "C" {
    /// 0: the NTT tables were freed (or none was built); -1: a table was
    /// kept for a later call.
    fn mgpu_ntt_teardown() -> i32;
    /// 0 only when the context reset succeeded; -1 otherwise.
    fn mgpu_teardown_context() -> i32;
}

/// Whether the one context teardown ran and left no context: a
/// successful reset, or no context to reset. Once it holds, every
/// transfer of the dead context has ended.
pub(crate) fn context_reset_done() -> bool {
    RESET_OK.get().copied().unwrap_or(false)
}

static DISABLED: AtomicBool = AtomicBool::new(false);
static ERASURE_FAILED: AtomicBool = AtomicBool::new(false);
static RESET_OK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
static DECLINED: AtomicU64 = AtomicU64::new(0);

/// Whether the device is retired for the rest of this process: set by
/// the first context teardown and never cleared. While it is set, every
/// device call of this crate declines as it does with no device.
pub fn device_disabled() -> bool {
    DISABLED.load(Relaxed)
}

/// Whether an unconfirmed drain forced a context teardown, or a context
/// teardown destroyed device buffers that were not individually erased.
/// Sticky: set once, never cleared.
pub fn erasure_failed() -> bool {
    ERASURE_FAILED.load(Relaxed)
}

/// Device calls declined because the device is retired (each is also in
/// [`crate::declines`] under the reason `teardown`).
pub fn declined_after_teardown() -> u64 {
    DECLINED.load(Relaxed)
}

/// Counts one call declined for the retired state and returns `false`
/// (the decline), like [`crate::decline`].
pub(crate) fn note_decline(class: &'static str) -> bool {
    DECLINED.fetch_add(1, Relaxed);
    crate::decline(class, "teardown")
}

/// Frees the NTT twiddle tables now, on the device-owner actor,
/// while the CUDA runtime is alive. `true`: freed, none was built,
/// there is no context, the device is already retired (the tables
/// went with its context), or this is a stub build. `false`: a
/// table was kept; a later call retries it. The next transform
/// after a successful teardown builds the tables again.
/// Returns false while a batch session is active.
pub fn teardown_ntt_tables() -> bool {
    let Some(_gate) = crate::batch::admit_ordinary("teardown") else {
        return false;
    };
    #[cfg(midnight_gpu_cuda)]
    {
        if device_disabled() || !crate::ffi::context_ready() {
            return true;
        }
        crate::ffi::call(|| {
            if device_disabled() {
                return true;
            }
            // SAFETY: no argument; on the actor thread, so no
            // transform runs during the teardown.
            let rc = unsafe { mgpu_ntt_teardown() };
            rc == 0
        })
        .unwrap_or_else(|| device_disabled() || crate::ffi::tearing_down())
    }
    #[cfg(not(midnight_gpu_cuda))]
    true
}

/// Whether a context reset must be attempted: a device is present and
/// its context is (or may be) made. The failed-drain caller comes from
/// a device call, so the probe behind [`crate::present`] has already
/// run when this is called on the actor thread.
fn needs_reset() -> bool {
    #[cfg(midnight_gpu_cuda)]
    {
        match crate::context_active() {
            Some(true) => true,
            Some(false) => false,
            None => crate::present().is_some(),
        }
    }
    #[cfg(not(midnight_gpu_cuda))]
    false
}

/// The one context teardown of this process (on the actor thread in
/// a CUDA build): sets [`device_disabled`] whether or
/// not the reset succeeds, sets [`erasure_failed`] when a reset is
/// attempted (the buffers that were alive are not erased one by one),
/// and resets the context at most once. Returns whether the device is
/// retired with no context left: a successful reset, or no context to
/// reset. Later calls return the first call's result.
fn retire_locked() -> bool {
    *RESET_OK.get_or_init(|| {
        let reset = needs_reset();
        DISABLED.store(true, Relaxed);
        if !reset {
            return true;
        }
        ERASURE_FAILED.store(true, Relaxed);
        #[cfg(midnight_gpu_cuda)]
        {
            // Before the reset takes them away, attempt the zeroing of this
            // crate's quarantined regions without freeing them (the core
            // does the same with its own quarantine inside
            // `mgpu_teardown_context`). After a successful reset the ones
            // that could not be zeroed are counted as lost unerased and the
            // list is cleared without a CUDA call; when the reset fails
            // nothing is counted or cleared.
            crate::wipe::reset_quarantine(|| {
                // SAFETY: the core wipes its pinned buffers before the reset unmaps them.
                unsafe { mgpu_teardown_context() == 0 }
            })
        }
        #[cfg(not(midnight_gpu_cuda))]
        false
    })
}

/// The single entry point of a failed-drain path: the stream of a device
/// call could not be confirmed drained, so a copy may still touch the
/// caller's host memory. Runs on the actor thread (the actor loop's
/// drain check calls it after the operation that drained).
///
/// Sets [`erasure_failed`] and [`device_disabled`] (both sticky),
/// whether or not the context reset succeeds, and resets the CUDA
/// context exactly once, which ends every transfer. Later calls change
/// nothing; later device calls only decline and are counted. The
/// process is never exited or aborted.
pub(crate) fn on_unconfirmed_drain() {
    ERASURE_FAILED.store(true, Relaxed);
    let _ = retire_locked();
}

/// The unconfirmed-drain count this module last accounted for.
static DRAINS_SEEN: AtomicU64 = AtomicU64::new(0);

/// Test only: whether the drain check of the device guard retires the
/// device (on by default).
#[cfg(feature = "test-fault")]
static DRAIN_CHECK: AtomicBool = AtomicBool::new(true);

/// Test only (feature `test-fault`): turns the drain check of the device
/// guard off or on, so a test can look at the state between an
/// unconfirmed drain and the context teardown.
#[cfg(feature = "test-fault")]
pub fn set_drain_check_for_test(on: bool) {
    let Some(_gate) = crate::batch::admit_ordinary("mode") else {
        return;
    };
    DRAIN_CHECK.store(on, Relaxed);
}

/// Whether an unconfirmed drain at `now`, last accounted at `seen`,
/// must retire the device: only a growth, and only before the one
/// teardown (its own device calls must not recurse into the check).
fn drain_grew(seen: u64, now: u64, retired: bool) -> bool {
    !retired && now > seen
}

/// Accounts for the core's unconfirmed drains after a device call
/// (the actor loop runs this after every operation): when the count grew
/// since the last check, the failed-drain path retires the device.
/// The counters are host memory only, read here without the probe
/// gate of [`crate::error_drains`], so the check makes no CUDA call
/// and takes no lock itself. The count is recorded before the
/// retirement runs, and a growth seen after the one teardown is
/// recorded without retiring again.
pub(crate) fn check_drains() {
    #[cfg(midnight_gpu_cuda)]
    {
        let mut c = [0u64; 2];
        // SAFETY: writes 2 u64 into `c`; host memory only.
        unsafe { crate::ffi::mgpu_drain_counters(c.as_mut_ptr()) };
        #[cfg(feature = "test-fault")]
        if !DRAIN_CHECK.load(Relaxed) {
            return;
        }
        let now = c[1];
        let seen = DRAINS_SEEN.load(Relaxed);
        DRAINS_SEEN.store(now.max(seen), Relaxed);
        if drain_grew(seen, now, device_disabled()) {
            on_unconfirmed_drain();
        }
    }
}

/// Retires the device for the rest of this process, for a caller that
/// wants to tear the context down itself: the same exactly-once context
/// reset as the failed-drain path, as an actor teardown operation.
/// `true`: the reset succeeded, or there was no context to reset (a
/// stub build, no device, or no device call yet). Sets
/// [`device_disabled`]; when a reset is attempted it also sets
/// [`erasure_failed`], because the device buffers alive at the reset
/// are not erased one by one.
/// Returns false while a batch session is active.
pub fn teardown_context() -> bool {
    let Some(_gate) = crate::batch::admit_ordinary("teardown") else {
        return false;
    };
    #[cfg(midnight_gpu_cuda)]
    {
        crate::ffi::call_teardown(retire_locked).unwrap_or(false)
    }
    #[cfg(not(midnight_gpu_cuda))]
    retire_locked()
}

/// Test only (feature `test-fault`): runs the failed-drain retirement
/// as an actor teardown operation, as the error path of a device
/// call would.
#[cfg(feature = "test-fault")]
pub fn trigger_unconfirmed_drain_for_test() {
    let Some(_gate) = crate::batch::admit_ordinary("teardown") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    {
        crate::ffi::call_teardown(on_unconfirmed_drain);
    }
    #[cfg(not(midnight_gpu_cuda))]
    on_unconfirmed_drain();
}

/// Test only (feature `test-fault`): occupies the actor for `hold`
/// with a device operation, then (still inside that operation)
/// requests the teardown state, so a test can have another call
/// queue a request to the actor across the context reset. The
/// retirement itself runs at the end of the occupying operation,
/// through the actor loop's drain path: here it is run directly on
/// the actor thread before the operation replies.
#[cfg(feature = "test-fault")]
pub fn retire_after_holding_lock_for_test(hold: std::time::Duration) {
    let Some(_gate) = crate::batch::admit_ordinary("teardown") else {
        return;
    };
    #[cfg(midnight_gpu_cuda)]
    {
        let _ = crate::present();
        let ran = crate::ffi::call(move || {
            std::thread::sleep(hold);
            on_unconfirmed_drain();
        });
        if ran.is_none() {
            std::thread::sleep(hold);
            crate::ffi::call_teardown(on_unconfirmed_drain);
        }
    }
    #[cfg(not(midnight_gpu_cuda))]
    {
        std::thread::sleep(hold);
        on_unconfirmed_drain();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The drain check retires the device exactly on a growth of the
    /// unconfirmed count, and never again after the one teardown:
    /// an unchanged count (a confirmed drain, or no drain) keeps the
    /// device, and the teardown's own calls cannot recurse into it.
    #[test]
    fn drain_check_fires_only_on_growth_before_retirement() {
        assert!(!drain_grew(0, 0, false), "no unconfirmed drain yet");
        assert!(!drain_grew(3, 3, false), "no growth since the last check");
        assert!(drain_grew(0, 1, false), "the first unconfirmed drain");
        assert!(drain_grew(3, 5, false), "a later growth");
        assert!(
            !drain_grew(3, 5, true),
            "after the one teardown a growth is only recorded"
        );
        assert!(!drain_grew(5, 3, false), "the sticky count never shrinks");
    }
}

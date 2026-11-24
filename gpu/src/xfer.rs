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

//! Host-device copy counters and the staging statistics of the CUDA core.
//!
//! Copies of 16 MiB or more between pageable host memory and a discrete
//! device go through a page-locked bounce ring of the CUDA core
//! (`MIDNIGHT_GPU_STAGE=off` turns it off; `MIDNIGHT_GPU_STAGE_THREADS`,
//! default up to 8, sets the host copy threads). The ring is not used on an
//! integrated device (one memory).

use std::sync::{
    Mutex,
    atomic::{AtomicBool, AtomicU64, Ordering::Relaxed},
};

static H2D: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];
static D2H: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];

#[allow(dead_code)]
pub(crate) fn note_h2d(bytes: usize) {
    H2D[0].fetch_add(1, Relaxed);
    H2D[1].fetch_add(bytes as u64, Relaxed);
}

static RECORD: AtomicBool = AtomicBool::new(false);
static D2H_LOG: Mutex<Vec<usize>> = Mutex::new(Vec::new());

#[allow(dead_code)]
pub(crate) fn note_d2h(bytes: usize) {
    D2H[0].fetch_add(1, Relaxed);
    D2H[1].fetch_add(bytes as u64, Relaxed);
    if RECORD.load(Relaxed) {
        D2H_LOG.lock().unwrap_or_else(|e| e.into_inner()).push(bytes);
    }
}

/// Starts (or stops) recording the size of every device-to-host copy of
/// a result of this crate (transform outputs, the quotient coefficients).
/// sppark's MSM copies its bucket rows to the host inside each MSM; they are
/// counted apart ([`CopyStats::msm_d2h_copies`]) and zeroed after use (a
/// local sppark patch). Zero checks run on the device and copy back only a
/// count.
pub fn record_d2h(on: bool) {
    let Some(_gate) = crate::batch::admit_ordinary("mode") else {
        return;
    };
    RECORD.store(on, Relaxed);
}

/// The sizes in bytes of the recorded device-to-host copies since the last
/// call, in order.
pub fn take_d2h_log() -> Vec<usize> {
    std::mem::take(&mut *D2H_LOG.lock().unwrap_or_else(|e| e.into_inner()))
}

/// Resets the copy counters.
pub fn reset() {
    for c in H2D.iter().chain(D2H.iter()) {
        c.store(0, Relaxed);
    }
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: counters only.
    unsafe {
        crate::ffi::mgpu_lib_dtoh_reset()
    };
    take_d2h_log();
}

/// Copies and bytes since process start.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CopyStats {
    /// Host-to-device copies.
    pub h2d_copies: u64,
    /// Their bytes.
    pub h2d_bytes: u64,
    /// Device-to-host copies.
    pub d2h_copies: u64,
    /// Their bytes.
    pub d2h_bytes: u64,
    /// Device-to-host copies of bucket rows inside sppark's MSM (two per MSM
    /// batch; zeroed after use).
    pub msm_d2h_copies: u64,
    /// Their bytes.
    pub msm_d2h_bytes: u64,
    /// Staged copies, staged bytes, large direct copies, their bytes, failed
    /// bounce allocations, bounce allocations, bus-bound requests, bounce
    /// bytes held now.
    pub stage: [u64; 8],
}

/// The counters.
pub fn stats() -> CopyStats {
    #[allow(unused_mut)]
    let (mut stage, mut lib) = ([0u64; 8], [0u64; 2]);
    #[cfg(midnight_gpu_cuda)]
    // SAFETY: out arrays of the sizes the core writes.
    unsafe {
        crate::ffi::mgpu_stage_counters(stage.as_mut_ptr());
        crate::ffi::mgpu_lib_dtoh(lib.as_mut_ptr());
    };
    CopyStats {
        h2d_copies: H2D[0].load(Relaxed),
        h2d_bytes: H2D[1].load(Relaxed),
        d2h_copies: D2H[0].load(Relaxed),
        d2h_bytes: D2H[1].load(Relaxed),
        msm_d2h_copies: lib[0],
        msm_d2h_bytes: lib[1],
        stage,
    }
}

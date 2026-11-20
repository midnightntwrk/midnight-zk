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

//! Decline and service accounting. A kernel module ends every call with
//! exactly one of [`served`] or [`decline`].

use std::{
    collections::BTreeMap,
    sync::{
        Mutex,
        atomic::{AtomicU64, Ordering::Relaxed},
    },
};

/// A hook class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Class {
    /// [`crate::msm_g1`].
    Msm,
    /// [`crate::fft`].
    Fft,
    /// [`crate::ifft`].
    Ifft,
    /// [`crate::quotient`].
    Quotient,
}

impl Class {
    /// The class's name in [`crate::declines`] and the reports.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Class::Msm => "msm",
            Class::Fft => "fft",
            Class::Ifft => "ifft",
            Class::Quotient => "quotient",
        }
    }
    /// The index of the class in the service counters.
    const fn index(self) -> usize {
        self as usize
    }
}

/// A decline reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Reason {
    /// Stub build, no usable device, or `MIDNIGHT_METAL=off`.
    NoDevice,
    /// The size is below the class's threshold (`crate::thresholds`).
    BelowMinK,
    /// A length, root, job layout or version the device does not take.
    Shape,
    /// A scalar not below the modulus.
    Unreduced,
    /// A buffer above `maxBufferLength`, a failed allocation, or a budget.
    Memory,
    /// A pipeline, encoder or command buffer failed.
    DeviceError,
    /// The backend panicked; the hook entry caught it (`crate::guarded`).
    Panic,
    /// An MSM base outside G1.
    BasesNotInSubgroup,
    /// An MSM whose bases no registered table serves, with the one-shot path
    /// off.
    UnregisteredBases,
}

impl Reason {
    /// The reason's name in [`crate::declines`].
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Reason::NoDevice => "no-device",
            Reason::BelowMinK => "below-min-k",
            Reason::Shape => "shape",
            Reason::Unreduced => "unreduced",
            Reason::Memory => "memory",
            Reason::DeviceError => "device-error",
            Reason::Panic => "panic",
            Reason::BasesNotInSubgroup => "bases-not-in-subgroup",
            Reason::UnregisteredBases => "unregistered-bases",
        }
    }

    /// The decline reason of a device-context error.
    #[cfg(target_os = "macos")]
    pub(crate) fn of(e: &crate::ctx::Error) -> Self {
        match e {
            crate::ctx::Error::NoDevice(_) => Reason::NoDevice,
            crate::ctx::Error::Memory(_) => Reason::Memory,
            crate::ctx::Error::Device(_) => Reason::DeviceError,
            crate::ctx::Error::Unreduced(_) => Reason::Unreduced,
        }
    }
}

/// Declines by `(class, reason)`.
static DECLINES: Mutex<BTreeMap<(&'static str, &'static str), u64>> = Mutex::new(BTreeMap::new());
/// Calls served, and their GPU nanoseconds, by [`Class::index`].
static SERVED: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
static NANOS: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];

/// Counts a decline; returns `false` (the decline value of a `bool` hook).
pub(crate) fn decline(class: Class, reason: Reason) -> bool {
    *DECLINES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .entry((class.name(), reason.name()))
        .or_insert(0) += 1;
    false
}

/// Counts a call served by the device, with its GPU time.
pub(crate) fn served(class: Class, device_nanos: u64) {
    SERVED[class.index()].fetch_add(1, Relaxed);
    NANOS[class.index()].fetch_add(device_nanos, Relaxed);
}

/// Every decline: `(class, reason, count)`.
pub(crate) fn declines() -> Vec<(&'static str, &'static str, u64)> {
    DECLINES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .iter()
        .map(|(k, v)| (k.0, k.1, *v))
        .collect()
}

/// The service counters of `class`.
pub(crate) fn class_stats(class: Class) -> crate::ClassStats {
    crate::ClassStats {
        served: SERVED[class.index()].load(Relaxed),
        device_nanos: NANOS[class.index()].load(Relaxed),
    }
}

/// Clears every counter.
pub(crate) fn reset() {
    for c in SERVED.iter().chain(NANOS.iter()) {
        c.store(0, Relaxed);
    }
    DECLINES.lock().unwrap_or_else(|e| e.into_inner()).clear();
}

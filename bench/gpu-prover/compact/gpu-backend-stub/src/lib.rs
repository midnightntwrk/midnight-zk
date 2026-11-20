// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The GPU backend interface of compact-bench, and a stub that installs nothing.
//!
//! A real backend has the same crate name and these items. It registers its
//! accelerator functions in the hooked midnight-proofs 0.8.3 (`install_hooks`) and
//! counts how often each hook ran on the device and how often it fell back to the
//! CPU.

/// Hook calls since the last [`reset_counters`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counters {
    /// Multi-scalar multiplications run on the device.
    pub msm: u64,
    /// Forward and inverse NTTs run on the device.
    pub ntt: u64,
    /// Coefficient to extended-coset transforms run on the device.
    pub coset: u64,
    /// Quotient polynomials computed on the device.
    pub quotient: u64,
    /// Hook calls that declined after they started and left the work to the CPU.
    pub fallbacks: u64,
    /// Peak device memory this process held, in bytes, since the last reset.
    pub device_peak_bytes: u64,
}

/// Installs the hooks. Returns a description of the device when the hooks are
/// installed and a device is present, `None` otherwise. The stub returns `None`.
pub fn install_hooks() -> Option<String> {
    None
}

/// The counters since the last reset. The stub returns zeros.
pub fn counters() -> Counters {
    Counters::default()
}

/// Sets the counters to zero.
pub fn reset_counters() {}

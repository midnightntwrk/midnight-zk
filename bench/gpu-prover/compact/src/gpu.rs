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

//! The GPU backend, when the `gpu` feature is on. Without it nothing is
//! installed and every counter reads zero.

/// Hook calls of one proof.
#[derive(Clone, Copy, Debug, Default)]
pub struct Hits {
    pub msm: u64,
    pub ntt: u64,
    pub coset: u64,
    pub quotient: u64,
    pub fallbacks: u64,
    pub device_peak_bytes: u64,
}

/// Installs the backend's hooks. Returns the device description when hooks are
/// installed on a device.
pub fn install() -> Option<String> {
    #[cfg(feature = "gpu")]
    return compact_bench_gpu::install_hooks();
    #[cfg(not(feature = "gpu"))]
    None
}

/// Sets the hook counters to zero.
pub fn reset() {
    #[cfg(feature = "gpu")]
    compact_bench_gpu::reset_counters();
}

/// The hook counters since the last [`reset`].
pub fn hits() -> Hits {
    #[cfg(feature = "gpu")]
    {
        let c = compact_bench_gpu::counters();
        Hits {
            msm: c.msm,
            ntt: c.ntt,
            coset: c.coset,
            quotient: c.quotient,
            fallbacks: c.fallbacks,
            device_peak_bytes: c.device_peak_bytes,
        }
    }
    #[cfg(not(feature = "gpu"))]
    Hits::default()
}

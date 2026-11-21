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

//! The device memory one proof needs, computed from the loaded key.
//!
//! The counts come from [`Shape`], which the device layer derives from the
//! proving key. Every buffer is in exactly one term. The resident
//! proving-key copies and the MSM base tables are added only for the part that
//! is not on the device yet, so a resident buffer is counted once.

use serde::Serialize;

use crate::device::{Held, Phases, Shape};

/// Bytes of one field element.
const FIELD: u64 = 32;
/// Bytes of one affine G1 point on the device.
const AFFINE: u64 = 96;
/// Bytes of one projective bucket of the device MSM.
const BUCKET: u64 = 192;

/// Window width and count of the device MSM for `n` points (the choice of
/// the sppark MSM context): the per-call digits buffer holds one 32-bit digit
/// per window and scalar.
fn msm_window(n: u64) -> (u64, u64) {
    let lg = 63 - (n + n / 2).max(1).leading_zeros() as u64;
    let wbits = if n > 192 {
        lg.saturating_sub(8).clamp(10, 18)
    } else {
        10
    };
    (wbits, 254 / wbits + 1)
}

/// Upper bound of the bucket region of one MSM context for `n` points: two
/// times the bucket count of every window.
fn msm_buckets(n: u64) -> u64 {
    let (wbits, windows) = msm_window(n);
    2 * windows * (1u64 << (wbits - 1)) * BUCKET
}

/// Device bytes of one proof, by term.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct DeviceNeed {
    /// The per-proof extended cosets.
    pub cosets: u64,
    /// The numerator output and the kernel's scratch slots.
    pub quotient: u64,
    /// The transform scratch: one extended polynomial.
    pub scratch: u64,
    /// The per-call MSM buffer (scalars and digits of one MSM of 2^k terms).
    pub msm_call: u64,
    /// The resident proving-key copies, all of them.
    pub resident: u64,
    /// The two MSM base tables (`g[..n]` and `g_lagrange[..n]`), points and
    /// bucket region.
    pub tables: u64,
    /// Reserve on top of the sum.
    pub margin: u64,
    /// Points of one MSM base table (2^k).
    pub table_len: u64,
}

impl DeviceNeed {
    /// The need of `s` with `margin` bytes of reserve.
    pub fn of(s: &Shape, margin: u64) -> DeviceNeed {
        let ext = FIELD << s.ext_k;
        let n = 1u64 << s.k;
        let resident = s.resident_polys as u64 * ext;
        // the job's own memory check, when known: it covers the proof's
        // cosets, the key cosets, the numerator and the scratch slots
        let (cosets, quotient, scratch) = if s.quotient_bytes > 0 {
            (0, s.quotient_bytes.saturating_sub(resident), 0)
        } else {
            (
                s.proof_cosets as u64 * ext,
                ext + (s.nslots.max(1) as u64) * s.grid_threads * FIELD,
                ext,
            )
        };
        DeviceNeed {
            cosets,
            quotient,
            scratch,
            msm_call: n * (FIELD + 4 * msm_window(n).1),
            resident: s.resident_polys as u64 * ext,
            tables: 2 * (n * AFFINE + msm_buckets(n)),
            margin,
            table_len: n,
        }
    }

    /// The need of the phases without the device quotient, for a key whose
    /// quotient the device does not take: MSMs and base-domain NTTs.
    pub fn without_quotient(k: u32, ext_k: u32, margin: u64) -> DeviceNeed {
        let mut d = DeviceNeed::of(
            &Shape {
                k,
                ext_k,
                ..Shape::default()
            },
            margin,
        );
        d.quotient = 0;
        d
    }

    /// What every phase allocates during one proof, beside what stays
    /// resident.
    pub fn proof(&self) -> u64 {
        self.cosets + self.quotient + self.scratch + self.msm_call
    }

    /// Point bytes of one of the two MSM base tables.
    pub fn table_points(&self) -> u64 {
        if self.tables == 0 {
            0
        } else {
            self.table_len * AFFINE
        }
    }

    /// Table bytes still to come for `tables_held` point bytes on the
    /// device. Each table context counts by itself: one table held leaves the
    /// other in the need.
    fn tables_missing(&self, tables_held: u64) -> u64 {
        let per = self.table_points();
        if per == 0 {
            return self.tables;
        }
        let present = (tables_held / per).min(2);
        (2 - present) * (self.tables / 2)
    }

    /// Free device memory a proof with every phase on the device needs now.
    pub fn full(&self, held: Held) -> u64 {
        self.proof()
            + self.resident.saturating_sub(held.resident)
            + self.tables_missing(held.tables)
            + self.margin
    }

    /// The same for the reduced set (MSMs and base-domain NTTs on the
    /// device, the quotient on the CPU): no extended coset and no
    /// proving-key copy is on the device.
    pub fn reduced(&self, held: Held) -> u64 {
        self.scratch + self.msm_call + self.tables_missing(held.tables) + self.margin
    }

    /// Free device memory the phases of `phases` need now.
    pub fn of_phases(&self, phases: Phases, held: Held) -> u64 {
        if phases.contains(Phases::QUOTIENT) {
            self.full(held)
        } else if !phases.is_empty() {
            self.reduced(held)
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MARGIN: u64 = 768 << 20;

    /// A shape at k = 21 with 30 resident copies and 17 per-proof cosets.
    fn shape() -> Shape {
        Shape {
            k: 21,
            ext_k: 23,
            proof_cosets: 17,
            resident_polys: 30,
            nslots: 90,
            grid_threads: 80 * 1024,
            quotient_bytes: 0,
        }
    }

    fn held(resident: u64, tables: u64) -> Held {
        Held { resident, tables }
    }

    #[test]
    fn need_counts_resident_once() {
        let d = DeviceNeed::of(&shape(), MARGIN);
        let mib = |b: u64| b >> 20;
        assert_eq!(mib(d.cosets), 17 * 256);
        assert_eq!(mib(d.resident), 30 * 256);
        let cold = d.full(held(0, 0));
        let both = 2 * d.table_points();
        assert_eq!(both, 2 * (AFFINE << 21));
        let warm = d.full(held(d.resident, both));
        assert_eq!(cold - warm, d.resident + d.tables);
        assert_eq!(warm, d.proof() + MARGIN);
        assert_eq!(d.full(held(d.resident / 2, both)) - warm, d.resident / 2);
        // a stale count above what the key has never lowers the need below
        // the proof
        assert_eq!(d.full(held(u64::MAX, u64::MAX)), warm);
        assert!(d.reduced(held(0, both)) < d.cosets);
        assert_eq!(d.reduced(held(0, 0)) - d.reduced(held(0, both)), d.tables);
    }

    #[test]
    fn tables_missing_counts_each_context() {
        let d = DeviceNeed::of(&shape(), MARGIN);
        let per = d.table_points();
        let one = d.tables / 2;
        assert_eq!(one, per + msm_buckets(1 << 21));
        let r = |t| d.reduced(held(0, t));
        assert_eq!(r(1) - r(2 * per), 2 * one);
        assert_eq!(r(per - 1) - r(2 * per), 2 * one);
        assert_eq!(r(per) - r(2 * per), one);
        assert_eq!(r(u64::MAX), r(2 * per));
    }

    #[test]
    fn msm_window_follows_the_device_msm() {
        assert_eq!(msm_window(1 << 21).1, 20);
        assert_eq!(msm_window(100).1, 26);
        assert_eq!(msm_window(1 << 28).1, 15);
        // the bucket bound scales with k and stays near 32 MiB at k = 21
        assert_eq!(msm_buckets(1 << 21) >> 20, 30);
        assert!(msm_buckets(1 << 16) < msm_buckets(1 << 21));
    }

    #[test]
    fn need_by_phase_set() {
        let d = DeviceNeed::of(&shape(), MARGIN);
        let h = held(0, 0);
        assert_eq!(d.of_phases(Phases::ALL, h), d.full(h));
        assert_eq!(d.of_phases(Phases::MSM, h), d.reduced(h));
        assert_eq!(d.of_phases(Phases::NONE, h), 0);
        let q = DeviceNeed::without_quotient(21, 23, MARGIN);
        assert_eq!(q.quotient, 0);
        assert_eq!(q.resident, 0);
        assert_eq!(q.reduced(h), d.reduced(h));
    }
}

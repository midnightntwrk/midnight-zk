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

//! The plan of one MSM (window width, chunks) and the device share of the
//! CPU/device split. sppark computes the plan by formula; here both come from
//! tables measured on Apple silicon.

use crate::lg2_nearest;

/// Bits of a scalar (sppark `scalar_t::bit_length()`).
pub(super) const NBITS: u32 = 255;
/// The most window digits of one chunk, so that a command buffer stays near
/// or below 0.5 s of GPU time.
pub(super) const CHUNK_ADDS: usize = 1 << 25;
/// Bytes of the temporary sort buffer one pass may use.
const SORT_TEMP_BYTES: usize = 64 << 20;

/// The window plan of an MSM of `n` points.
#[derive(Clone, Copy, Debug)]
pub(super) struct Plan {
    pub(super) n: usize,
    pub(super) wbits: u32,
    pub(super) nwins: u32,
    /// Chunks (command buffers).
    pub(super) batch: usize,
    /// Points per chunk (a multiple of 32).
    pub(super) stride: usize,
    /// `wbits - 1`: bucket index bits.
    pub(super) bits: u32,
    /// Bits of the upper sort (`bits / 2`).
    pub(super) top_bits: u32,
    /// Bits of the lower sort (`bits - top_bits`).
    pub(super) low_bits: u32,
    /// Bits of the top window (sppark `top`).
    pub(super) top: u32,
    /// Windows per sort pass.
    pub(super) pass: u32,
}

/// sppark `lg2`: floor of log2, 0 for 0.
pub(super) const fn lg2(mut n: usize) -> u32 {
    let mut r = 0;
    while n > 1 {
        n >>= 1;
        r += 1;
    }
    r
}

/// `(log2 n, wbits, chunks)`, measured on Apple silicon (table path, CPU share
/// off). Sizes outside the table take the nearest end entry; other lengths
/// take the entry of [`lg2_nearest`], so a split's device share uses its
/// power's entry.
const MEASURED: [(u32, u32, usize); 10] = [
    (13, 11, 1),
    (14, 11, 1),
    (15, 11, 1),
    (16, 13, 1),
    (17, 13, 1),
    (18, 13, 1),
    (19, 13, 1),
    (20, 15, 1),
    (21, 16, 1),
    (22, 16, 1),
];

/// `(wbits, chunks)` of [`MEASURED`] for `n` points.
fn measured(n: usize) -> (u32, usize) {
    let (lo, hi) = (MEASURED[0].0, MEASURED[MEASURED.len() - 1].0);
    let k = lg2_nearest(n).clamp(lo, hi);
    let e = MEASURED[(k - lo) as usize];
    (e.1, e.2)
}

/// The plan of an MSM of `n` points.
pub(super) fn plan(n: usize) -> Plan {
    let (wbits, batch) = measured(n);
    let nwins = (NBITS - 1) / wbits + 1;
    // cap the GPU time of one command buffer (sppark has no such bound)
    let max_stride = (CHUNK_ADDS / nwins as usize) & !31;
    let stride = n.div_ceil(batch).next_multiple_of(32).min(max_stride);
    let batch = n.div_ceil(stride);
    let bits = wbits - 1;
    let top_bits = bits / 2;
    let low_bits = bits - top_bits;
    let pass = (SORT_TEMP_BYTES / (8 * stride)).clamp(2, nwins as usize) as u32;
    Plan {
        n,
        wbits,
        nwins,
        batch,
        stride,
        bits,
        top_bits,
        low_bits,
        top: NBITS - wbits * (nwins - 1),
        pass,
    }
}

/// The denominator of the shares in [`MEASURED_SHARE`].
const SHARE_DEN: usize = 64;

/// The device share by size, `(log2 n, table path, one-shot path)` in 64ths
/// of the points (64: device only), measured on Apple silicon. At `2^13` to
/// `2^15` the table path keeps every point on the device: inside a proof the
/// CPU share keeps all CPU threads busy and the device share slows down over
/// successive proofs. Below the table: device only; above: the last entry.
const MEASURED_SHARE: [(u32, usize, usize); 10] = [
    (13, 64, 40),
    (14, 64, 40),
    (15, 64, 40),
    (16, 64, 48),
    (17, 54, 52),
    (18, 54, 40),
    (19, 54, 40),
    (20, 52, 40),
    (21, 52, 48),
    (22, 52, 44),
];

/// The device share `m` of an MSM of `n` points: the device computes `[0, m)`
/// and the CPU `[m, n)`. A function of `n` and the path only;
/// `MIDNIGHT_METAL_MSM_CPU_SHARE=off` or no CPU pool gives `m = n`.
pub(super) fn device_share(n: usize, table: bool) -> usize {
    if std::env::var("MIDNIGHT_METAL_MSM_CPU_SHARE").as_deref() == Ok("off")
        || super::split::cpu_pool().is_none()
    {
        return n;
    }
    let k = lg2_nearest(n);
    let (lo, hi) = (
        MEASURED_SHARE[0].0,
        MEASURED_SHARE[MEASURED_SHARE.len() - 1].0,
    );
    if k < lo {
        return n;
    }
    // in range: `lo <= k.min(hi) <= hi`, one entry per log2
    let e = MEASURED_SHARE[(k.min(hi) - lo) as usize];
    let frac = if table { e.1 } else { e.2 };
    (n * frac / SHARE_DEN).clamp(1, n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_follows_measured_table() {
        // (log2 n, wbits, nwins, chunks after the command-buffer bound)
        for (k, wbits, nwins, batch) in [
            (13, 11, 24, 1),
            (14, 11, 24, 1),
            (15, 11, 24, 1),
            (16, 13, 20, 1),
            (17, 13, 20, 1),
            (18, 13, 20, 1),
            (19, 13, 20, 1),
            (20, 15, 17, 1),
            (21, 16, 16, 1),
            (22, 16, 16, 2),
        ] {
            let p = plan(1 << k);
            assert_eq!((p.wbits, p.nwins, p.batch), (wbits, nwins, batch), "2^{k}");
            assert_eq!(p.top, NBITS - wbits * (nwins - 1));
            assert!(p.stride * p.batch >= 1 << k, "2^{k}");
        }
        // outside the table: the end entries; a non-power of two: its
        // nearest log2 (a device share of 52/64 of 2^20 takes the 2^20 entry)
        assert_eq!(plan(1).wbits, 11);
        assert_eq!(plan(1000).wbits, 11);
        assert_eq!(plan((1 << 20) * 52 / 64).wbits, 15);
        assert_eq!(plan((1 << 20) * 46 / 64).wbits, 15);
        assert_eq!(plan((1 << 20) * 45 / 64).wbits, 13);
        assert_eq!(plan((1 << 21) - 1).wbits, 16);
        assert_eq!(plan((1 << 21) + 5).wbits, 16);
        // the command-buffer bound up to 2^28
        for k in 0..=crate::MAX_MSM_LOG {
            for n in [1usize << k, (1usize << k) + 33] {
                let p = plan(n);
                assert!(p.stride * p.nwins as usize <= CHUNK_ADDS, "{n}");
                assert!(
                    p.stride * p.batch >= n && p.stride * (p.batch - 1) < n,
                    "{n}"
                );
                assert!(p.stride.is_multiple_of(32), "{n}");
                if k >= 22 {
                    assert_eq!(p.wbits, 16, "{n}");
                }
            }
        }
        assert_eq!(plan(1 << 23).batch, 4);
        assert_eq!(plan(1 << 28).batch, 128);
    }

    #[test]
    fn device_share_follows_measured_table() {
        if std::env::var("MIDNIGHT_METAL_MSM_CPU_SHARE").as_deref() == Ok("off") {
            return;
        }
        for &(k, t, o) in &MEASURED_SHARE {
            let n = 1usize << k;
            assert_eq!(device_share(n, true), n * t / SHARE_DEN, "2^{k}");
            assert_eq!(device_share(n, false), n * o / SHARE_DEN, "2^{k}");
        }
        assert_eq!(device_share(1000, true), 1000);
        assert_eq!(device_share(1 << 12, false), 1 << 12);
        // a length just below a power of two takes that power's share
        assert_eq!(device_share((1 << 20) - 1, true), ((1 << 20) - 1) * 52 / 64);
        assert_eq!(device_share(1 << 24, true), (1 << 24) * 52 / 64);
    }
}

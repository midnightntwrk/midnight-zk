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

//! The effective size of an MSM: its count of non-zero scalars (1 when all
//! are zero). The masked device MSM costs the same however sparse the scalars
//! are, while the stock CPU MSM skips zeros, so a sparse MSM stays on the CPU.
//! Only the admission decline is observable; the count is never stored.

use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use super::par::{host_threads, par_parts};
use crate::Scalar;

/// Default need on the table path: `SPARSE_TABLE_FIXED + n / SPARSE_TABLE_DIV`
/// non-zero scalars. Both parts are measured crossovers against the stock CPU
/// MSM on Apple silicon: `n/5` at large `n`, plus a fixed part for the
/// device's fixed cost near the threshold. A function of the length only.
const SPARSE_TABLE_DIV: usize = 5;
/// See [`SPARSE_TABLE_DIV`].
const SPARSE_TABLE_FIXED: usize = 1 << 12;

/// The non-zero scalars an MSM of `n` scalars needs for the device under the
/// log2 threshold `k` of its path. With the default thresholds the table path
/// needs [`SPARSE_TABLE_DIV`]'s formula; with an explicit threshold either path
/// needs `2^k`. The one-shot path is only reached with an explicit threshold.
pub(crate) fn effective_need(n: usize, k: u32, table: bool, explicit: bool) -> usize {
    if table && !explicit {
        SPARSE_TABLE_FIXED + n / SPARSE_TABLE_DIV
    } else {
        1usize << k.min(40)
    }
}

/// Whether `scalars` has at least `need` non-zero scalars (all zero counts as
/// 1). Scans a prefix first so a dense input decides early, then counts the
/// rest in parallel with early exit.
pub(crate) fn effective_size_reaches(scalars: &[Scalar], need: usize) -> bool {
    const BLOCK: usize = 1 << 13;
    if need <= 1 {
        return true;
    }
    let nz = |s: &Scalar| (s[0] | s[1] | s[2] | s[3] != 0) as usize;
    let head = scalars.len().min(need.saturating_mul(2).max(BLOCK));
    let mut seen = 0usize;
    for b in scalars[..head].chunks(BLOCK) {
        seen += b.iter().map(nz).sum::<usize>();
        if seen >= need {
            return true;
        }
    }
    let rest = &scalars[head..];
    if seen + rest.len() < need {
        return false;
    }
    let total = AtomicUsize::new(seen);
    // a panicked part leaves the count short, so the call declines
    let _ = par_parts(rest.len(), host_threads(), BLOCK, |lo, hi| {
        for b in rest[lo..hi].chunks(BLOCK) {
            if total.load(Relaxed) >= need {
                return;
            }
            total.fetch_add(b.iter().map(nz).sum::<usize>(), Relaxed);
        }
    });
    total.load(Relaxed) >= need
}

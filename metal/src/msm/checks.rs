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

//! Host passes over every point, on several threads: the identity comparison
//! of a table with the caller's slice, and the G1 check.

use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

use blst::{blst_p1_affine, blst_p1_affine_on_curve};

use super::par::{host_threads, par_parts};
use crate::G1AffineLimbs;

/// Points per step between reads of the shared flag.
const POINT_BLOCK: usize = 1 << 12;

/// Whether `a == b`, comparing every point; a panicked part counts as a
/// difference.
pub(super) fn points_equal(a: &[G1AffineLimbs], b: &[G1AffineLimbs]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let differs = AtomicBool::new(false);
    let done = par_parts(a.len(), host_threads(), 1 << 14, |lo, hi| {
        for s in (lo..hi).step_by(POINT_BLOCK) {
            if differs.load(Relaxed) {
                return;
            }
            let e = (s + POINT_BLOCK).min(hi);
            if a[s..e] != b[s..e] {
                differs.store(true, Relaxed);
                return;
            }
        }
    });
    done.is_some() && !differs.load(Relaxed)
}

/// Whether `p` is in G1: all zero (infinity), or on the curve and in the
/// prime-order subgroup.
pub(super) fn in_g1(p: &G1AffineLimbs) -> bool {
    if p.iter().all(|&w| w == 0) {
        return true;
    }
    // SAFETY: `G1AffineLimbs` has the size of `blst_p1_affine` and of the
    // transparent `G1Affine`, and at least their alignments (asserted in the
    // parent module); every bit pattern is a value of both (field limbs).
    let (raw, aff) = unsafe {
        (
            &*(p as *const G1AffineLimbs as *const blst_p1_affine),
            &*(p as *const G1AffineLimbs as *const midnight_curves::G1Affine),
        )
    };
    // SAFETY: `raw` points to an affine point.
    let on_curve = unsafe { blst_p1_affine_on_curve(raw) };
    on_curve && bool::from(aff.is_torsion_free())
}

/// The first index of `bases` not in G1, or `bases.len()`. A panicked part
/// counts from its start.
pub(super) fn first_not_in_g1(bases: &[G1AffineLimbs]) -> usize {
    let n = bases.len();
    let firsts = par_parts(n, host_threads(), POINT_BLOCK, |lo, hi| {
        (lo..hi).find(|&i| !in_g1(&bases[i])).unwrap_or(n)
    });
    firsts.map_or(0, |f| f.into_iter().min().unwrap_or(n))
}

/// Whether every point of `bases` is in G1; a panicked part counts as a
/// failure.
pub(super) fn all_in_g1(bases: &[G1AffineLimbs]) -> bool {
    let bad = AtomicBool::new(false);
    let done = par_parts(bases.len(), host_threads(), POINT_BLOCK, |lo, hi| {
        for s in (lo..hi).step_by(POINT_BLOCK) {
            if bad.load(Relaxed) {
                return;
            }
            let e = (s + POINT_BLOCK).min(hi);
            if !bases[s..e].iter().all(in_g1) {
                bad.store(true, Relaxed);
                return;
            }
        }
    });
    done.is_some() && !bad.load(Relaxed)
}

#[cfg(test)]
mod tests {
    use group::prime::PrimeCurveAffine;

    use super::*;

    #[test]
    fn g1_check_takes_infinity_and_rejects_others() {
        let g = midnight_curves::G1Affine::generator();
        // SAFETY: the layout asserted in the parent module.
        let lim = |p: &midnight_curves::G1Affine| unsafe {
            *(p as *const midnight_curves::G1Affine as *const G1AffineLimbs)
        };
        let inf = [0u64; 12];
        assert!(in_g1(&lim(&g)) && in_g1(&inf));
        // a point off the curve: the generator with its y coordinate changed
        let mut off = lim(&g);
        off[6] ^= 1;
        assert!(!in_g1(&off));
        let pts = vec![lim(&g), inf, off, lim(&g), off];
        assert!(points_equal(&pts, &pts.to_vec()));
        assert!(!points_equal(&pts[..2], &pts[1..3]));
        assert_eq!(first_not_in_g1(&pts), 2);
        assert!(!all_in_g1(&pts));
        assert!(all_in_g1(&pts[..2]));
        assert_eq!(first_not_in_g1(&pts[..2]), 2);
    }
}

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

//! The host collection (sppark `collect`, `integrate_row`, `sum_up`) with
//! blst, and the conversions between the device records and blst points.

use blst::{blst_fp, blst_fp_mul, blst_p1, blst_p1_add_or_double, blst_p1_double};

use super::{
    Xyzz,
    par::{host_threads, par_parts},
    plan::{Plan, lg2},
    secret::{ScrubOnExit, Secret, SecretVec, wipe},
};
use crate::G1JacobianLimbs;

/// `a += b`.
pub(super) fn add(a: &mut blst_p1, b: &blst_p1) {
    let t = *a;
    // SAFETY: valid blst points; the output does not alias the inputs.
    unsafe { blst_p1_add_or_double(a, &t, b) };
}

/// `a = 2 a`.
fn dbl(a: &mut blst_p1) {
    let t = *a;
    // SAFETY: a valid blst point; the output does not alias the input.
    unsafe { blst_p1_double(a, &t) };
}

/// An XYZZ record as Jacobian `(X ZZ, Y ZZZ, ZZ)`; infinity (`ZZ = 0`) stays
/// infinity.
fn p1_of_xyzz(r: &Xyzz) -> blst_p1 {
    let fp = |i: usize| {
        let mut l = [0u64; 6];
        l.copy_from_slice(&r[6 * i..6 * i + 6]);
        blst_fp { l }
    };
    let (x, y, zzz, zz) = (fp(0), fp(1), fp(2), fp(3));
    let mut p = blst_p1 {
        z: zz,
        ..Default::default()
    };
    // SAFETY: valid field elements; outputs do not alias inputs.
    unsafe {
        blst_fp_mul(&mut p.x, &x, &zz);
        blst_fp_mul(&mut p.y, &y, &zzz);
    }
    p
}

/// Jacobian limbs as a blst point.
pub(super) fn p1_of(l: &G1JacobianLimbs) -> blst_p1 {
    let fp = |i: usize| {
        let mut f = [0u64; 6];
        f.copy_from_slice(&l[6 * i..6 * i + 6]);
        blst_fp { l: f }
    };
    blst_p1 {
        x: fp(0),
        y: fp(1),
        z: fp(2),
    }
}

/// A blst point as Jacobian limbs.
pub(super) fn limbs_of(p: &blst_p1) -> G1JacobianLimbs {
    let mut out = [0u64; 18];
    out[..6].copy_from_slice(&p.x.l);
    out[6..12].copy_from_slice(&p.y.l);
    out[12..].copy_from_slice(&p.z.l);
    out
}

/// sppark `integrate_row`: the window sum from the `2^nthrbits` (weighted,
/// plain) run-sum pairs of `msm_integrate` in `row`; `lsbits` is the window
/// width.
fn integrate_row(row: &[Xyzz], lsbits: u32, nthrbits: u32) -> blst_p1 {
    let rec = |i: usize, j: usize| p1_of_xyzz(&row[2 * i + j]);
    let mut i = (1usize << nthrbits) - 1;
    if lsbits - 1 <= nthrbits {
        let mask = (1usize << (nthrbits - (lsbits - 1))) - 1;
        let mut acc = rec(i, 1);
        let mut res = if mask != 0 { blst_p1::default() } else { acc };
        while i > 0 {
            i -= 1;
            add(&mut acc, &rec(i, 1));
            if i & mask == 0 {
                add(&mut res, &acc);
            }
        }
        wipe(&mut acc);
        return res;
    }
    // sppark adds `acc * 2^(lsbits - 1 - nthrbits)` at every step; here the
    // sum of the running sums is doubled once at the end (the same point)
    let mut res = rec(i, 0);
    let mut acc = rec(i, 1);
    let mut raised = blst_p1::default();
    while i > 0 {
        i -= 1;
        add(&mut raised, &acc);
        add(&mut res, &rec(i, 0));
        if i != 0 {
            add(&mut acc, &rec(i, 1));
        }
    }
    for _ in 0..(lsbits - 1 - nthrbits) {
        dbl(&mut raised);
    }
    add(&mut res, &raised);
    wipe(&mut raised);
    wipe(&mut acc);
    res
}

/// The window sums of windows `[lo, hi)` (sppark `collect_rows`). Out of line
/// so its frames lie below the worker's frame, where
/// [`super::secret::scrub_stack`] runs afterwards.
#[inline(never)]
fn collect_rows(
    rows: &[Xyzz],
    lo: usize,
    hi: usize,
    pl: &Plan,
    per_row: usize,
    nthrbits: u32,
) -> SecretVec<blst_p1> {
    let nwins = pl.nwins as usize;
    let mut out = SecretVec::with_capacity(hi - lo);
    for y in lo..hi {
        let dy = if y == nwins - 1 { pl.top } else { pl.wbits };
        let mut s = integrate_row(&rows[y * per_row..(y + 1) * per_row], dy, nthrbits);
        out.push_within(s);
        wipe(&mut s);
    }
    out
}

/// sppark `collect`: the window sums (rows in parallel), the doubling ladder
/// from the top window, plus the digit-1 bucket of window 0 (`ones`). `None`:
/// the rows are short or a worker panicked. Every worker scrubs its stack
/// ([`ScrubOnExit`]); the caller scrubs this thread's.
pub(super) fn collect(
    rows: SecretVec<Xyzz>,
    ones: SecretVec<Xyzz>,
    pl: &Plan,
    nthr: usize,
) -> Option<Secret<blst_p1>> {
    let nwins = pl.nwins as usize;
    let per_row = 2 * nthr;
    let nthrbits = lg2(nthr);
    if rows.len() < nwins * per_row {
        return None;
    }
    let parts = par_parts(nwins, host_threads(), 1, |lo, hi| {
        let _scrub = ScrubOnExit;
        collect_rows(&rows, lo, hi, pl, per_row, nthrbits)
    })?;
    let sums: Vec<&blst_p1> = parts.iter().flat_map(|p| p.iter()).collect();
    if sums.len() != nwins {
        return None;
    }
    let mut out = Secret(blst_p1::default());
    for y in (0..nwins).rev() {
        add(&mut out, sums[y]);
        if y > 0 {
            for _ in 0..pl.wbits {
                dbl(&mut out);
            }
        }
    }
    for r in ones.iter() {
        let mut p = p1_of_xyzz(r);
        add(&mut out, &p);
        wipe(&mut p);
    }
    Some(out)
}

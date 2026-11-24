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

//! One device MSM pass (sppark `invoke`): each chunk's kernels in one command
//! buffer, and each chunk's host collection on its own thread while the
//! device runs the next.

use std::{mem::size_of, sync::Mutex};

use blst::blst_p1;
use objc2_metal::MTLComputePipelineState;

use super::{
    Xyzz,
    collect::{add, collect},
    par::{catch, lock},
    plan::{NBITS, Plan, lg2},
    secret::{ScrubOnExit, Secret, SecretVec},
};
use crate::{
    G1AffineLimbs, Scalar,
    ctx::{Arg, Buffer, Command, Ctx, Error},
};

/// Upper-sort groups per window (sppark: `sm_count / 3`, a power of two).
const SORT_GROUPS: u32 = 8;
/// Threads of a sort group (sppark `SORT_BLOCKDIM`).
const SORT_BLOCK: usize = 1024;
/// Groups of `msm_ones` (sppark: `sm_count` blocks).
const ONES_GROUPS: usize = 32;
/// Threads of an `msm_ones` group (sppark `BATCH_ADD_BLOCK_SIZE`).
const ONES_BLOCK: usize = 256;
/// Threads of an `msm_accumulate` group (`ACC_GROUP` in msm.metal).
const ACC_GROUP: usize = 256;
/// Threads per window of `msm_integrate` (sppark `MSM_NTHREADS`).
const MSM_NTHREADS: usize = 256;
/// The largest low-digit width of the lower sort (`MAX_LOW` in msm.metal).
const MAX_LOW_BITS: u32 = 12;
/// The largest top-digit width of the upper sort (`MAX_TOP` in msm.metal).
const MAX_TOP_BITS: u32 = 9;

/// The SIMD-group width the `msm_ones` reduction and the sort's prefix sums
/// assume.
const SIMD_WIDTH: usize = 32;
/// The kernels whose pipelines must have [`SIMD_WIDTH`].
const KERNELS: [&str; 9] = [
    "msm_digits",
    "msm_sort_count",
    "msm_sort_scan",
    "msm_sort_scatter",
    "msm_sort_lower",
    "msm_bucket_guard",
    "msm_ones",
    "msm_accumulate",
    "msm_integrate",
];

/// The most points one bucket of a chunk may hold (the digit-1 bucket of
/// window 0 excepted). One GPU thread sums a bucket serially, so its length
/// bounds the command buffer's time; `CHUNK_ADDS` assumes balanced buckets.
///
/// With the mask, honest scalars spread evenly over the buckets and stay far
/// below this limit. Scalars chosen as `s_i = c - r_i` send a whole window to
/// one bucket, which can run into the GPU watchdog. Above the limit the chunk
/// skips accumulation and the call declines `device-error`. That decline
/// reveals one bit about the masked scalars, which honest scalars set with
/// negligible probability; it is reported only as a generic `device-error`.
pub(super) const HOT_BUCKET_LIMIT: u32 = 1 << 16;

/// Scalar mode of `msm_digits`: the masked scalars `s + r`.
pub(super) const MODE_MASKED: u32 = 1;
/// Scalar mode of `msm_digits`: the mask `r` alone (scalars not read).
pub(super) const MODE_MASK: u32 = 2;

/// Thread counts that depend on the pipelines.
#[derive(Clone, Copy, Debug)]
pub(super) struct Geometry {
    sort_block: usize,
    ones_block: usize,
    /// `msm_integrate` threads per window (a power of two).
    nthr: usize,
}

impl Geometry {
    /// The thread counts of `pl` on this device, after checking what the
    /// kernels rely on (threadgroup sizes, sort widths, SIMD-group width).
    pub(super) fn of(c: &Ctx, pl: &Plan) -> Result<Geometry, Error> {
        let max = |k: &str| -> Result<usize, Error> {
            Ok(c.pipeline(k)?.maxTotalThreadsPerThreadgroup())
        };
        let pow2_floor = |x: usize| if x == 0 { 0 } else { 1usize << lg2(x) };
        let sort_block = [
            "msm_sort_count",
            "msm_sort_scan",
            "msm_sort_scatter",
            "msm_sort_lower",
        ]
        .iter()
        .map(|k| max(k))
        .try_fold(SORT_BLOCK, |a, m| m.map(|m| a.min(pow2_floor(m))))?;
        let ones_block = pow2_floor(max("msm_ones")?.min(ONES_BLOCK));
        let nthr = pow2_floor(max("msm_integrate")?.min(MSM_NTHREADS));
        if sort_block < 32 || ones_block < 32 || nthr < 2 || lg2(nthr) >= pl.bits {
            return Err(Error::Device(format!(
                "msm: threadgroup sizes {sort_block}/{ones_block}/{nthr} too small"
            )));
        }
        if pl.low_bits > MAX_LOW_BITS || pl.top_bits > MAX_TOP_BITS {
            return Err(Error::Device("msm: window too wide for the sort".into()));
        }
        simd_width_ok(c)?;
        Ok(Geometry {
            sort_block,
            ones_block,
            nthr,
        })
    }

    /// The records `msm_ones` writes: one per 32 threads of its grid.
    pub(super) fn ones_slots(&self) -> usize {
        ONES_GROUPS * self.ones_block / SIMD_WIDTH
    }
}

/// Whether every MSM pipeline has SIMD-groups of [`SIMD_WIDTH`], checked once
/// per process. Another width is a `device-error` decline.
fn simd_width_ok(c: &Ctx) -> Result<(), Error> {
    static OK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let ok = match OK.get() {
        Some(&ok) => ok,
        None => {
            let mut ok = true;
            for k in KERNELS {
                ok &= c.pipeline(k)?.threadExecutionWidth() == SIMD_WIDTH;
            }
            *OK.get_or_init(|| ok)
        }
    };
    if ok {
        Ok(())
    } else {
        Err(Error::Device(
            "msm: a SIMD-group width other than 32".into(),
        ))
    }
}

/// The device buffers of an MSM.
pub(super) struct Bufs<'a> {
    /// The points: a registered table, or the caller's copied for the call.
    pub(super) points: &'a Buffer,
    pub(super) scalars: &'a Buffer,
    /// `nwins` rows of `stride` digits, then of sorted point indices.
    pub(super) digits: &'a Buffer,
    /// The sort's (key, value) pairs of one pass.
    pub(super) temps: &'a Buffer,
    /// The upper sort's per-group counters of one pass.
    pub(super) counts: &'a Buffer,
    /// `nwins` rows of bucket end offsets.
    pub(super) hist: &'a Buffer,
    /// `nwins` rows of bucket sums, then of `msm_integrate` partial sums.
    pub(super) buckets: &'a Buffer,
    /// The partial sums of `msm_ones`.
    pub(super) ones: &'a Buffer,
    /// Set by `msm_bucket_guard` when a bucket exceeds [`HOT_BUCKET_LIMIT`]
    /// (reset by `msm_digits`).
    pub(super) hot: &'a Buffer,
}

/// Byte sizes of the scratch buffers of `pl`, in [`Bufs`] field order from
/// `digits` to `hot`.
pub(super) fn scratch_bytes(pl: &Plan, g: &Geometry) -> [usize; 7] {
    let ntop = 1usize << pl.top_bits;
    let rows = (pl.nwins as usize) << pl.bits;
    [
        pl.nwins as usize * pl.stride * 4,
        pl.pass as usize * pl.stride * 8,
        pl.pass as usize * ntop * SORT_GROUPS as usize * 4,
        rows * 4,
        rows * size_of::<Xyzz>(),
        g.ones_slots() * size_of::<Xyzz>(),
        4,
    ]
}

/// The kernel parameters of one chunk (the `constant` structs of msm.metal).
struct ChunkParams {
    /// `DigitsParams`.
    digits: [u32; 6],
    /// `SortParams` of each sort pass.
    sort: Vec<[u32; 9]>,
    /// `AccParams`.
    acc: [u32; 4],
    /// `IntParams`.
    int: [u32; 3],
}

fn chunk_params(pl: &Plan, mode: u32, h_off: usize, num: usize) -> ChunkParams {
    let sort = (0..pl.nwins)
        .step_by(pl.pass as usize)
        .map(|w0| {
            [
                num as u32,
                pl.stride as u32,
                w0,
                pl.nwins,
                SORT_GROUPS,
                pl.top_bits,
                pl.low_bits,
                pl.bits,
                pl.top - 1,
            ]
        })
        .collect();
    ChunkParams {
        digits: [
            num as u32,
            h_off as u32,
            pl.nwins,
            pl.wbits,
            pl.stride as u32,
            mode,
        ],
        sort,
        acc: [pl.nwins, pl.bits, pl.stride as u32, HOT_BUCKET_LIMIT],
        int: [pl.nwins, pl.wbits, NBITS],
    }
}

fn enc_digits<'a>(
    cmd: &mut Command<'a>,
    b: &Bufs<'a>,
    p: &'a ChunkParams,
    h_off: usize,
    num: usize,
) -> Result<(), Error> {
    // the mask mode does not read the scalars; binding them keeps the input
    // distinct from the output buffer
    let sc = if p.digits[5] == MODE_MASK {
        Arg::Buffer(b.scalars)
    } else {
        Arg::BufferAt(b.scalars, h_off * size_of::<Scalar>())
    };
    cmd.dispatch(
        "msm_digits",
        num,
        &[
            sc,
            Arg::Buffer(b.digits),
            Arg::value(&p.digits),
            Arg::Buffer(b.hot),
        ],
    )
}

fn enc_sort<'a>(
    cmd: &mut Command<'a>,
    b: &Bufs<'a>,
    p: &'a ChunkParams,
    pl: &Plan,
    g: &Geometry,
) -> Result<(), Error> {
    let ntop = 1usize << pl.top_bits;
    for sp in &p.sort {
        // windows of this pass (`sp[2]`, its first window, is below `nwins`)
        let pw = (pl.nwins - sp[2]).min(pl.pass) as usize;
        let groups = pw * SORT_GROUPS as usize;
        let prm = Arg::value(sp);
        cmd.dispatch_groups(
            "msm_sort_count",
            groups,
            g.sort_block,
            &[Arg::Buffer(b.digits), Arg::Buffer(b.counts), prm],
            &[],
        )?;
        cmd.dispatch_groups(
            "msm_sort_scan",
            pw,
            g.sort_block,
            &[Arg::Buffer(b.counts), Arg::Buffer(b.hist), prm],
            &[],
        )?;
        cmd.dispatch_groups(
            "msm_sort_scatter",
            groups,
            g.sort_block,
            &[
                Arg::Buffer(b.digits),
                Arg::Buffer(b.counts),
                Arg::Buffer(b.temps),
                prm,
            ],
            &[],
        )?;
        cmd.dispatch_groups(
            "msm_sort_lower",
            pw * ntop,
            g.sort_block,
            &[
                Arg::Buffer(b.digits),
                Arg::Buffer(b.temps),
                Arg::Buffer(b.hist),
                prm,
            ],
            &[],
        )?;
    }
    Ok(())
}

/// The hot-bucket guard, `msm_ones` and `msm_accumulate`.
fn enc_accumulate<'a>(
    cmd: &mut Command<'a>,
    b: &Bufs<'a>,
    p: &'a ChunkParams,
    pl: &Plan,
    g: &Geometry,
    h_off: usize,
) -> Result<(), Error> {
    let pts = Arg::BufferAt(b.points, h_off * size_of::<G1AffineLimbs>());
    let total = (pl.nwins as usize) << pl.bits;
    cmd.dispatch(
        "msm_bucket_guard",
        total,
        &[Arg::Buffer(b.hist), Arg::Buffer(b.hot), Arg::value(&p.acc)],
    )?;
    cmd.dispatch_groups(
        "msm_ones",
        ONES_GROUPS,
        g.ones_block,
        &[
            Arg::Buffer(b.ones),
            pts,
            Arg::Buffer(b.digits),
            Arg::Buffer(b.hist),
        ],
        &[],
    )?;
    cmd.dispatch_with(
        "msm_accumulate",
        total,
        ACC_GROUP,
        &[
            Arg::Buffer(b.buckets),
            pts,
            Arg::Buffer(b.digits),
            Arg::Buffer(b.hist),
            Arg::value(&p.acc),
            Arg::Buffer(b.hot),
        ],
        &[],
    )
}

fn enc_integrate<'a>(
    cmd: &mut Command<'a>,
    b: &Bufs<'a>,
    p: &'a ChunkParams,
    pl: &Plan,
    g: &Geometry,
) -> Result<(), Error> {
    cmd.dispatch_groups(
        "msm_integrate",
        pl.nwins as usize,
        g.nthr,
        &[Arg::Buffer(b.buckets), Arg::value(&p.int)],
        &[],
    )
}

/// A chunk's partial sums on the host: `2 * nthr` records per window from
/// `msm_integrate`, and the `msm_ones` records.
type Partials = (SecretVec<Xyzz>, SecretVec<Xyzz>);

/// One device MSM pass (sppark `invoke`) over the first `pl.n` points with the
/// scalars of `mode`. Returns the sum and the GPU time.
///
/// Each chunk's partial sums are combined on a host thread while the device
/// runs the next chunk. Any chunk or collection failure is an error, returned
/// after every started collection has been joined.
pub(super) fn run(
    c: &Ctx,
    b: &Bufs<'_>,
    pl: &Plan,
    g: &Geometry,
    mode: u32,
) -> Result<(Secret<blst_p1>, u64), Error> {
    // each chunk's collection inputs, taken by its thread (or by this thread
    // when that thread could not be started)
    type Inputs = Mutex<Option<Partials>>;
    let inputs: Vec<Inputs> = (0..pl.batch).map(|_| Mutex::new(None)).collect();
    let nthr = g.nthr;
    let collect_inputs = |i: &Inputs| {
        let _scrub = ScrubOnExit;
        lock(i).take().and_then(|(rows, ones)| collect(rows, ones, pl, nthr))
    };
    std::thread::scope(|sc| {
        enum Pending<'s> {
            Thread(std::thread::ScopedJoinHandle<'s, Option<Secret<blst_p1>>>),
            Done(Option<Secret<blst_p1>>),
        }
        let mut pending = Vec::with_capacity(pl.batch);
        let mut gpu = 0u64;
        let mut h_off = 0usize;
        let mut err = None;
        for slot in &inputs {
            let num = pl.stride.min(pl.n - h_off);
            match run_chunk(c, b, pl, g, mode, h_off, num) {
                Ok((ns, partials)) => {
                    gpu += ns;
                    *lock(slot) = Some(partials);
                }
                Err(e) => {
                    err = Some(e);
                    break;
                }
            }
            let job = move || collect_inputs(slot);
            match std::thread::Builder::new().spawn_scoped(sc, job) {
                Ok(h) => pending.push(Pending::Thread(h)),
                Err(_) => pending.push(Pending::Done(catch(job).flatten())),
            }
            h_off += num;
        }
        let mut out = Secret(blst_p1::default());
        for h in pending {
            let r = match h {
                Pending::Thread(h) => h.join().ok().flatten(),
                Pending::Done(r) => r,
            };
            match r {
                Some(p) => add(&mut out, &p),
                None => err = err.or(Some(Error::Device("msm: host collect failed".into()))),
            }
        }
        match err {
            Some(e) => Err(e),
            None => Ok((out, gpu)),
        }
    })
}

/// Runs the chunk of `num` points from `h_off` in one command buffer and
/// copies out its partial sums before the next chunk reuses the buffers.
fn run_chunk(
    c: &Ctx,
    b: &Bufs<'_>,
    pl: &Plan,
    g: &Geometry,
    mode: u32,
    h_off: usize,
    num: usize,
) -> Result<(u64, Partials), Error> {
    let p = chunk_params(pl, mode, h_off, num);
    let ((), ns) = c.run(|cmd| {
        enc_digits(cmd, b, &p, h_off, num)?;
        enc_sort(cmd, b, &p, pl, g)?;
        enc_accumulate(cmd, b, &p, pl, g, h_off)?;
        enc_integrate(cmd, b, &p, pl, g)
    })?;
    // a bucket above the bound skipped accumulation: decline with the generic
    // message of any failed command buffer
    if b.hot.as_slice::<u32>().first().is_none_or(|&h| h != 0) {
        return Err(Error::Device("msm: a command buffer failed".into()));
    }
    let partials = copy_partials(b, pl, g).ok_or_else(|| Error::Memory("msm scratch".into()))?;
    Ok((ns, partials))
}

/// The partial sums of the chunk just run, copied into guards; `None` when a
/// device buffer is shorter than the plan needs.
fn copy_partials(b: &Bufs<'_>, pl: &Plan, g: &Geometry) -> Option<Partials> {
    let per_row = 2 * g.nthr;
    let row_len = 1usize << pl.bits;
    let bk = b.buckets.as_slice::<Xyzz>();
    let mut rows = SecretVec::with_capacity(pl.nwins as usize * per_row);
    let mut ok = true;
    for y in 0..pl.nwins as usize {
        ok &= bk
            .get(y * row_len..y * row_len + per_row)
            .is_some_and(|r| rows.extend_within(r));
    }
    let mut ones = SecretVec::with_capacity(g.ones_slots());
    ok &= b
        .ones
        .as_slice::<Xyzz>()
        .get(..g.ones_slots())
        .is_some_and(|o| ones.extend_within(o));
    ok.then_some((rows, ones))
}

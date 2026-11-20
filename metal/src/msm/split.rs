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

//! The MSM of one call: the device share as `MSM(s + r) - MSM(r)` and the CPU
//! share on its own thread, added on the host.

use std::mem::{size_of, size_of_val};

use blst::{blst_p1, blst_p1_cneg};

use super::{
    Served, Trace,
    collect::{add, limbs_of, p1_of},
    par::{catch, lock, par_parts},
    pipeline::{Bufs, Geometry, MODE_MASK, MODE_MASKED, run, scratch_bytes},
    plan::{Plan, device_share, plan},
    registry::MaskCache,
    secret::{ScrubOnExit, Secret, scrub_stack},
};
use crate::{
    G1AffineLimbs, Scalar,
    ctx::{self, Buffer, Error, Session},
};

/// The points of the device share.
pub(super) enum Points<'a> {
    /// A registered table's device buffer (a prefix of it is used).
    Table(&'a Buffer),
    /// The caller's points, copied for the call.
    Host(&'a [G1AffineLimbs]),
}

const K_SCALARS: &str = "msm-scalars";
const K_POINTS: &str = "msm-points";
const K_DIGITS: &str = "msm-digits";
const K_TEMPS: &str = "msm-temps";
const K_COUNTS: &str = "msm-counts";
const K_HIST: &str = "msm-hist";
const K_BUCKETS: &str = "msm-buckets";
const K_ONES: &str = "msm-ones";
const K_HOT: &str = "msm-hot";

/// Splits the MSM: the device takes `[0, m)` masked, the CPU `[m, n)` on
/// another thread (or on this one after the device share when no thread can
/// be started). `masks`: the table's cache of `MSM(r)`.
pub(super) fn split(
    s: &mut Session,
    points: Points<'_>,
    scalars: &[Scalar],
    bases: &[G1AffineLimbs],
    masks: Option<&MaskCache>,
    mut trace: Trace<'_>,
) -> Result<Served, Error> {
    let n = scalars.len();
    let m = device_share(n, matches!(points, Points::Table(_)));
    trace!(trace, |st| st.device_points += m as u64);
    if m == n {
        return masked(s, points, scalars, masks, trace);
    }
    let points = match points {
        Points::Host(b) => Points::Host(&b[..m]),
        t => t,
    };
    let (cs, cb) = (&scalars[m..], &bases[m..]);
    let cpu_share = move || {
        let _scrub = ScrubOnExit;
        cpu_msm(cs, cb)
    };
    let (dev, cpu) = std::thread::scope(|sc| {
        let h = std::thread::Builder::new()
            .name("midnight-metal-msm-share".into())
            .spawn_scoped(sc, cpu_share)
            .ok();
        let dev = masked(s, points, &scalars[..m], masks, trace);
        let cpu = match h {
            Some(h) => h.join().ok().flatten(),
            None => catch(cpu_share).flatten(),
        };
        (dev, cpu)
    });
    // on every early return below, the guards zero the other share's sum
    let Some(cpu) = cpu else {
        return Err(Error::Device("msm: the CPU share failed".into()));
    };
    let (d, ns) = dev?;
    let mut sum = Secret(p1_of(&d));
    add(&mut sum, &cpu);
    Ok((Secret(limbs_of(&sum)), ns))
}

/// The thread pool of the CPU share: its own threads, so that the share
/// never waits for a worker of the caller's pool (the prover calls MSMs from
/// rayon workers, which may all be blocked on the device lock).
pub(super) fn cpu_pool() -> Option<&'static rayon::ThreadPool> {
    static POOL: std::sync::OnceLock<Option<rayon::ThreadPool>> = std::sync::OnceLock::new();
    POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(std::thread::available_parallelism().map_or(4, |t| t.get()))
            .thread_name(|i| format!("midnight-metal-msm-cpu-{i}"))
            .build()
            .ok()
    })
    .as_ref()
}

/// The CPU share: the stock `msm_pippenger` on the share's own pool, over the
/// caller's slices. Afterwards each pool thread scrubs its stack.
fn cpu_msm(scalars: &[Scalar], bases: &[G1AffineLimbs]) -> Option<Secret<blst_p1>> {
    use midnight_curves::{Fq, G1Affine, G1Projective, msm::msm_pippenger};
    // SAFETY: `Fq` is a transparent `blst_fr` (`[u64; 4]`) and `G1Affine` a
    // transparent `blst_p1_affine` (`[u64; 12]`), with the sizes and
    // alignments of `Scalar` and `G1AffineLimbs` (asserted in the parent
    // module); the scalars were checked reduced at admission.
    let (s, b) = unsafe {
        (
            &*(scalars as *const [Scalar] as *const [Fq]),
            &*(bases as *const [G1AffineLimbs] as *const [G1Affine]),
        )
    };
    let pool = cpu_pool()?;
    let r = pool.install(|| {
        let r: G1Projective = msm_pippenger(s, b);
        // SAFETY: `G1Projective` is a transparent `blst_p1` (sizes asserted
        // in the parent module).
        Secret(unsafe { std::mem::transmute::<G1Projective, blst_p1>(r) })
    });
    pool.broadcast(|_| scrub_stack());
    Some(r)
}

/// `MSM(s + r) - MSM(r)` on the device, with `MSM(r)` from `masks` when cached
/// (stored there otherwise). Returns the result and the GPU time.
fn masked(
    s: &mut Session,
    points: Points<'_>,
    scalars: &[Scalar],
    masks: Option<&MaskCache>,
    mut trace: Trace<'_>,
) -> Result<Served, Error> {
    let n = scalars.len();
    let pl = plan(n);
    let c = s.ctx();
    let geo = Geometry::of(c, &pl)?;
    let bufs = bind_buffers(s, &pl, &geo, scalars, points)?;

    let mut ns = 0u64;
    let cached = masks.and_then(|m| lock(m).get(&n).copied());
    let rr = match cached {
        Some(rr) => rr,
        None => {
            let (rr, t) = run(c, &bufs, &pl, &geo, MODE_MASK)?;
            ns += t;
            let rr = limbs_of(&rr);
            if let Some(m) = masks {
                lock(m).insert(n, rr);
            }
            rr
        }
    };
    let (mut sr, t) = run(c, &bufs, &pl, &geo, MODE_MASKED)?;
    ns += t;
    trace!(trace, |st| {
        st.wbits = pl.wbits;
        st.batches = pl.batch as u32;
        st.passes = if cached.is_some() { 1 } else { 2 };
    });
    let mut nr = p1_of(&rr);
    // SAFETY: a valid blst point.
    unsafe { blst_p1_cneg(&mut nr, true) };
    add(&mut sr, &nr);
    Ok((Secret(limbs_of(&sr)), ns))
}

/// Binds the scratch buffers of `pl`, copying in the scalars (and the points
/// on the one-shot path).
fn bind_buffers<'s>(
    s: &'s mut Session,
    pl: &Plan,
    geo: &Geometry,
    scalars: &[Scalar],
    points: Points<'s>,
) -> Result<Bufs<'s>, Error> {
    let short = || Error::Memory("msm scratch".into());
    let keys = [
        K_DIGITS, K_TEMPS, K_COUNTS, K_HIST, K_BUCKETS, K_ONES, K_HOT,
    ];
    for (k, bytes) in keys.into_iter().zip(scratch_bytes(pl, geo)) {
        s.scratch(k, bytes)?;
    }
    write_parallel(s.scratch(K_SCALARS, size_of_val(scalars))?, scalars)?;
    if let Points::Host(b) = points {
        write_parallel(s.scratch(K_POINTS, size_of_val(b))?, b)?;
    }
    let s: &'s Session = s;
    let [digits, temps, counts, hist, buckets, ones, hot, sc] = s
        .scratch_many([
            K_DIGITS, K_TEMPS, K_COUNTS, K_HIST, K_BUCKETS, K_ONES, K_HOT, K_SCALARS,
        ])
        .ok_or_else(short)?;
    let points = match points {
        Points::Table(b) => b,
        Points::Host(_) => s.get_scratch(K_POINTS).ok_or_else(short)?,
    };
    Ok(Bufs {
        points,
        scalars: sc,
        digits,
        temps,
        counts,
        hist,
        buckets,
        ones,
        hot,
    })
}

/// Copies `data` to the start of `buf` on a few threads; a part whose thread
/// cannot be started is copied on this thread.
fn write_parallel<T: ctx::Pod + Sync + Send>(buf: &mut Buffer, data: &[T]) -> Result<(), Error> {
    const PART: usize = 1 << 20;
    let short = || Error::Memory("msm scratch".into());
    let dst = buf.as_mut_slice::<T>().get_mut(..data.len()).ok_or_else(short)?;
    if size_of_val(data) <= PART {
        dst.copy_from_slice(data);
        return Ok(());
    }
    let base = dst.as_mut_ptr() as usize;
    par_parts(data.len(), 4, PART / size_of::<T>().max(1), |a, b| {
        // SAFETY: `dst` holds `data.len()` elements and the parts `[a, b)`
        // are disjoint and within it; `dst` is borrowed exclusively for the
        // call.
        unsafe {
            std::ptr::copy_nonoverlapping(data[a..b].as_ptr(), (base as *mut T).add(a), b - a)
        }
    })
    .map(|_| ())
    .ok_or_else(|| Error::Device("msm: a host copy failed".into()))
}

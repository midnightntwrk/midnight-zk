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

//! The scalar-field NTT on the device, and device-side building blocks of the
//! coset transforms for the quotient.
//!
//! [`fft`] and [`ifft`] take only the standard `2^log_n`-th root of unity (as
//! `EvaluationDomain` derives it) or its inverse; any other root declines
//! `shape`.
//!
//! The kernel (`shaders/ntt.metal`) is a Stockham transform with natural
//! order in and out: `ceil(log_n / 10)` passes of near-equal radix up to
//! `2^10`, each done in threadgroup memory (32 KiB holds 1024 elements).
//! The transform is bound by field multiplications, not memory, so the design
//! minimises passes. Passes ping-pong with a scratch buffer, and an inverse
//! transform's divisor is folded into the last pass.
//!
//! Twiddles: per direction, `w_{2^16}^j` and `w_{2^28}^j` (`j < 2^12`) serve
//! every size up to `2^28` with at most one product per factor. They are
//! public and stay on the device for the life of the process.

use std::sync::{Mutex, OnceLock};

use blst::{blst_fr, blst_fr_inverse, blst_fr_mul, blst_fr_sqr};

use crate::{
    MAX_LOG_N, Scalar,
    account::{self, Class, Reason},
    ctx::{self, Arg, Buffer, Command, Ctx, Error, Pod},
    field,
};

/// Bytes of one scalar.
const SCALAR_BYTES: usize = 32;

/// `2^S` is the largest power of two dividing `r - 1`.
const S: u32 = 32;

/// `ROOT_OF_UNITY` of `midnight_curves::Fq`, Montgomery limbs.
const ROOT_OF_UNITY: Scalar = [
    0xb9b5_8d8c_5f0e_466a,
    0x5b1b_4c80_1819_d7ec,
    0x0af5_3ae3_52a3_1e64,
    0x5bf3_adda_19e9_b27b,
];

/// The factors of the passes are powers of the `2^UNIVERSAL_LOG`-th root.
const UNIVERSAL_LOG: u32 = 28;
const _: () = assert!(MAX_LOG_N <= UNIVERSAL_LOG);

/// Log2 of the length of the high twiddle table (`w_{2^HI_BITS}^j`); the
/// low table (`w_{2^28}^j`) has `2^(28 - HI_BITS)` elements.
const HI_BITS: u32 = 16;

/// Bytes of the scaled low twiddle table a transform with a divisor
/// allocates; the quotient's memory need counts it.
pub(crate) const SCALE_TABLE_BYTES: usize = SCALAR_BYTES << (UNIVERSAL_LOG - HI_BITS);

/// The largest radix (log2) of a pass: `2^MAX_PASS_LOG` elements fill a
/// threadgroup's 32 KiB.
const MAX_PASS_LOG: u32 = 10;

/// Log2 of the elements one threadgroup holds (radix times columns).
const GROUP_LOG: u32 = 10;

/// Field multiplications per command buffer, a fraction of a second of GPU
/// time. A pass is never split.
const RUN_BUDGET: u64 = 1_500_000_000;

/// The direction of a transform.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Dir {
    /// At the standard root `w_n`.
    Forward,
    /// At `w_n^-1`.
    Inverse,
}

impl Dir {
    /// The index of the direction in the root and twiddle tables.
    fn index(self) -> usize {
        match self {
            Dir::Forward => 0,
            Dir::Inverse => 1,
        }
    }
}

// ---------------------------------------------------------------------------
// Host field operations (blst)

/// `a * b` in `Fr` (Montgomery limbs).
fn mul(a: &Scalar, b: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: valid pointers to blst_fr values.
    unsafe { blst_fr_mul(&mut r, &blst_fr { l: *a }, &blst_fr { l: *b }) };
    r.l
}

/// `a^2` in `Fr`.
fn square(a: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: as `mul`.
    unsafe { blst_fr_sqr(&mut r, &blst_fr { l: *a }) };
    r.l
}

/// `a^-1` in `Fr` (`a` non-zero).
fn invert(a: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: as `mul`; the argument is a root of unity, never zero.
    unsafe { blst_fr_inverse(&mut r, &blst_fr { l: *a }) };
    r.l
}

/// `roots[dir][m]`: the standard `2^m`-th root of unity (`m <= 28`) or its
/// inverse.
fn roots() -> &'static [[Scalar; UNIVERSAL_LOG as usize + 1]; 2] {
    static ROOTS: OnceLock<[[Scalar; UNIVERSAL_LOG as usize + 1]; 2]> = OnceLock::new();
    ROOTS.get_or_init(|| {
        let mut w = ROOT_OF_UNITY;
        for _ in UNIVERSAL_LOG..S {
            w = square(&w);
        }
        let mut fwd = [[0u64; 4]; UNIVERSAL_LOG as usize + 1];
        let mut inv = fwd;
        let mut wi = invert(&w);
        for m in (0..=UNIVERSAL_LOG as usize).rev() {
            fwd[m] = w;
            inv[m] = wi;
            w = square(&w);
            wi = square(&wi);
        }
        [fwd, inv]
    })
}

/// The standard `2^log_n`-th root of unity of `Fr` (`dir` forward) or its
/// inverse; `None` above `2^28`.
pub(crate) fn std_root(log_n: u32, dir: Dir) -> Option<Scalar> {
    (log_n <= UNIVERSAL_LOG).then(|| roots()[dir.index()][log_n as usize])
}

/// The direction of `omega` for a `2^log_n` transform, if it is the standard
/// root or its inverse.
fn direction(omega: &Scalar, log_n: u32) -> Option<Dir> {
    if std_root(log_n, Dir::Forward).as_ref() == Some(omega) {
        Some(Dir::Forward)
    } else if std_root(log_n, Dir::Inverse).as_ref() == Some(omega) {
        Some(Dir::Inverse)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Twiddle tables (public, resident)

/// `hi[dir]`: `w_{2^H}^j`, `j < 2^H`; `lo[dir]`: `w_{2^28}^j`,
/// `j < 2^(28 - H)` (`H` = [`HI_BITS`]; 2 MiB in all).
struct Tables {
    hi: [Buffer; 2],
    lo: [Buffer; 2],
}

/// `[1, w, w^2, ..., w^(len - 1)]`.
fn powers(w: &Scalar, len: usize) -> Vec<Scalar> {
    let mut v = Vec::with_capacity(len);
    // Montgomery one: 2^256 mod r
    let mut acc: Scalar = [
        0x0000_0001_ffff_fffe,
        0x5884_b7fa_0003_4802,
        0x998c_4fef_ecbc_4ff5,
        0x1824_b159_acc5_056f,
    ];
    for _ in 0..len {
        v.push(acc);
        acc = mul(&acc, w);
    }
    v
}

/// The twiddle tables, made at the first transform.
static TABLES: Mutex<Option<&'static Tables>> = Mutex::new(None);

/// The twiddle tables (made at the first call, kept for the process).
fn tables(ctx: &Ctx) -> Result<&'static Tables, Error> {
    let hb = HI_BITS;
    let mut t = TABLES.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(t) = *t {
        return Ok(t);
    }
    let r = roots();
    let make = |dir: usize, m: u32, bits: u32| ctx.upload(&powers(&r[dir][m as usize], 1 << bits));
    let lb = UNIVERSAL_LOG - hb;
    let made = Tables {
        hi: [make(0, hb, hb)?, make(1, hb, hb)?],
        lo: [make(0, UNIVERSAL_LOG, lb)?, make(1, UNIVERSAL_LOG, lb)?],
    };
    // public data kept for the life of the process
    let leaked: &'static Tables = Box::leak(Box::new(made));
    *t = Some(leaked);
    Ok(leaked)
}

// ---------------------------------------------------------------------------
// Plan

/// The parameters of one pass (`ntt::PassParams` of the shader).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
struct PassParams {
    log_n: u32,
    log_r: u32,
    log_p: u32,
    log_g: u32,
    flags: u32,
    n_src: u32,
    hi_bits: u32,
    pad: u32,
    z1: Scalar,
    z2: Scalar,
}
// SAFETY: `repr(C)`, eight `u32` then two `[u64; 4]`: no padding, every bit
// pattern valid.
unsafe impl Pod for PassParams {}

/// Pass flag: multiply the inputs by the pass factors.
const F_TWIDDLE: u32 = 1;
/// Pass flag: the factors read the high and the low table.
const F_TWO_LEVEL: u32 = 2;
/// Pass flag: the input is `coeff_to_extended`'s (distributed, zero-padded).
const F_COSET: u32 = 4;

/// The radices (log2) of the passes of a `2^log_n` transform: as few passes
/// as the threadgroup memory allows, of near-equal radices (larger first).
fn plan(log_n: u32) -> Vec<u32> {
    let passes = log_n.div_ceil(MAX_PASS_LOG).max(1);
    let base = log_n / passes;
    let extra = log_n % passes;
    (0..passes).map(|i| base + u32::from(i < extra)).collect()
}

/// Log2 of the columns of one threadgroup of a pass of radix `2^r` in a
/// `2^log_n` transform.
fn group_columns_log(log_n: u32, r: u32) -> u32 {
    GROUP_LOG.saturating_sub(r).min(log_n - r)
}

/// Threads of one threadgroup of a pass holding `2^e_log` elements: one per
/// four elements, the measured best.
fn group_threads(e_log: u32) -> usize {
    1usize << e_log.saturating_sub(2)
}

/// The threadgroup size of each `ntt_pass` dispatch of a `2^log_n` transform.
#[cfg(test)]
pub(crate) fn pass_group_threads(log_n: u32) -> Vec<usize> {
    plan(log_n)
        .into_iter()
        .map(|r| group_threads(r + group_columns_log(log_n, r)))
        .collect()
}

/// Scratch bytes of a [`ntt_dev`] or [`coeff_to_extended_dev_at`] of `2^log_n`:
/// none for one pass (`log_n <= 10`), else the transform's length.
pub(crate) fn scratch_bytes(log_n: u32) -> usize {
    if plan(log_n).len() > 1 {
        SCALAR_BYTES << log_n
    } else {
        0
    }
}

/// What a sequence of passes reads and writes.
struct Job<'b> {
    log_n: u32,
    dir: Dir,
    /// The first pass's input: `2^log_n` elements, or `n_src` with `coset`.
    src: &'b Buffer,
    /// The result's buffer, and the byte offset of the result in it.
    dst: &'b Buffer,
    dst_off: usize,
    /// Scratch of `2^log_n` elements (unused by one pass).
    tmp: &'b Buffer,
    /// The divisor folded into the last pass.
    scale: Option<Scalar>,
    /// `(n_src, [z1, z2])`: the first pass reads `src` as coeff_to_extended
    /// does: `src[i] * [1, z1, z2][i mod 3]` for `i < n_src`, zero beyond.
    coset: Option<(usize, [Scalar; 2])>,
    /// `(t, log_tn)`: before the first pass, `src[i] *= t[i mod 2^log_tn]`
    /// (`src` is then `dst` at offset 0).
    pre_mul: Option<(&'b Buffer, u32)>,
    /// After the last pass, `dst[i] *= [1, z1, z2][i mod 3]`.
    post_zeta: Option<[Scalar; 2]>,
}

/// `b` holds at least `elems` scalars.
fn check_len(b: &Buffer, elems: usize, what: &str) -> Result<(), Error> {
    if b.len_bytes() < elems * SCALAR_BYTES {
        return Err(Error::Device(format!(
            "ntt: the {what} buffer holds {} bytes, {} needed",
            b.len_bytes(),
            elems * SCALAR_BYTES
        )));
    }
    Ok(())
}

/// A buffer and a byte offset in it.
type At<'b> = (&'b Buffer, usize);

/// Checks the scalar arguments, size and buffers of `job` before any device
/// work. An unreduced scalar is [`Error::Unreduced`]: the kernels silently
/// mis-compute on such inputs.
fn check_job(job: &Job<'_>) -> Result<(), Error> {
    let by_value = job
        .scale
        .iter()
        .chain(job.coset.iter().flat_map(|(_, z)| z.iter()))
        .chain(job.post_zeta.iter().flatten());
    for v in by_value {
        if !field::is_reduced(v) {
            return Err(Error::Unreduced(format!(
                "ntt: a scalar argument {v:x?} is not below the modulus"
            )));
        }
    }
    let log_n = job.log_n;
    if log_n == 0 || log_n > MAX_LOG_N {
        return Err(Error::Device(format!("ntt: size 2^{log_n}")));
    }
    let n = 1usize << log_n;
    let passes = plan(log_n).len();
    if !job.dst_off.is_multiple_of(SCALAR_BYTES)
        || job.dst.len_bytes() < job.dst_off + n * SCALAR_BYTES
        || (job.dst_off != 0
            && (std::ptr::eq(job.src, job.dst) || job.pre_mul.is_some() || job.post_zeta.is_some()))
    {
        return Err(Error::Device(format!(
            "ntt: the data buffer holds {} bytes, {} needed at offset {}",
            job.dst.len_bytes(),
            n * SCALAR_BYTES,
            job.dst_off
        )));
    }
    if job.pre_mul.is_some() && (!std::ptr::eq(job.src, job.dst) || job.coset.is_some()) {
        return Err(Error::Device("ntt: a periodic factor on a copy".into()));
    }
    if passes > 1 {
        check_len(job.tmp, n, "scratch")?;
        if std::ptr::eq(job.tmp, job.dst) || std::ptr::eq(job.tmp, job.src) {
            return Err(Error::Device("ntt: the scratch is also the data".into()));
        }
    }
    match job.coset {
        Some((n_src, _)) if n_src > n => Err(Error::Device(
            "ntt: source longer than the transform".into(),
        )),
        Some((n_src, _)) => check_len(job.src, n_src, "source"),
        None => check_len(job.src, n, "source"),
    }
}

/// The (input, output) of each pass: passes alternate between `tmp` and
/// `dst`, never writing their own input; the last writes `dst`.
fn pass_io<'b>(job: &Job<'b>, passes: usize) -> Vec<(At<'b>, At<'b>)> {
    let mut cur = (job.src, 0);
    (0..passes)
        .map(|q| {
            let out = if q + 1 == passes || q % 2 == 1 {
                (job.dst, job.dst_off)
            } else {
                (job.tmp, 0)
            };
            let pair = (cur, out);
            cur = out;
            pair
        })
        .collect()
}

/// The parameters of each pass of `job` with the radices `radices`;
/// `scaled`: the last pass folds in the divisor.
fn pass_params(job: &Job<'_>, radices: &[u32], scaled: bool) -> Vec<PassParams> {
    let passes = radices.len();
    let mut params = Vec::with_capacity(passes);
    let mut log_p = 0u32;
    for (q, &r) in radices.iter().enumerate() {
        let scale_here = q + 1 == passes && scaled;
        let log_pr = log_p + r;
        let mut flags = 0;
        if log_p > 0 || scale_here {
            flags |= F_TWIDDLE;
        }
        if log_pr > HI_BITS || scale_here {
            flags |= F_TWO_LEVEL;
        }
        let mut p = PassParams {
            log_n: job.log_n,
            log_r: r,
            log_p,
            log_g: group_columns_log(job.log_n, r),
            flags,
            hi_bits: HI_BITS,
            ..Default::default()
        };
        if let (0, Some((n_src, z))) = (q, job.coset) {
            p.flags |= F_COSET;
            p.n_src = n_src as u32;
            p.z1 = z[0];
            p.z2 = z[1];
        }
        params.push(p);
        log_p = log_pr;
    }
    params
}

/// The end of the command buffer that starts at pass `q`: the passes
/// `q..end` stay within [`RUN_BUDGET`] (at least one pass).
fn run_end(params: &[PassParams], q: usize, n: usize) -> usize {
    let mut end = q;
    let mut cost = 0u64;
    while end < params.len() {
        let p = &params[end];
        let c = (n as u64) * (u64::from(p.log_r) / 2 + 1 + 2 * u64::from(p.flags & F_TWIDDLE));
        if end > q && cost + c > RUN_BUDGET {
            break;
        }
        cost += c;
        end += 1;
    }
    end
}

/// Runs the passes of `job` in as many command buffers as [`RUN_BUDGET`]
/// asks. Returns the GPU time.
fn run_job(ctx: &Ctx, job: &Job<'_>) -> Result<u64, Error> {
    check_job(job)?;
    let n = 1usize << job.log_n;
    let radices = plan(job.log_n);
    let passes = radices.len();
    let tables = tables(ctx)?;
    let d = job.dir.index();
    let hi = &tables.hi[d];

    // the divisor is folded into a scaled copy of the low table, made in the
    // first command buffer
    let scaled = match job.scale {
        Some(_) => Some(ctx.alloc_pooled(SCALE_TABLE_BYTES)?),
        None => None,
    };
    let io = pass_io(job, passes);
    let params = pass_params(job, &radices, scaled.is_some());

    let mut ns = 0;
    let mut q = 0;
    while q < passes {
        let end = run_end(&params, q, n);
        let lo = scaled.as_ref();
        let first = q == 0;
        let last_cb = end == passes;
        ns += ctx
            .run(|cmd| {
                if let (true, Some((t, log_tn))) = (first, job.pre_mul) {
                    encode_mul_periodic(cmd, job.dst, n, t, log_tn)?;
                }
                if let (true, Some(b), Some(c)) = (first, lo, job.scale.as_ref()) {
                    cmd.dispatch(
                        "ntt_scale_copy",
                        1usize << (UNIVERSAL_LOG - HI_BITS),
                        &[Arg::Buffer(&tables.lo[d]), Arg::Buffer(b), Arg::value(c)],
                    )?;
                }
                for i in q..end {
                    let p = &params[i];
                    let lo_tab = match (i + 1 == passes, lo) {
                        (true, Some(s)) => s,
                        _ => &tables.lo[d],
                    };
                    let ((src, src_off), (dst, dst_off)) = io[i];
                    let args = [
                        Arg::BufferAt(src, src_off),
                        Arg::BufferAt(dst, dst_off),
                        Arg::Buffer(hi),
                        Arg::Buffer(lo_tab),
                        Arg::value(p),
                    ];
                    let e_log = p.log_r + p.log_g;
                    cmd.dispatch_groups(
                        "ntt_pass",
                        n >> e_log,
                        group_threads(e_log),
                        &args,
                        &[SCALAR_BYTES << e_log],
                    )?;
                }
                if let (true, Some(z)) = (last_cb, job.post_zeta.as_ref()) {
                    // the data is at offset 0 here (checked by `check_job`)
                    encode_distribute_zeta(cmd, job.dst, n, z)?;
                }
                Ok(())
            })?
            .1;
        q = end;
    }
    Ok(ns)
}

// ---------------------------------------------------------------------------
// Building blocks (device buffers, nothing read back)
//
// The caller holds the device for the whole sequence. The data must already
// be reduced, and so must every scalar argument (else `Error::Unreduced`
// before any device work). After an `Err` the data and scratch are undefined:
// earlier command buffers may have transformed them in part.

/// The NTT of the first `2^log_n` elements of `a`, in place, natural order,
/// at `w_n` or `w_n^-1`, then times `scale` if given. `tmp` is scratch of at
/// least [`scratch_bytes`]`(log_n)` bytes (unused, and may be `a`, for
/// `log_n <= 10`). Returns the GPU time.
pub(crate) fn ntt_dev(
    ctx: &Ctx,
    a: &Buffer,
    tmp: &Buffer,
    log_n: u32,
    dir: Dir,
    scale: Option<&Scalar>,
) -> Result<u64, Error> {
    run_job(
        ctx,
        &Job {
            log_n,
            dir,
            src: a,
            dst: a,
            dst_off: 0,
            tmp,
            scale: scale.copied(),
            coset: None,
            pre_mul: None,
            post_zeta: None,
        },
    )
}

/// `coeff_to_extended` on the device: writes `2^ext_k` elements of `dst` from
/// byte offset `dst_off` (a multiple of 32, so a coset lands in place in a
/// larger buffer): the forward NTT of `src[i] * [1, zeta[0], zeta[1]][i mod 3]`
/// for `i < 2^k`, zero-padded. The distribution and padding happen in the
/// first pass. `zeta` is `[g_coset, g_coset_inv]`. Returns the GPU time.
#[allow(clippy::too_many_arguments)]
pub(crate) fn coeff_to_extended_dev_at(
    ctx: &Ctx,
    src: &Buffer,
    dst: &Buffer,
    dst_off: usize,
    tmp: &Buffer,
    k: u32,
    ext_k: u32,
    zeta: &[Scalar; 2],
) -> Result<u64, Error> {
    if k < 1 || k > ext_k || ext_k > MAX_LOG_N {
        return Err(Error::Device(format!(
            "coeff_to_extended: dimensions k {k}, ext_k {ext_k}"
        )));
    }
    if std::ptr::eq(src, dst) || std::ptr::eq(src, tmp) {
        return Err(Error::Device(
            "coeff_to_extended: the source is also the destination or the scratch".into(),
        ));
    }
    run_job(
        ctx,
        &Job {
            log_n: ext_k,
            dir: Dir::Forward,
            src,
            dst,
            dst_off,
            tmp,
            scale: None,
            coset: Some((1usize << k, *zeta)),
            pre_mul: None,
            post_zeta: None,
        },
    )
}

/// `extended_to_coeff` in place on `a[..2^ext_k]`: the inverse NTT times
/// `divisor`, then [`encode_distribute_zeta`] with `zeta_out`. Returns the GPU
/// time.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn extended_to_coeff_dev(
    ctx: &Ctx,
    a: &Buffer,
    tmp: &Buffer,
    ext_k: u32,
    divisor: &Scalar,
    zeta_out: &[Scalar; 2],
) -> Result<u64, Error> {
    run_job(
        ctx,
        &Job {
            log_n: ext_k,
            dir: Dir::Inverse,
            src: a,
            dst: a,
            dst_off: 0,
            tmp,
            scale: Some(*divisor),
            coset: None,
            pre_mul: None,
            post_zeta: Some(*zeta_out),
        },
    )
}

/// [`encode_mul_periodic`] by `t` (the division by the vanishing polynomial),
/// then `extended_to_coeff` as [`extended_to_coeff_dev`], fused into the same
/// command buffers. `t` must be reduced too. Returns the GPU time.
#[allow(clippy::too_many_arguments)]
pub(crate) fn divide_extended_to_coeff_dev(
    ctx: &Ctx,
    a: &Buffer,
    tmp: &Buffer,
    ext_k: u32,
    divisor: &Scalar,
    zeta_out: &[Scalar; 2],
    t: &Buffer,
    log_tn: u32,
) -> Result<u64, Error> {
    run_job(
        ctx,
        &Job {
            log_n: ext_k,
            dir: Dir::Inverse,
            src: a,
            dst: a,
            dst_off: 0,
            tmp,
            scale: Some(*divisor),
            coset: None,
            pre_mul: Some((t, log_tn)),
            post_zeta: Some(*zeta_out),
        },
    )
}

/// Checks that `a` holds `n <= 2^MAX_LOG_N` scalars.
fn elementwise_len(a: &Buffer, n: usize) -> Result<(), Error> {
    check_len(a, n, "data")?;
    if n > 1usize << MAX_LOG_N {
        return Err(Error::Device(format!("ntt: {n} elements")));
    }
    Ok(())
}

/// `MASKS[m] = 2^m - 1`: kernel arguments that live as long as any command.
static MASKS: [u32; 32] = {
    let mut m = [0u32; 32];
    let mut i = 0;
    while i < 32 {
        m[i] = ((1u64 << i) - 1) as u32;
        i += 1;
    }
    m
};

/// Encodes `a[i] *= [1, zeta[0], zeta[1]][i mod 3]` for `i < n`. `zeta` must be
/// reduced.
pub(crate) fn encode_distribute_zeta<'a>(
    cmd: &mut Command<'a>,
    a: &'a Buffer,
    n: usize,
    zeta: &'a [Scalar; 2],
) -> Result<(), Error> {
    elementwise_len(a, n)?;
    if !zeta.iter().all(field::is_reduced) {
        return Err(Error::Unreduced("distribute_zeta: zeta".into()));
    }
    cmd.dispatch(
        "ntt_distribute_zeta",
        n,
        &[Arg::Buffer(a), Arg::value(&zeta[0]), Arg::value(&zeta[1])],
    )
}

/// Encodes `a[i] *= c` for `i < n`. `c` must be reduced.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn encode_scale<'a>(
    cmd: &mut Command<'a>,
    a: &'a Buffer,
    n: usize,
    c: &'a Scalar,
) -> Result<(), Error> {
    elementwise_len(a, n)?;
    if !field::is_reduced(c) {
        return Err(Error::Unreduced("scale: the factor".into()));
    }
    cmd.dispatch("ntt_scale", n, &[Arg::Buffer(a), Arg::value(c)])
}

/// Encodes `a[i] *= t[i mod 2^log_tn]` for `i < n`, as
/// `divide_by_vanishing_poly` does with its power-of-two table.
pub(crate) fn encode_mul_periodic<'a>(
    cmd: &mut Command<'a>,
    a: &'a Buffer,
    n: usize,
    t: &'a Buffer,
    log_tn: u32,
) -> Result<(), Error> {
    elementwise_len(a, n)?;
    if log_tn > MAX_LOG_N {
        return Err(Error::Device(format!("mul_periodic: table of 2^{log_tn}")));
    }
    check_len(t, 1usize << log_tn, "table")?;
    cmd.dispatch(
        "ntt_mul_periodic",
        n,
        &[
            Arg::Buffer(a),
            Arg::Buffer(t),
            Arg::value(&MASKS[log_tn as usize]),
        ],
    )
}

// ---------------------------------------------------------------------------
// Host transforms

/// The transform of a host slice through per-request buffers taken without
/// the device ([`ctx::take_request_buffer`]), so the host copies of calls on
/// several threads overlap each other's device work. `a` is written only after
/// every command buffer completed. Returns the GPU time.
fn transform_host(
    class: Class,
    a: &mut [Scalar],
    log_n: u32,
    dir: Dir,
    scale: Option<&Scalar>,
) -> Result<u64, Error> {
    let ctx = ctx::context()?;
    let bytes = std::mem::size_of_val(a);
    let mut data = ctx::take_request_buffer("ntt-data", bytes)?;
    ctx::par_copy(&mut data.buf_mut().as_mut_slice::<Scalar>()[..a.len()], a);
    let tmp = if scratch_bytes(log_n) > 0 {
        Some(ctx::take_request_buffer("ntt-scratch", bytes)?)
    } else {
        None
    };
    // the test panic fires with the request buffers filled and `a` unchanged
    crate::test_switch::hook_panic(class);
    let ns = {
        let _device = ctx::lock()?;
        let d = data.buf();
        ntt_dev(
            ctx,
            d,
            tmp.as_ref().map_or(d, |t| t.buf()),
            log_n,
            dir,
            scale,
        )?
    };
    ctx::par_copy(a, &data.buf().as_slice::<Scalar>()[..a.len()]);
    data.give_back();
    if let Some(t) = tmp {
        t.give_back();
    }
    Ok(ns)
}

/// Accounts the end of a hook call: served with its GPU time, or declined
/// with the reason of the error.
fn finish(class: Class, r: Result<u64, Error>) -> bool {
    match r {
        Ok(ns) => {
            account::served(class, ns);
            true
        }
        Err(e) => account::decline(class, Reason::of(&e)),
    }
}

/// The FFT of `a` at `omega`, natural order, in place. `false`: declined, `a`
/// unchanged.
pub(crate) fn fft(a: &mut [Scalar], omega: Scalar, log_n: u32) -> bool {
    let Some(dir) = direction(&omega, log_n) else {
        return account::decline(Class::Fft, Reason::Shape);
    };
    finish(Class::Fft, transform_host(Class::Fft, a, log_n, dir, None))
}

/// The FFT of `a` at `omega_inv`, then each element times `divisor`, in
/// place. `false`: declined, `a` unchanged.
pub(crate) fn ifft(a: &mut [Scalar], omega_inv: Scalar, log_n: u32, divisor: Scalar) -> bool {
    let Some(dir) = direction(&omega_inv, log_n) else {
        return account::decline(Class::Ifft, Reason::Shape);
    };
    finish(
        Class::Ifft,
        transform_host(Class::Ifft, a, log_n, dir, Some(&divisor)),
    )
}

// ---------------------------------------------------------------------------
// Test support

/// Host-to-host wrappers of the device building blocks (not a stable
/// interface).
#[cfg(any(test, feature = "test-support"))]
pub mod test_support {
    use super::*;

    /// Runs `f` holding the device.
    fn on_device<R>(f: impl FnOnce(&Ctx) -> Result<R, Error>) -> Result<R, String> {
        let s = ctx::lock().map_err(|e| e.to_string())?;
        f(s.ctx()).map_err(|e| e.to_string())
    }

    /// The scratch of a `2^log_n` transform.
    fn scratch(ctx: &Ctx, log_n: u32) -> Result<Buffer, Error> {
        ctx.alloc(scratch_bytes(log_n))
    }

    /// `coeff_to_extended` through [`coeff_to_extended_dev_at`]: `coeffs` has
    /// `2^k` elements; the result `2^ext_k`.
    pub fn coeff_to_extended(
        coeffs: &[Scalar],
        k: u32,
        ext_k: u32,
        zeta: [Scalar; 2],
    ) -> Result<Vec<Scalar>, String> {
        if coeffs.len() != 1usize << k {
            return Err("length".into());
        }
        on_device(|ctx| {
            let src = ctx.upload(coeffs)?;
            let dst = ctx.alloc(SCALAR_BYTES << ext_k)?;
            let tmp = scratch(ctx, ext_k)?;
            coeff_to_extended_dev_at(ctx, &src, &dst, 0, &tmp, k, ext_k, &zeta)?;
            Ok(dst.as_slice::<Scalar>()[..1usize << ext_k].to_vec())
        })
    }

    /// `extended_to_coeff` through [`extended_to_coeff_dev`] (the whole
    /// `2^ext_k` result, before any truncation).
    pub fn extended_to_coeff(
        values: &[Scalar],
        ext_k: u32,
        divisor: Scalar,
        zeta_out: [Scalar; 2],
    ) -> Result<Vec<Scalar>, String> {
        if values.len() != 1usize << ext_k {
            return Err("length".into());
        }
        on_device(|ctx| {
            let a = ctx.upload(values)?;
            let tmp = scratch(ctx, ext_k)?;
            extended_to_coeff_dev(ctx, &a, &tmp, ext_k, &divisor, &zeta_out)?;
            Ok(a.as_slice::<Scalar>()[..values.len()].to_vec())
        })
    }

    /// [`ntt_dev`] on a copy of `values` (`inverse`: at `w^-1`).
    pub fn ntt(
        values: &[Scalar],
        log_n: u32,
        inverse: bool,
        scale: Option<Scalar>,
    ) -> Result<Vec<Scalar>, String> {
        let dir = if inverse { Dir::Inverse } else { Dir::Forward };
        on_device(|ctx| {
            let a = ctx.upload(values)?;
            let tmp = scratch(ctx, log_n)?;
            ntt_dev(ctx, &a, &tmp, log_n, dir, scale.as_ref())?;
            Ok(a.as_slice::<Scalar>()[..values.len()].to_vec())
        })
    }

    /// The elementwise blocks on a copy of `values` in one command buffer:
    /// distribute by `zeta`, scale by `c`, multiply by `table` periodically.
    pub fn elementwise(
        values: &[Scalar],
        zeta: [Scalar; 2],
        c: Scalar,
        table: &[Scalar],
    ) -> Result<Vec<Scalar>, String> {
        if !table.len().is_power_of_two() {
            return Err("table length".into());
        }
        on_device(|ctx| {
            let a = ctx.upload(values)?;
            let t = ctx.upload(table)?;
            let n = values.len();
            ctx.run(|cmd| {
                encode_distribute_zeta(cmd, &a, n, &zeta)?;
                encode_scale(cmd, &a, n, &c)?;
                encode_mul_periodic(cmd, &a, n, &t, table.len().ilog2())
            })?;
            Ok(a.as_slice::<Scalar>()[..n].to_vec())
        })
    }

    /// The standard `2^log_n`-th root of unity (or its inverse) as this
    /// module derives it.
    pub fn root(log_n: u32, inverse: bool) -> Option<Scalar> {
        std_root(log_n, if inverse { Dir::Inverse } else { Dir::Forward })
    }

    /// The radices (log2) of the passes of a `2^log_n` transform.
    pub fn passes(log_n: u32) -> Vec<u32> {
        plan(log_n)
    }
}

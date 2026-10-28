//! A Pippenger multi-scalar multiplication over tiles of windows × chunks of
//! the terms (blst's design), with batched affine buckets (gnark's) from window
//! 7 and XYZZ buckets below.
//!
//! This is the MSM behind polynomial commitments; see [`msm_pippenger`].

use std::ops::{Neg, Range};

use ff::{Field, PrimeField};
use group::Group;
use rayon::{
    iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator, repeat_n},
    slice::ParallelSlice,
};

use crate::{CurveAffine, FieldInto};

/// The Booth digit of window `window_index` (of `window_size` bits) of the
/// little-endian scalar `el`: in `-2^(window_size-1)..=2^(window_size-1)`.
#[inline]
fn get_booth_index(window_index: usize, window_size: usize, el: &[u8]) -> i32 {
    // Booth encoding:
    // * step by `window` size.
    // * slice by size of `window + 1`.
    // * each window overlaps by 1 bit.
    // * append a zero bit to the least significant end.
    // Indexing rule for example window size 3 where we slice by 4 bits:
    // `[0, +1, +1, +2, +2, +3, +3, +4, -4, -3, -3 -2, -2, -1, -1, 0]`.
    // So we can reduce the bucket size without preprocessing scalars
    // and remembering them as in classic signed digit encoding.

    let skip_bits = (window_index * window_size).saturating_sub(1);
    let skip_bytes = skip_bits / 8;

    // Fill into a u32.
    let mut v: [u8; 4] = [0; 4];
    match el.get(skip_bytes..skip_bytes + 4) {
        // One load, rather than a byte copy loop (a `memmove` call on aarch64).
        Some(bytes) => v.copy_from_slice(bytes),
        None => {
            for (dst, src) in v.iter_mut().zip(el.iter().skip(skip_bytes)) {
                *dst = *src
            }
        }
    }
    let mut tmp = u32::from_le_bytes(v);

    // Pad with one 0 if slicing the least significant window.
    if window_index == 0 {
        tmp <<= 1;
    }

    // Remove further bits.
    tmp >>= skip_bits - (skip_bytes * 8);
    // Apply the Booth window.
    tmp &= (1 << (window_size + 1)) - 1;

    let sign = tmp & (1 << window_size) == 0;

    // Div ceil by 2.
    tmp = (tmp + 1) >> 1;

    // Find the Booth action index.
    if sign {
        tmp as i32
    } else {
        ((!(tmp - 1) & ((1 << window_size) - 1)) as i32).neg()
    }
}

/// The affine coordinates of a base, copied out of it (for curves without
/// [`CurveAffine::xy_ref`]).
#[derive(Debug, Clone, Copy)]
struct Affine<F> {
    x: F,
    y: F,
}

impl<F: Field> Affine<F> {
    /// The coordinates, or zeros for the identity (whose scalar the MSM then
    /// zeroes, so they are never read).
    fn from<C: CurveAffine<Base = F>>(point: &C) -> Self {
        match Option::<crate::Coordinates<C>>::from(point.coordinates()) {
            Some(c) => Self {
                x: *c.x(),
                y: *c.y(),
            },
            None => Self {
                x: F::ZERO,
                y: F::ZERO,
            },
        }
    }
}

/// A point in XYZZ coordinates, `(x, y) = (X/ZZ, Y/ZZZ)` with `ZZ^3 = ZZZ^2`;
/// the identity has `ZZ = ZZZ = 0`. Adding an affine point costs 8M + 2S and no
/// inversion, which makes these good Pippenger buckets (as in blst). The
/// formulas assume `a = 0`.
#[derive(Clone, Copy, Debug)]
struct Xyzz<F> {
    x: F,
    y: F,
    zz: F,
    zzz: F,
}

impl<F: FieldInto> Xyzz<F> {
    fn identity() -> Self {
        Self {
            x: F::ZERO,
            y: F::ZERO,
            zz: F::ZERO,
            zzz: F::ZERO,
        }
    }

    fn from_affine(x: &F, y: &F) -> Self {
        Self {
            x: *x,
            y: *y,
            zz: F::ONE,
            zzz: F::ONE,
        }
    }

    // Variable time: which buckets are touched depends on the scalars anyway.
    fn is_identity(&self) -> bool {
        self.zz.is_zero_vartime() && self.zzz.is_zero_vartime()
    }

    /// `self += (x2, y2)`, or `-=` if `negate`, for an affine point `(x2, y2)`
    /// on the curve (EFD madd-2008-s; [`Self::double`] when the points are
    /// equal). Like blst, every result is written where it is needed
    /// ([`FieldInto`]), never copied while fresh.
    fn add_affine(&mut self, x2: &F, y2: &F, negate: bool) {
        let mut neg_y2 = F::ZERO;
        let y2 = if negate {
            F::neg_into(&mut neg_y2, y2);
            &neg_y2
        } else {
            y2
        };
        if self.is_identity() {
            *self = Self::from_affine(x2, y2);
            return;
        }
        // P = x2·ZZ1 - X1, R = y2·ZZZ1 - Y1.
        let mut p = F::ZERO;
        F::mul_into(&mut p, x2, &self.zz);
        p -= &self.x;
        let mut r = F::ZERO;
        F::mul_into(&mut r, y2, &self.zzz);
        r -= &self.y;
        if !p.is_zero_vartime() {
            let mut pp = F::ZERO;
            F::square_into(&mut pp, &p);
            let mut ppp = F::ZERO;
            F::mul_into(&mut ppp, &pp, &p);
            let mut q = F::ZERO;
            F::mul_into(&mut q, &self.x, &pp);
            // X3 = R^2 - PPP - 2Q.
            F::square_into(&mut self.x, &r);
            self.x -= &ppp;
            self.x -= &q;
            self.x -= &q;
            // Y3 = R·(Q - X3) - Y1·PPP.
            q -= &self.x;
            q *= &r;
            self.y *= &ppp;
            F::rsub_assign(&mut self.y, &q);
            self.zz *= &pp;
            self.zzz *= &ppp;
        } else if r.is_zero_vartime() {
            // Equal points (rare).
            *self = Self::from_affine(x2, y2);
            self.double();
        } else {
            *self = Self::identity();
        }
    }

    /// `self += other` (EFD add-2008-s, and dbl-2008-s-1 when the points are
    /// equal).
    fn add(&mut self, other: &Self) {
        if other.is_identity() {
            return;
        }
        if self.is_identity() {
            *self = *other;
            return;
        }
        let mut u1 = F::ZERO;
        F::mul_into(&mut u1, &self.x, &other.zz);
        let mut s1 = F::ZERO;
        F::mul_into(&mut s1, &self.y, &other.zzz);
        let mut p = F::ZERO;
        F::mul_into(&mut p, &other.x, &self.zz);
        p -= &u1;
        let mut r = F::ZERO;
        F::mul_into(&mut r, &other.y, &self.zzz);
        r -= &s1;
        if !p.is_zero_vartime() {
            let mut pp = F::ZERO;
            F::square_into(&mut pp, &p);
            let mut ppp = F::ZERO;
            F::mul_into(&mut ppp, &pp, &p);
            let mut q = F::ZERO;
            F::mul_into(&mut q, &u1, &pp);
            F::square_into(&mut self.x, &r);
            self.x -= &ppp;
            self.x -= &q;
            self.x -= &q;
            q -= &self.x;
            q *= &r;
            s1 *= &ppp;
            F::sub_into(&mut self.y, &q, &s1);
            self.zz *= &other.zz;
            self.zz *= &pp;
            self.zzz *= &other.zzz;
            self.zzz *= &ppp;
        } else if r.is_zero_vartime() {
            self.double();
        } else {
            *self = Self::identity();
        }
    }

    /// `2·self` (EFD dbl-2008-s-1, `a = 0`); `2·O = O`.
    fn double(&mut self) {
        if self.is_identity() {
            return;
        }
        let mut u = F::ZERO;
        F::add_into(&mut u, &self.y, &self.y);
        let mut v = F::ZERO;
        F::square_into(&mut v, &u);
        let mut w = F::ZERO;
        F::mul_into(&mut w, &v, &u);
        let mut s = F::ZERO;
        F::mul_into(&mut s, &self.x, &v);
        let mut xsq = F::ZERO;
        F::square_into(&mut xsq, &self.x);
        let mut m = F::ZERO;
        F::add_into(&mut m, &xsq, &xsq);
        m += &xsq;
        F::square_into(&mut self.x, &m);
        self.x -= &s;
        self.x -= &s;
        s -= &self.x;
        s *= &m;
        self.y *= &w;
        F::rsub_assign(&mut self.y, &s);
        self.zz *= &v;
        self.zzz *= &w;
    }

    /// The point in the curve's own representation. It is a sum of points of
    /// the prime-order subgroup, so the subgroup check is skipped
    /// ([`CurveAffine::from_xy_unchecked`]).
    fn to_curve<C: CurveAffine<Base = F>>(&self) -> C::Curve {
        if self.is_identity() {
            return C::Curve::identity();
        }
        let zzz_inv = self.zzz.invert().expect("ZZZ is non-zero off the identity");
        // ZZ^3 = ZZZ^2, so 1/ZZ = ZZ^2/ZZZ^2.
        let zz_inv = zzz_inv.square() * self.zz.square();
        C::from_xy_unchecked(self.x * zz_inv, self.y * zzz_inv).to_curve()
    }
}

/// The Pippenger's window size for `n` terms, measured on BLS12-381 G1 by
/// sweeping it: x86-64 on a Ryzen 5950X (32 threads), aarch64 on an Apple M3
/// Max (12 performance and 4 efficiency cores), which wants wider windows.
fn window_size(n: usize) -> usize {
    let k = n.max(1).ilog2();
    if cfg!(target_arch = "aarch64") {
        match k {
            0..=7 => 5,
            8..=9 => 7,
            10 => 8,
            11..=14 => 10,
            15..=16 => 12,
            _ => 13,
        }
    } else {
        match k {
            0..=6 => 5,
            7 => 4,
            8 => 7,
            9 => 8,
            10..=12 => 9,
            13 => 10,
            14 => 11,
            15..=16 => 12,
            _ => 13,
        }
    }
}

/// The point-chunk count for window size `c`: the least cost, as parallel
/// rounds times one tile's work (its bucket additions, then summing its
/// buckets). Chunks of the terms give more tiles when there are fewer windows
/// than threads, as in blst's `breakdown`.
fn chunk_count(n: usize, nbits: usize, c: usize, threads: usize) -> usize {
    let windows = nbits / c + 1;
    let mut best = (usize::MAX, 1);
    for chunks in 1..=threads.max(1) {
        let per_chunk = n.div_ceil(chunks);
        if chunks > 1 && per_chunk < 64 {
            break;
        }
        let rounds = (windows * chunks).div_ceil(threads.max(1));
        let cost = rounds * (per_chunk + (1 << c)) + windows * chunks;
        if cost < best.0 {
            best = (cost, chunks);
        }
    }
    best.1
}

/// `Σ (i + 1)·buckets[i]` by running sums, emptying the buckets for reuse.
fn integrate_and_clear<F: FieldInto>(buckets: &mut [Xyzz<F>]) -> Xyzz<F> {
    let mut acc = Xyzz::identity();
    let mut sum = Xyzz::identity();
    for b in buckets.iter_mut().rev() {
        acc.add(b);
        sum.add(&acc);
        *b = Xyzz::identity();
    }
    sum
}

/// Pippenger buckets in affine form, added to in batches: one inversion serves
/// a whole batch of slopes (Montgomery's trick), so an addition costs 5M + 1S
/// and a share of the inversion, against 8M + 2S into an XYZZ bucket (as in
/// gnark). A point whose bucket is already in the batch waits for the next one;
/// past a batch's worth of those, or if it would double or cancel its bucket,
/// it goes to an XYZZ bucket beside it.
struct AffineBuckets<F> {
    buckets: Vec<AffineBucket<F>>,
    side: Vec<Xyzz<F>>,
    /// Whether any `side` bucket is in use.
    sides: bool,
    /// Awaiting the next batch, with their `x` differences and the running
    /// products of those.
    batch: Vec<Pending>,
    dx: Vec<F>,
    prefix: Vec<F>,
    /// Waiting for their bucket to leave the batch (and `spare`, its double
    /// buffer).
    waiting: Vec<Pending>,
    spare: Vec<Pending>,
    /// Running sums for the lanes of [`Self::integrate_lanes`].
    acc: Vec<AffineBucket<F>>,
    sum: Vec<AffineBucket<F>>,
}

/// An affine bucket (or running sum): its point when `full`; `queued` while it
/// has an addition in the batch.
#[derive(Clone, Copy)]
struct AffineBucket<F> {
    x: F,
    y: F,
    full: bool,
    queued: bool,
}

/// `buckets[bucket] += ±points[point]`, batched; `same_x` if the point shares
/// the bucket's `x`, so the addition doubles or cancels it (no slope: added in
/// XYZZ instead).
#[derive(Clone, Copy)]
struct Pending {
    bucket: usize,
    point: usize,
    negate: bool,
    same_x: bool,
}

/// At most this many lanes of running sums when summing the buckets (an eighth
/// of them is best, measured on BLS12-381 G1, single core).
const LANES: usize = 128;

impl<F: FieldInto> AffineBuckets<F> {
    fn new(buckets: usize, batch: usize) -> Self {
        let empty = AffineBucket {
            x: F::ZERO,
            y: F::ZERO,
            full: false,
            queued: false,
        };
        let lanes = LANES.min(batch);
        Self {
            buckets: vec![empty; buckets],
            side: vec![Xyzz::identity(); buckets],
            sides: false,
            batch: Vec::with_capacity(batch),
            dx: vec![F::ZERO; batch],
            prefix: vec![F::ZERO; batch],
            waiting: Vec::with_capacity(batch),
            spare: Vec::with_capacity(batch),
            acc: vec![empty; lanes],
            sum: vec![empty; lanes],
        }
    }

    /// `buckets[b] += ±xy(i)`, now or in a later batch.
    fn add<'a>(&mut self, b: usize, i: usize, negate: bool, xy: &impl Fn(usize) -> (&'a F, &'a F))
    where
        F: 'a,
    {
        let p = Pending {
            bucket: b,
            point: i,
            negate,
            same_x: false,
        };
        self.enqueue(p, xy);
        if self.batch.len() == self.dx.len() {
            self.flush(xy);
        }
    }

    fn enqueue<'a>(&mut self, p: Pending, xy: &impl Fn(usize) -> (&'a F, &'a F))
    where
        F: 'a,
    {
        let bucket = &mut self.buckets[p.bucket];
        if !bucket.full {
            let (x, y) = xy(p.point);
            bucket.x = *x;
            if p.negate {
                F::neg_into(&mut bucket.y, y);
            } else {
                bucket.y = *y;
            }
            bucket.full = true;
        } else if !bucket.queued {
            bucket.queued = true;
            self.batch.push(p);
        } else if self.waiting.len() < self.dx.len() {
            self.waiting.push(p);
        } else {
            let (x, y) = xy(p.point);
            self.side[p.bucket].add_affine(x, y, p.negate);
            self.sides = true;
        }
    }

    /// Adds the batch, then queues the waiting points whose buckets it freed,
    /// again while they fill a batch.
    fn flush<'a>(&mut self, xy: &impl Fn(usize) -> (&'a F, &'a F))
    where
        F: 'a,
    {
        loop {
            self.add_batch(xy);
            std::mem::swap(&mut self.waiting, &mut self.spare);
            for k in 0..self.spare.len() {
                let p = self.spare[k];
                self.enqueue(p, xy);
            }
            self.spare.clear();
            if self.batch.len() < self.dx.len() {
                return;
            }
        }
    }

    /// Adds the batch ([`add_with_inverse`]), one inversion for all.
    fn add_batch<'a>(&mut self, xy: &impl Fn(usize) -> (&'a F, &'a F))
    where
        F: 'a,
    {
        let len = self.batch.len();
        for (p, dx) in self.batch.iter_mut().zip(&mut self.dx) {
            F::sub_into(dx, xy(p.point).0, &self.buckets[p.bucket].x);
            // Doubles or cancels: added apart from the batch, below.
            p.same_x = dx.is_zero_vartime();
            if p.same_x {
                *dx = F::ONE;
            }
        }
        invert_all(&mut self.dx[..len], &mut self.prefix);
        for (p, inv) in self.batch.iter().zip(&self.dx) {
            let bucket = &mut self.buckets[p.bucket];
            bucket.queued = false;
            let (x, y) = xy(p.point);
            if p.same_x {
                self.side[p.bucket].add_affine(x, y, p.negate);
                self.sides = true;
            } else {
                add_with_inverse(&mut bucket.x, &mut bucket.y, x, y, p.negate, inv);
            }
        }
        self.batch.clear();
    }

    /// `Σ (b + 1)·buckets[b]` over the first `used` buckets, emptying them for
    /// reuse.
    fn integrate_and_clear<'a>(
        &mut self,
        used: usize,
        xy: &impl Fn(usize) -> (&'a F, &'a F),
    ) -> Xyzz<F>
    where
        F: 'a,
    {
        // A few more batches for the waiting points, then the XYZZ buckets for the
        // rest.
        for _ in 0..4 {
            if self.batch.is_empty() && self.waiting.is_empty() {
                break;
            }
            self.flush(xy);
        }
        for k in 0..self.batch.len() {
            let p = self.batch[k];
            self.buckets[p.bucket].queued = false;
            self.waiting.push(p);
        }
        self.batch.clear();
        for p in self.waiting.drain(..) {
            let (x, y) = xy(p.point);
            self.side[p.bucket].add_affine(x, y, p.negate);
            self.sides = true;
        }
        let lanes = (used / 8).clamp(32, self.acc.len());
        if !self.sides
            && used >= 4 * lanes
            && let Some(sum) = self.integrate_lanes(used, lanes)
        {
            self.buckets[..used].iter_mut().for_each(|b| b.full = false);
            return sum;
        }
        let mut acc = Xyzz::identity();
        let mut sum = Xyzz::identity();
        for (bucket, side) in self.buckets[..used].iter_mut().zip(&mut self.side[..used]).rev() {
            if bucket.full {
                acc.add_affine(&bucket.x, &bucket.y, false);
                bucket.full = false;
            }
            if !side.is_identity() {
                acc.add(side);
                *side = Xyzz::identity();
            }
            sum.add(&acc);
        }
        self.sides = false;
        sum
    }

    /// `Σ (b + 1)·buckets[b]` by running sums over `lanes` contiguous segments
    /// of the buckets at once, each step's additions sharing one inversion;
    /// the segments' sums then combine as `Σ_l (sum_l + l·seg·acc_l)`.
    /// Nothing if an addition would double or cancel (the caller then sums
    /// in XYZZ).
    fn integrate_lanes(&mut self, used: usize, lanes: usize) -> Option<Xyzz<F>> {
        let seg = used / lanes;
        debug_assert!(used.is_power_of_two() && lanes.is_power_of_two() && seg >= 1);
        for s in self.acc[..lanes].iter_mut().chain(&mut self.sum[..lanes]) {
            (s.full, s.queued) = (false, false);
        }
        for j in (0..seg).rev() {
            let (acc, sum) = (&mut self.acc[..lanes], &mut self.sum[..lanes]);
            let buckets = &self.buckets;
            if !add_lanes(
                acc,
                |l| &buckets[l * seg + j],
                &mut self.dx,
                &mut self.prefix,
            ) || !add_lanes(sum, |l| &acc[l], &mut self.dx, &mut self.prefix)
            {
                return None;
            }
        }
        // Σ_l l·acc_l by running sums over the lanes, times `seg`, plus Σ_l sum_l.
        let (mut run, mut total, mut sums) = (Xyzz::identity(), Xyzz::identity(), Xyzz::identity());
        for l in (0..lanes).rev() {
            total.add(&run);
            if self.acc[l].full {
                run.add_affine(&self.acc[l].x, &self.acc[l].y, false);
            }
            if self.sum[l].full {
                sums.add_affine(&self.sum[l].x, &self.sum[l].y, false);
            }
        }
        for _ in 0..seg.ilog2() {
            total.double();
        }
        total.add(&sums);
        Some(total)
    }
}

/// `dst[l] += src(l)` in every lane, the additions sharing one inversion; false
/// if one would double or cancel (`dst` is then partly updated).
fn add_lanes<'a, F: FieldInto + 'a>(
    dst: &mut [AffineBucket<F>],
    src: impl Fn(usize) -> &'a AffineBucket<F>,
    dx: &mut [F],
    prefix: &mut [F],
) -> bool {
    // Lanes with both points: their x differences.
    let mut m = 0;
    for (l, d) in dst.iter_mut().enumerate() {
        let s = src(l);
        if !s.full {
            continue;
        }
        if !d.full {
            *d = *s;
            continue;
        }
        F::sub_into(&mut dx[m], &s.x, &d.x);
        if dx[m].is_zero_vartime() {
            return false;
        }
        d.queued = true;
        m += 1;
    }
    invert_all(&mut dx[..m], prefix);
    let queued = dst.iter_mut().enumerate().filter(|(_, d)| d.queued);
    for ((l, d), inv) in queued.zip(dx.iter()) {
        let s = src(l);
        d.queued = false;
        add_with_inverse(&mut d.x, &mut d.y, &s.x, &s.y, false, inv);
    }
    true
}

/// Montgomery's trick: `values` (all non-zero) become their inverses, for one
/// inversion and 3M each; `scratch` (at least as long) holds the running
/// products.
fn invert_all<F: FieldInto>(values: &mut [F], scratch: &mut [F]) {
    let Some(last) = values.len().checked_sub(1) else {
        return;
    };
    scratch[0] = values[0];
    for j in 1..values.len() {
        let (done, rest) = scratch.split_at_mut(j);
        F::mul_into(&mut rest[0], &done[j - 1], &values[j]);
    }
    let mut inv = scratch[last].invert().expect("a product of non-zero values is invertible");
    for j in (1..values.len()).rev() {
        // 1/v_j = (v_0···v_j)^-1 · (v_0···v_{j-1}).
        let (done, rest) = scratch.split_at_mut(j);
        F::mul_into(&mut rest[0], &inv, &done[j - 1]);
        inv *= &values[j];
        values[j] = rest[0];
    }
    values[0] = inv;
}

/// `(x1, y1) += (x2, ±y2)` (`-y2` if `negate`), given `inv = 1/(x2 - x1)`:
/// `λ = (y2 - y1)·inv`, `x' = λ² - x1 - x2`, `y' = λ(x1 - x') - y1`. Adding
/// `-P`, the slope is `-λ'` for `λ' = (y2 + y1)·inv`, and then `y' = λ'(x' -
/// x1) - y1`: no negation needed.
#[inline]
fn add_with_inverse<F: FieldInto>(x1: &mut F, y1: &mut F, x2: &F, y2: &F, negate: bool, inv: &F) {
    let (mut lambda, mut t, mut d) = (F::ZERO, F::ZERO, F::ZERO);
    if negate {
        F::add_into(&mut t, y2, y1);
    } else {
        F::sub_into(&mut t, y2, y1);
    }
    F::mul_into(&mut lambda, &t, inv);
    F::square_into(&mut t, &lambda);
    t -= &*x1;
    t -= x2;
    if negate {
        F::sub_into(&mut d, &t, x1);
    } else {
        F::sub_into(&mut d, x1, &t);
    }
    *x1 = t;
    F::mul_into(&mut t, &lambda, &d);
    F::rsub_assign(y1, &t);
}

/// Scalars converted together by [`pippenger`]'s tiles.
const SCALAR_BLOCK: usize = 256;

/// The Pippenger over `n` affine points `xy(i)` (none the identity) and
/// little-endian scalars of `nbits` bits, `repr(range)` giving those in
/// `range`.
///
/// The scalars are converted lazily, a block at a time, by whichever tile first
/// needs a block, so the conversion runs in parallel with no fork-join of its
/// own. Each tile visits its blocks starting at its own offset, so the first
/// tiles, which start together, convert different blocks rather than queue on
/// one.
fn pippenger<'a, C: CurveAffine, S: AsRef<[u8]> + Send + Sync, R, XY>(
    n: usize,
    repr: R,
    xy: XY,
    nbits: usize,
    c: usize,
) -> C::Curve
where
    R: Fn(Range<usize>) -> Vec<S> + Sync,
    XY: Fn(usize) -> (&'a C::Base, &'a C::Base) + Sync,
{
    use std::sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
        mpsc,
    };

    let windows = nbits / c + 1;
    let threads = rayon::current_num_threads();
    let chunks = chunk_count(n, nbits, c, threads);
    // Whole blocks per chunk.
    let chunk = n.div_ceil(chunks).next_multiple_of(SCALAR_BLOCK);
    let blocks: Vec<OnceLock<Vec<S>>> =
        (0..n.div_ceil(SCALAR_BLOCK)).map(|_| OnceLock::new()).collect();
    let tiles = windows * chunks;
    // Tile `t` is chunk `t % chunks` of window `windows - 1 - t / chunks`: the most
    // significant windows first, so the combination below can start while the rest
    // run.
    let results: Vec<OnceLock<Xyzz<C::Base>>> = (0..tiles).map(|_| OnceLock::new()).collect();
    let pending: Vec<AtomicUsize> = (0..windows).map(|_| AtomicUsize::new(chunks)).collect();
    let next = AtomicUsize::new(0);
    let (done_tx, done_rx) = mpsc::channel::<usize>();
    let mut acc = Xyzz::identity();
    // Batched affine buckets from 64 buckets up; the batch is a quarter of the
    // buckets, so few points find theirs already in it (measured on BLS12-381
    // G1, single core).
    let buckets = 1 << (c - 1);
    let batch = (c >= 7).then(|| (buckets / 4).clamp(64, 256).min(buckets));
    rayon::in_place_scope(|scope| {
        for _ in 0..threads.min(tiles) {
            let done_tx = done_tx.clone();
            let (results, pending, next, xy) = (&results, &pending, &next, &xy);
            let (blocks, repr) = (&blocks, &repr);
            scope.spawn(move |_| {
                let mut affine = batch.map(|batch| AffineBuckets::new(buckets, batch));
                let mut buckets =
                    vec![Xyzz::identity(); if affine.is_some() { 0 } else { buckets }];
                loop {
                    let t = next.fetch_add(1, Ordering::Relaxed);
                    if t >= tiles {
                        break;
                    }
                    let (w, k) = (windows - 1 - t / chunks, t % chunks);
                    let start = (k * chunk).min(n);
                    let end = ((k + 1) * chunk).min(n);
                    // The top window holds the last `nbits - w·c` bits, so its digits reach
                    // only 2^that: integrate just those buckets (as blst does).
                    let used = 1 << (nbits - w * c).min(c - 1);
                    // `start` is a block boundary, or `n` for a chunk past the end.
                    let (b0, b1) = (start.div_ceil(SCALAR_BLOCK), end.div_ceil(SCALAR_BLOCK));
                    for j in 0..b1 - b0 {
                        let b = b0 + (j + t) % (b1 - b0);
                        let first = b * SCALAR_BLOCK;
                        let block =
                            blocks[b].get_or_init(|| repr(first..(first + SCALAR_BLOCK).min(n)));
                        for (i, s) in block.iter().enumerate().map(|(i, s)| (first + i, s)) {
                            let d = get_booth_index(w, c, s.as_ref());
                            debug_assert!(d.unsigned_abs() as usize <= used);
                            if d != 0 {
                                let b = d.unsigned_abs() as usize - 1;
                                if let Some(a) = &mut affine {
                                    a.add(b, i, d < 0, xy);
                                } else {
                                    let (x, y) = xy(i);
                                    buckets[b].add_affine(x, y, d < 0);
                                }
                            }
                        }
                    }
                    let sum = match &mut affine {
                        Some(a) => a.integrate_and_clear(used, xy),
                        None => integrate_and_clear(&mut buckets[..used]),
                    };
                    let _ = results[t].set(sum);
                    if pending[w].fetch_sub(1, Ordering::AcqRel) == 1 {
                        // The receiver outlives the scope.
                        let _ = done_tx.send(w);
                    }
                }
            });
        }
        drop(done_tx);
        // Horner's rule as the windows complete, most significant first.
        let mut ready = vec![false; windows];
        let mut w_next = windows;
        while w_next > 0 {
            let w = match done_rx.try_recv() {
                Ok(w) => w,
                Err(mpsc::TryRecvError::Empty) => {
                    // Help with the tiles, or wait if this thread is not in the pool.
                    if rayon::yield_now().is_none() {
                        match done_rx.recv() {
                            Ok(w) => w,
                            Err(_) => break,
                        }
                    } else {
                        continue;
                    }
                }
                Err(mpsc::TryRecvError::Disconnected) => break,
            };
            ready[w] = true;
            while w_next > 0 && ready[w_next - 1] {
                w_next -= 1;
                if w_next + 1 < windows {
                    (0..c).for_each(|_| acc.double());
                }
                for k in 0..chunks {
                    let tile = &results[(windows - 1 - w_next) * chunks + k];
                    acc.add(tile.get().expect("a window is ready once all its tiles are set"));
                }
            }
        }
    });
    acc.to_curve::<C>()
}

/// [`msm_pippenger`] with window size `c`.
fn msm_with_window<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C], c: usize) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    let nbits = C::Scalar::NUM_BITS as usize;
    // Scalars converted by the tiles as they need them; an identity base gets a
    // zero scalar, so it is never added (nor its coordinates read).
    let zero = C::Scalar::ZERO.to_repr();
    let repr = |r: Range<usize>| -> Vec<_> {
        let repr = |i: usize| match bool::from(bases[i].is_identity()) {
            true => zero,
            false => coeffs[i].to_repr(),
        };
        r.map(repr).collect()
    };
    if bases.first().is_some_and(|b| b.xy_ref().is_some()) {
        // Coordinates read in place.
        let xy = |i: usize| {
            bases[i]
                .xy_ref()
                .expect("`xy_ref` is all or nothing for a type: the first base has it")
        };
        return pippenger::<C, _, _, _>(coeffs.len(), repr, xy, nbits, c);
    }
    let points: Vec<Affine<C::Base>> = bases.par_iter().map(Affine::from).collect();
    let xy = |i: usize| (&points[i].x, &points[i].y);
    pippenger::<C, _, _, _>(coeffs.len(), repr, xy, nbits, c)
}

/// From this many terms, [`compact`] counts and copies in parallel, in chunks
/// of [`COMPACT_CHUNK`] terms.
const PARALLEL_COMPACT: usize = 1 << 14;

/// The terms one job of a parallel [`compact`] counts, then copies.
const COMPACT_CHUNK: usize = 1 << 11;

/// The terms with a non-zero scalar.
fn nonzero_terms<'a, C: CurveAffine>(
    coeffs: &'a [C::Scalar],
    bases: &'a [C],
) -> impl Iterator<Item = (&'a C::Scalar, &'a C)> {
    coeffs.iter().zip(bases).filter(|(s, _)| !s.is_zero_vartime())
}

/// The non-zero terms of a sparse input, compacted; `None` when at least half
/// the scalars are non-zero (the input is then used in place). Zero scalars add
/// nothing to the buckets, but the window, hence the buckets each tile
/// integrates, is chosen by the length, so a sparse MSM would pay for its
/// zeros.
fn compact<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> Option<(Vec<C::Scalar>, Vec<C>)> {
    let n = coeffs.len();
    // On the calling thread below `PARALLEL_COMPACT`: waking the pool costs
    // more than the work for a small input.
    if n < PARALLEL_COMPACT {
        let nonzero = coeffs.iter().filter(|s| !s.is_zero_vartime()).count();
        if 2 * nonzero >= n {
            return None;
        }
        let (mut scalars, mut points) = (Vec::with_capacity(nonzero), Vec::with_capacity(nonzero));
        for (s, b) in nonzero_terms(coeffs, bases) {
            scalars.push(*s);
            points.push(*b);
        }
        return Some((scalars, points));
    }
    let counts: Vec<usize> = coeffs
        .par_chunks(COMPACT_CHUNK)
        .map(|chunk| chunk.iter().filter(|s| !s.is_zero_vartime()).count())
        .collect();
    let nonzero = counts.iter().sum::<usize>();
    if 2 * nonzero >= n {
        return None;
    }
    let (mut scalars, mut points) = (Vec::new(), Vec::new());
    repeat_n(C::Scalar::ZERO, nonzero).collect_into_vec(&mut scalars);
    repeat_n(C::identity(), nonzero).collect_into_vec(&mut points);
    // Each chunk's own slice of the outputs, by the running sum of the counts.
    let mut slices = Vec::with_capacity(counts.len());
    let (mut rest_s, mut rest_p) = (scalars.as_mut_slice(), points.as_mut_slice());
    for &count in &counts {
        let (s, tail) = std::mem::take(&mut rest_s).split_at_mut(count);
        rest_s = tail;
        let (p, tail) = std::mem::take(&mut rest_p).split_at_mut(count);
        rest_p = tail;
        slices.push((s, p));
    }
    coeffs
        .par_chunks(COMPACT_CHUNK)
        .zip(bases.par_chunks(COMPACT_CHUNK))
        .zip(slices)
        .for_each(|((cs, bs), (scalars, points))| {
            for (i, (s, b)) in nonzero_terms(cs, bs).enumerate() {
                scalars[i] = *s;
                points[i] = *b;
            }
        });
    Some((scalars, points))
}

/// The multi-scalar multiplication `Σ coeffs[i]·bases[i]` (the identity if
/// there are no terms), as used for polynomial commitments: a Pippenger over
/// blst-style tiles of windows × chunks of the terms, with batched affine
/// buckets from window 7 and XYZZ buckets below. Parallel; identity bases and
/// zero scalars contribute nothing.
///
/// # Panics
///
/// If `coeffs` and `bases` have different lengths.
pub fn msm_pippenger<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    if let Some((coeffs, bases)) = compact(coeffs, bases) {
        return msm_with_window(&coeffs, &bases, window_size(bases.len()));
    }
    msm_with_window(coeffs, bases, window_size(bases.len()))
}

#[cfg(test)]
mod tests;

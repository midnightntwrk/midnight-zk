use std::{
    convert::TryInto,
    ops::{Neg, Range},
};

use ff::{Field, PrimeField};
use group::{Curve, Group};
use rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
    },
    slice::ParallelSlice,
};

use crate::{CurveAffine, FieldInto};

#[inline]
fn get_booth_index(window_index: usize, window_size: usize, el: &[u8]) -> i32 {
    // Booth encoding:
    // * step by `window` size
    // * slice by size of `window + 1``
    // * each window overlap by 1 bit * append a zero bit to the least significant
    //   end
    // Indexing rule for example window size 3 where we slice by 4 bits:
    // `[0, +1, +1, +2, +2, +3, +3, +4, -4, -3, -3 -2, -2, -1, -1, 0]``
    // So we can reduce the bucket size without preprocessing scalars
    // and remembering them as in classic signed digit encoding

    let skip_bits = (window_index * window_size).saturating_sub(1);
    let skip_bytes = skip_bits / 8;

    // fill into a u32
    let mut v: [u8; 4] = [0; 4];
    match el.get(skip_bytes..skip_bytes + 4) {
        // One load, rather than a byte copy loop (a `memmove` call on aarch64)
        Some(bytes) => v.copy_from_slice(bytes),
        None => {
            for (dst, src) in v.iter_mut().zip(el.iter().skip(skip_bytes)) {
                *dst = *src
            }
        }
    }
    let mut tmp = u32::from_le_bytes(v);

    // pad with one 0 if slicing the least significant window
    if window_index == 0 {
        tmp <<= 1;
    }

    // remove further bits
    tmp >>= skip_bits - (skip_bytes * 8);
    // apply the booth window
    tmp &= (1 << (window_size + 1)) - 1;

    let sign = tmp & (1 << window_size) == 0;

    // div ceil by 2
    tmp = (tmp + 1) >> 1;

    // find the booth action index
    if sign {
        tmp as i32
    } else {
        ((!(tmp - 1) & ((1 << window_size) - 1)) as i32).neg()
    }
}

/// Wrapper to provide direct access to affine coordinates.
/// This avoids repeated calls to `CurveAffine::coordinates()` (which returns
/// a `CtOption` and performs an identity check).
#[derive(Debug, Clone, Copy)]
struct Affine<C: CurveAffine> {
    x: C::Base,
    y: C::Base,
}

impl<C: CurveAffine> Affine<C> {
    /// The coordinates, or zeros for the identity (whose scalar the MSM then zeroes, so they
    /// are never read)
    fn from(point: &C) -> Self {
        match Option::<crate::Coordinates<C>>::from(point.coordinates()) {
            Some(c) => Self {
                x: *c.x(),
                y: *c.y(),
            },
            None => Self {
                x: C::Base::ZERO,
                y: C::Base::ZERO,
            },
        }
    }
}

/// A point in XYZZ coordinates, `(x, y) = (X/ZZ, Y/ZZZ)` with `ZZ^3 = ZZZ^2`; the identity has
/// `ZZ = ZZZ = 0`. Adding an affine point costs 8M + 2S and no inversion, which makes these
/// good Pippenger buckets (as in blst). The formulas assume `a = 0`.
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

    // Variable time: which buckets are touched depends on the scalars anyway
    fn is_identity(&self) -> bool {
        self.zz.is_zero_vartime() && self.zzz.is_zero_vartime()
    }

    /// `self += (x2, y2)`, or `-= ` if `negate`, for an affine point `(x2, y2)` on the curve
    /// (EFD madd-2008-s; [`Self::double`] when the points are equal). Like blst, every result
    /// is written where it is needed ([`FieldInto`]), never copied while fresh.
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
        // P = x2·ZZ1 - X1, R = y2·ZZZ1 - Y1
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
            // X3 = R^2 - PPP - 2Q
            F::square_into(&mut self.x, &r);
            self.x -= &ppp;
            self.x -= &q;
            self.x -= &q;
            // Y3 = R·(Q - X3) - Y1·PPP
            q -= &self.x;
            q *= &r;
            self.y *= &ppp;
            F::rsub_assign(&mut self.y, &q);
            self.zz *= &pp;
            self.zzz *= &ppp;
        } else if r.is_zero_vartime() {
            // Equal points (rare)
            *self = Self::from_affine(x2, y2);
            self.double();
        } else {
            *self = Self::identity();
        }
    }

    /// `self += other` (EFD add-2008-s, and dbl-2008-s-1 when the points are equal)
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

    /// `2·self` (EFD dbl-2008-s-1, `a = 0`); `2·O = O`
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

    /// The points, by one inversion for all (Montgomery's trick on the `ZZZ`s)
    fn batch_to_curve<C: CurveAffine<Base = F>>(points: &[Self]) -> Vec<C::Curve> {
        // prefix[i] = product of the nonzero ZZZs before i
        let mut prefix = Vec::with_capacity(points.len());
        let mut acc = F::ONE;
        for p in points {
            prefix.push(acc);
            if !p.is_identity() {
                acc *= p.zzz;
            }
        }
        let mut inv = acc.invert().unwrap();
        let mut out = vec![C::Curve::identity(); points.len()];
        for (i, p) in points.iter().enumerate().rev() {
            if p.is_identity() {
                continue;
            }
            let zzz_inv = inv * prefix[i];
            inv *= p.zzz;
            // ZZ^3 = ZZZ^2, so 1/ZZ = ZZ^2/ZZZ^2
            let zz_inv = zzz_inv.square() * p.zz.square();
            out[i] = C::from_xy_unchecked(p.x * zz_inv, p.y * zzz_inv).to_curve();
        }
        out
    }
}

/// Fixed-base MSM tables: `2^(c·w)·P` for every base `P` and window `w`, so an MSM over these
/// bases sends every window's digits to one set of buckets: one bucket sum in all, and no
/// doublings between windows, where [`msm_best`] has one sum and `c` doublings a window.
/// Worth it for bases used many times (commitment keys).
///
/// Memory: one affine point per base and window, `(⌊255/c⌋ + 1)·96` bytes a base on
/// BLS12-381 G1, about 100 MB for 2^16 bases at `c = 16`. The table grows with the bases
/// ([`Self::extend`]), and an MSM may use any prefix of them, so one table built for the
/// largest size serves every smaller one over the same (monomial) bases.
pub struct FixedBases<C: CurveAffine> {
    c: usize,
    windows: usize,
    /// Base `i`'s row, `windows` entries from `i·windows`; zero for the identity
    table: Vec<Affine<C>>,
    identity: Vec<bool>,
}

impl<C: CurveAffine> FixedBases<C> {
    /// The table for `bases` with window size `c`, at least 7 (batched affine buckets); 16
    /// was best for 2^14..2^16 bases on BLS12-381 G1
    pub fn new(bases: &[C], c: usize) -> Self {
        assert!(c >= 7, "fixed-base window {c} below 7");
        let mut table = Self {
            c,
            windows: C::Scalar::NUM_BITS as usize / c + 1,
            table: Vec::new(),
            identity: Vec::new(),
        };
        table.extend(bases);
        table
    }

    /// Appends rows for more bases: `c` doublings a window, then one inversion per chunk of
    /// bases to make them affine
    pub fn extend(&mut self, bases: &[C]) {
        let (c, windows) = (self.c, self.windows);
        let rows: Vec<Vec<Affine<C>>> = bases
            .par_chunks(256)
            .map(|chunk| {
                let mut shifted = Vec::with_capacity(chunk.len() * windows);
                for b in chunk {
                    let mut p = b.to_curve();
                    for _ in 0..windows {
                        shifted.push(p);
                        (0..c).for_each(|_| p = p.double());
                    }
                }
                let mut affine = vec![C::identity(); shifted.len()];
                C::Curve::batch_normalize(&shifted, &mut affine);
                affine.iter().map(Affine::from).collect()
            })
            .collect();
        self.table.extend(rows.into_iter().flatten());
        self.identity.extend(bases.iter().map(|b| bool::from(b.is_identity())));
    }

    /// `Σ coeffs[i]·bases[i]` over the first `coeffs.len()` bases.
    ///
    /// The digits are split by bucket range, one range a task, so that each task adds only
    /// into its own buckets and the bucket sums cost one set's worth whatever the threads;
    /// the ranges then combine as `Σ_p (sum_p + p·range·total_p)`.
    ///
    /// # Panics
    ///
    /// If there are more scalars than bases.
    pub fn msm(&self, coeffs: &[C::Scalar]) -> C::Curve {
        let n = coeffs.len();
        let bases = self.identity.len();
        assert!(n <= bases, "{n} scalars for {bases} bases");
        assert!(
            n * self.windows <= u32::MAX as usize,
            "{n} bases: table index past u32"
        );
        let (c, windows) = (self.c, self.windows);
        let threads = rayon::current_num_threads();
        let buckets = 1usize << (c - 1);
        let parts = (2 * threads).next_power_of_two().clamp(1, buckets / 64);
        let range = buckets / parts;
        // [chunk][range]: (table index, digit)
        let chunk = n.div_ceil(4 * threads).max(256);
        let split: Vec<Vec<Vec<(u32, i32)>>> = coeffs
            .par_chunks(chunk)
            .enumerate()
            .map(|(k, coeffs)| {
                // Digits spread evenly over the ranges; a little over, to spare regrowth
                let cap = coeffs.len() * windows / parts * 9 / 8 + 16;
                let mut out = vec![Vec::with_capacity(cap); parts];
                for (i, s) in coeffs.iter().enumerate().map(|(j, s)| (k * chunk + j, s)) {
                    if self.identity[i] {
                        continue;
                    }
                    let repr = s.to_repr();
                    for w in 0..windows {
                        let d = get_booth_index(w, c, repr.as_ref());
                        if d != 0 {
                            let b = (d.unsigned_abs() as usize - 1) / range;
                            out[b].push(((i * windows + w) as u32, d));
                        }
                    }
                }
                out
            })
            .collect();
        let batch = (range / 4).clamp(64, 256).min(range);
        let sums: Vec<_> = (0..parts)
            .into_par_iter()
            .map(|p| {
                let mut a = AffineBuckets::new(range, batch);
                for (k, d) in split.iter().flat_map(|chunk| &chunk[p]) {
                    let point = &self.table[*k as usize];
                    let b = d.unsigned_abs() as usize - 1 - p * range;
                    a.add(b, &point.x, &point.y, *d < 0);
                }
                a.integrate_and_clear(range)
            })
            .collect();
        // Σ_p p·total_p by running sums, times `range`, plus Σ_p sum_p
        let (mut run, mut acc, mut local) = (Xyzz::identity(), Xyzz::identity(), Xyzz::identity());
        for (sum, total) in sums.iter().rev() {
            acc.add(&run);
            run.add(total);
            local.add(sum);
        }
        (0..range.ilog2()).for_each(|_| acc.double());
        acc.add(&local);
        Xyzz::batch_to_curve::<C>(&[acc])[0]
    }
}

/// One scalar multiplication per term, in parallel, then their sum: best for a few terms
#[doc(hidden)]
pub fn msm_pointwise<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    coeffs
        .par_iter()
        .zip(bases.par_iter())
        .map(|(s, b)| b.to_curve() * s)
        .reduce(C::Curve::identity, |a, b| a + b)
}

/// Pippenger parallel over tiles of windows × chunks of the terms (blst's design), with
/// batched affine buckets from `c = 7` ([`AffineBuckets`], gnark's) and XYZZ buckets below;
/// window size `c`. Below 32 terms, one scalar multiplication per term instead.
#[doc(hidden)]
pub fn msm_with_window<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C], c: usize) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    if coeffs.len() < 32 {
        return msm_pointwise(coeffs, bases);
    }
    let nbits = C::Scalar::NUM_BITS as usize;
    // Scalars converted by the tiles as they need them; an identity base gets a zero scalar,
    // so it is never added (nor its coordinates read)
    let zero = C::Scalar::ZERO.to_repr();
    let repr = |r: Range<usize>| -> Vec<_> {
        let repr = |i: usize| match bool::from(bases[i].is_identity()) {
            true => zero,
            false => coeffs[i].to_repr(),
        };
        r.map(repr).collect()
    };
    if bases.first().is_some_and(|b| b.xy_ref().is_some()) {
        // Coordinates read in place
        let xy = |i: usize| bases[i].xy_ref().unwrap();
        return pippenger::<C, _, _, _>(coeffs.len(), repr, xy, nbits, c);
    }
    let points: Vec<Affine<C>> = bases.par_iter().map(Affine::from).collect();
    let xy = |i: usize| (&points[i].x, &points[i].y);
    pippenger::<C, _, _, _>(coeffs.len(), repr, xy, nbits, c)
}

/// `⌊2^256 / λ⌋` as little-endian limbs (129 bits for a 128-bit `λ`), by long division:
/// the Barrett constant for [`glv_split`]
fn glv_reciprocal(lambda: u128) -> [u64; 3] {
    // The numerator is a 1 followed by 256 zeros; its leading 1 is below λ, so that quotient
    // bit is 0 and the remainder starts at 1
    let (mut rem, mut q) = (1u128, [0u64; 3]);
    for _ in 0..256 {
        let carry = rem >> 127;
        rem <<= 1;
        let bit = carry == 1 || rem >= lambda;
        if bit {
            rem = rem.wrapping_sub(lambda);
        }
        q = [
            q[0] << 1 | u64::from(bit),
            q[1] << 1 | q[0] >> 63,
            q[2] << 1 | q[1] >> 63,
        ];
    }
    q
}

/// `k = k2·λ + k1` with `k1 < λ`, for a little-endian `k < 2^128 λ`: the GLV halves,
/// little-endian. By Barrett reduction with `m = glv_reciprocal(λ)`: `(k·m) >> 256` is at
/// most 2 below `⌊k/λ⌋`, and the remainder is corrected by subtracting `λ`
#[doc(hidden)]
pub fn glv_split(k: &[u8], lambda: u128, m: &[u64; 3]) -> ([u8; 16], [u8; 16]) {
    let mut bytes = [0u8; 32];
    bytes[..k.len()].copy_from_slice(k);
    let kl: [u64; 4] =
        core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()));
    // k·m, keeping limbs 4 and 5 (bits 256..384; the quotient is below 2^128)
    let mut prod = [0u64; 7];
    for (i, ki) in kl.iter().enumerate() {
        let mut carry = 0u128;
        for (j, mj) in m.iter().enumerate() {
            let t = u128::from(*ki) * u128::from(*mj) + u128::from(prod[i + j]) + carry;
            prod[i + j] = t as u64; // lossless: the low 64 bits, by design
            carry = t >> 64;
        }
        prod[i + 3] = carry as u64; // lossless: a 64-bit carry
    }
    let mut q = u128::from(prod[4]) | (u128::from(prod[5]) << 64);
    // r = k - q·λ, which is below 3λ < 2^130: compute it mod 2^192
    let (ql, qh) = (q as u64, (q >> 64) as u64); // lossless: the two halves
    let (ll, lh) = (lambda as u64, (lambda >> 64) as u64); // lossless: the two halves
    let p0 = u128::from(ql) * u128::from(ll);
    let p1 = u128::from(ql) * u128::from(lh) + u128::from(qh) * u128::from(ll) + (p0 >> 64);
    let p2 = u128::from(qh) * u128::from(lh) + (p1 >> 64);
    let ql_lambda = [p0 as u64, p1 as u64, p2 as u64]; // lossless: limbs of q·λ mod 2^192
    let mut r = [0u64; 3];
    let mut borrow = 0u64;
    for i in 0..3 {
        let (d, b1) = kl[i].overflowing_sub(ql_lambda[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        r[i] = d;
        borrow = u64::from(b1 | b2);
    }
    // At most two corrections; r has at most 130 bits
    for _ in 0..3 {
        let r_lo = u128::from(r[0]) | (u128::from(r[1]) << 64);
        if r[2] == 0 && r_lo < lambda {
            break;
        }
        let (d, b) = r_lo.overflowing_sub(lambda);
        r = [d as u64, (d >> 64) as u64, r[2] - u64::from(b)]; // lossless: halves of d
        q += 1;
    }
    debug_assert!(r[2] == 0 && (u128::from(r[0]) | (u128::from(r[1]) << 64)) < lambda);
    let rem = u128::from(r[0]) | (u128::from(r[1]) << 64);
    (rem.to_le_bytes(), q.to_le_bytes())
}

/// [`msm_with_window`] through a GLV endomorphism ([`CurveAffine::glv`]): twice the terms,
/// with 128-bit scalars, so half the windows and doublings.
#[doc(hidden)]
pub fn msm_glv_with_window<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    c: usize,
) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    let Some((beta, lambda)) = C::glv() else {
        return msm_with_window(coeffs, bases, c);
    };
    let m = glv_reciprocal(lambda);
    if coeffs.len() < 32 {
        return msm_pointwise(coeffs, bases);
    }
    // Each term as two, (k1, P) and (k2, φ(P)); an identity base gets zero scalars
    let split = |(s, b): (&C::Scalar, &C)| {
        let (k1, k2) = match bool::from(b.is_identity()) {
            true => ([0; 16], [0; 16]),
            false => glv_split(s.to_repr().as_ref(), lambda, &m),
        };
        let p = Affine::from(b);
        let phi = Affine {
            x: p.x * beta,
            y: p.y,
        };
        [(k1, p), (k2, phi)]
    };
    let (scalars, points): (Vec<[u8; 16]>, Vec<Affine<C>>) =
        coeffs.iter().zip(bases).flat_map(split).unzip();
    let repr = |r: Range<usize>| scalars[r].to_vec();
    pippenger::<C, _, _, _>(
        scalars.len(),
        repr,
        |i| (&points[i].x, &points[i].y),
        128,
        c,
    )
}

/// The Pippenger's window size for `n` terms, measured on BLS12-381 G1 by sweeping it: x86-64
/// on a Ryzen 5950X (32 threads), aarch64 on an Apple M3 Max (12 performance and 4
/// efficiency cores), which wants wider windows.
#[doc(hidden)]
pub fn window_size(n: usize) -> usize {
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

/// The point-chunk count for window size `c`: the least cost, as parallel rounds times one
/// tile's work (its bucket additions, then summing its buckets); chunks of the terms give
/// more tiles when there are fewer windows than threads, as in blst's `breakdown`
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

/// `Σ (i + 1)·buckets[i]` by running sums, emptying the buckets for reuse
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

/// Pippenger buckets in affine form, added to in batches: one inversion serves a whole batch
/// of slopes (Montgomery's trick), so an addition costs 5M + 1S and a share of the inversion,
/// against 8M + 2S into an XYZZ bucket (as in gnark). A point whose bucket is already in the
/// batch waits for the next one; past a batch's worth of those, or if it would double or
/// cancel its bucket, it goes to an XYZZ bucket beside it.
struct AffineBuckets<'a, F> {
    buckets: Vec<AffineBucket<F>>,
    /// Allocated on first use (rare: busy buckets, doubling or cancelling points)
    side: Vec<Xyzz<F>>,
    /// Whether any `side` bucket is in use
    sides: bool,
    /// Awaiting the next batch, with their `x` differences and the running products of those
    batch: Vec<Pending<'a, F>>,
    dx: Vec<F>,
    prefix: Vec<F>,
    /// Waiting for their bucket to leave the batch (and `spare`, its double buffer)
    waiting: Vec<Pending<'a, F>>,
    spare: Vec<Pending<'a, F>>,
    /// Running sums for the lanes of [`Self::integrate_lanes`]
    acc: Vec<AffineBucket<F>>,
    sum: Vec<AffineBucket<F>>,
}

/// An affine bucket (or running sum): its point when `full`; `queued` while it has an
/// addition in the batch
#[derive(Clone, Copy)]
struct AffineBucket<F> {
    x: F,
    y: F,
    full: bool,
    queued: bool,
}

/// `buckets[bucket] += ±(x, y)`, batched, the point borrowed from the caller's bases (or
/// [`FixedBases`] table). `same_x` if the point shares the bucket's `x`, so the addition
/// doubles or cancels it (no slope: added in XYZZ instead).
#[derive(Clone, Copy)]
struct Pending<'a, F> {
    bucket: usize,
    x: &'a F,
    y: &'a F,
    negate: bool,
    same_x: bool,
}

/// At most this many lanes of running sums when summing the buckets (an eighth of them is
/// best, measured on BLS12-381 G1, single core)
const LANES: usize = 128;

impl<'a, F: FieldInto> AffineBuckets<'a, F> {
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
            side: Vec::new(),
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

    /// `buckets[b] += ±(x, y)`, now or in a later batch
    fn add(&mut self, b: usize, x: &'a F, y: &'a F, negate: bool) {
        let p = Pending {
            bucket: b,
            x,
            y,
            negate,
            same_x: false,
        };
        self.enqueue(p);
        if self.batch.len() == self.dx.len() {
            self.flush();
        }
    }

    fn enqueue(&mut self, p: Pending<'a, F>) {
        let bucket = &mut self.buckets[p.bucket];
        if !bucket.full {
            bucket.x = *p.x;
            if p.negate {
                F::neg_into(&mut bucket.y, p.y);
            } else {
                bucket.y = *p.y;
            }
            bucket.full = true;
        } else if !bucket.queued {
            bucket.queued = true;
            self.batch.push(p);
        } else if self.waiting.len() < self.dx.len() {
            self.waiting.push(p);
        } else {
            self.side_add(&p);
        }
    }

    /// `side[p.bucket] += ±(p.x, p.y)`
    fn side_add(&mut self, p: &Pending<'a, F>) {
        if self.side.is_empty() {
            self.side = vec![Xyzz::identity(); self.buckets.len()];
        }
        self.side[p.bucket].add_affine(p.x, p.y, p.negate);
        self.sides = true;
    }

    /// Adds the batch, then queues the waiting points whose buckets it freed, again while
    /// they fill a batch
    fn flush(&mut self) {
        loop {
            self.add_batch();
            std::mem::swap(&mut self.waiting, &mut self.spare);
            for k in 0..self.spare.len() {
                let p = self.spare[k];
                self.enqueue(p);
            }
            self.spare.clear();
            if self.batch.len() < self.dx.len() {
                return;
            }
        }
    }

    /// Adds the batch ([`add_with_inverse`]), one inversion for all
    fn add_batch(&mut self) {
        let len = self.batch.len();
        for (p, dx) in self.batch.iter_mut().zip(&mut self.dx) {
            F::sub_into(dx, p.x, &self.buckets[p.bucket].x);
            // Doubles or cancels: added apart from the batch, below
            p.same_x = dx.is_zero_vartime();
            if p.same_x {
                *dx = F::ONE;
            }
        }
        invert_all(&mut self.dx[..len], &mut self.prefix);
        for j in 0..len {
            let p = self.batch[j];
            let bucket = &mut self.buckets[p.bucket];
            bucket.queued = false;
            if p.same_x {
                self.side_add(&p);
            } else {
                let inv = &self.dx[j];
                add_with_inverse(&mut bucket.x, &mut bucket.y, p.x, p.y, p.negate, inv);
            }
        }
        self.batch.clear();
    }

    /// Every pending addition done: a few more batches for the waiting points, then the XYZZ
    /// buckets for the rest
    fn flush_all(&mut self) {
        for _ in 0..4 {
            if self.batch.is_empty() && self.waiting.is_empty() {
                break;
            }
            self.flush();
        }
        for k in 0..self.batch.len() {
            let p = self.batch[k];
            self.buckets[p.bucket].queued = false;
            self.waiting.push(p);
        }
        self.batch.clear();
        let waiting = std::mem::take(&mut self.waiting);
        for p in &waiting {
            self.side_add(p);
        }
        self.waiting = waiting;
        self.waiting.clear();
    }

    /// `Σ (b + 1)·buckets[b]` over the first `used` buckets, and their plain sum, emptying
    /// them for reuse
    fn integrate_and_clear(&mut self, used: usize) -> (Xyzz<F>, Xyzz<F>) {
        self.flush_all();
        let lanes = (used / 8).clamp(32, self.acc.len());
        if !self.sides
            && used >= 4 * lanes
            && let Some(sums) = self.integrate_lanes(used, lanes)
        {
            self.buckets[..used].iter_mut().for_each(|b| b.full = false);
            return sums;
        }
        let mut acc = Xyzz::identity();
        let mut sum = Xyzz::identity();
        for b in (0..used).rev() {
            let bucket = &mut self.buckets[b];
            if bucket.full {
                acc.add_affine(&bucket.x, &bucket.y, false);
                bucket.full = false;
            }
            if let Some(side) = self.side.get_mut(b)
                && !side.is_identity()
            {
                acc.add(side);
                *side = Xyzz::identity();
            }
            sum.add(&acc);
        }
        self.sides = false;
        (sum, acc)
    }

    /// `Σ (b + 1)·buckets[b]`, and their plain sum, by running sums over `lanes` contiguous
    /// segments of the buckets at once, each step's additions sharing one inversion; the
    /// segments' sums then combine as `Σ_l (sum_l + l·seg·acc_l)`. Nothing if an addition
    /// would double or cancel (the caller then sums in XYZZ).
    fn integrate_lanes(&mut self, used: usize, lanes: usize) -> Option<(Xyzz<F>, Xyzz<F>)> {
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
        // Σ_l l·acc_l by running sums over the lanes, times `seg`, plus Σ_l sum_l; `run`
        // ends as Σ_l acc_l, the plain sum
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
        Some((total, run))
    }
}

/// `dst[l] += src(l)` in every lane, the additions sharing one inversion; false if one would
/// double or cancel (`dst` is then partly updated)
fn add_lanes<'a, F: FieldInto + 'a>(
    dst: &mut [AffineBucket<F>],
    src: impl Fn(usize) -> &'a AffineBucket<F>,
    dx: &mut [F],
    prefix: &mut [F],
) -> bool {
    // Lanes with both points: their x differences
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
    let mut inv = dx.iter();
    for (l, d) in dst.iter_mut().enumerate().filter(|(_, d)| d.queued) {
        let s = src(l);
        d.queued = false;
        add_with_inverse(&mut d.x, &mut d.y, &s.x, &s.y, false, inv.next().unwrap());
    }
    true
}

/// Montgomery's trick: `values` (all non-zero) become their inverses, for one inversion and
/// 3M each; `scratch` (at least as long) holds the running products
fn invert_all<F: FieldInto>(values: &mut [F], scratch: &mut [F]) {
    let Some(last) = values.len().checked_sub(1) else {
        return;
    };
    scratch[0] = values[0];
    for j in 1..values.len() {
        let (done, rest) = scratch.split_at_mut(j);
        F::mul_into(&mut rest[0], &done[j - 1], &values[j]);
    }
    let mut inv = scratch[last].invert().unwrap();
    for j in (1..values.len()).rev() {
        // 1/v_j = (v_0···v_j)^-1 · (v_0···v_{j-1})
        let (done, rest) = scratch.split_at_mut(j);
        F::mul_into(&mut rest[0], &inv, &done[j - 1]);
        inv *= &values[j];
        values[j] = rest[0];
    }
    values[0] = inv;
}

/// `(x1, y1) += (x2, ±y2)` (`-y2` if `negate`), given `inv = 1/(x2 - x1)`:
/// `λ = (y2 - y1)·inv`, `x' = λ² - x1 - x2`, `y' = λ(x1 - x') - y1`. Adding `-P`, the slope is
/// `-λ'` for `λ' = (y2 + y1)·inv`, and then `y' = λ'(x' - x1) - y1`: no negation needed.
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

/// Scalars converted together by [`pippenger`]'s tiles
const SCALAR_BLOCK: usize = 256;

/// The Pippenger over `n` affine points `xy(i)` (none the identity) and little-endian
/// scalars of `nbits` bits, `repr(range)` giving those in `range`.
///
/// The scalars are converted lazily, a block at a time, by whichever tile first needs a block,
/// so the conversion runs in parallel with no fork-join of its own. Each tile visits its
/// blocks starting at its own offset, so the first tiles, which start together, convert
/// different blocks rather than queue on one.
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
    // Whole blocks per chunk
    let chunk = n.div_ceil(chunks).next_multiple_of(SCALAR_BLOCK);
    let blocks: Vec<OnceLock<Vec<S>>> =
        (0..n.div_ceil(SCALAR_BLOCK)).map(|_| OnceLock::new()).collect();
    let tiles = windows * chunks;
    // Tile `t` is chunk `t % chunks` of window `windows - 1 - t / chunks`: the most
    // significant windows first, so the combination below can start while the rest run
    let results: Vec<OnceLock<Xyzz<C::Base>>> = (0..tiles).map(|_| OnceLock::new()).collect();
    let pending: Vec<AtomicUsize> = (0..windows).map(|_| AtomicUsize::new(chunks)).collect();
    let next = AtomicUsize::new(0);
    let (done_tx, done_rx) = mpsc::channel::<usize>();
    let mut acc = Xyzz::identity();
    // Batched affine buckets from 64 buckets up; the batch is a quarter of the buckets, so
    // few points find theirs already in it (measured on BLS12-381 G1, single core)
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
                    // only 2^that: integrate just those buckets (as blst does)
                    let used = 1 << (nbits - w * c).min(c - 1);
                    // `start` is a block boundary, or `n` for a chunk past the end
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
                                let (x, y) = xy(i);
                                match &mut affine {
                                    Some(a) => a.add(b, x, y, d < 0),
                                    None => buckets[b].add_affine(x, y, d < 0),
                                }
                            }
                        }
                    }
                    let sum = match &mut affine {
                        Some(a) => a.integrate_and_clear(used).0,
                        None => integrate_and_clear(&mut buckets[..used]),
                    };
                    let _ = results[t].set(sum);
                    if pending[w].fetch_sub(1, Ordering::AcqRel) == 1 {
                        // The receiver outlives the scope
                        let _ = done_tx.send(w);
                    }
                }
            });
        }
        drop(done_tx);
        // Horner's rule as the windows complete, most significant first
        let mut ready = vec![false; windows];
        let mut w_next = windows;
        while w_next > 0 {
            let w = match done_rx.try_recv() {
                Ok(w) => w,
                Err(mpsc::TryRecvError::Empty) => {
                    // Help with the tiles, or wait if this thread is not in the pool
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
                    acc.add(results[(windows - 1 - w_next) * chunks + k].get().unwrap());
                }
            }
        }
    });
    Xyzz::batch_to_curve::<C>(&[acc])[0]
}

/// Performs a multi-scalar multiplication operation.
///
/// This function will panic if coeffs and bases have a different length.
pub fn msm_serial<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C], acc: &mut C::Curve) {
    let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();

    let c = if bases.len() < 4 {
        1
    } else if bases.len() < 32 {
        3
    } else {
        (f64::from(bases.len() as u32)).ln().ceil() as usize
    };

    let field_byte_size = C::Scalar::NUM_BITS.div_ceil(8u32) as usize;
    // OR all coefficients in order to make a mask to figure out the maximum number
    // of bytes used among all coefficients.
    let mut acc_or = vec![0; field_byte_size];
    for coeff in &coeffs {
        for (acc_limb, limb) in acc_or.iter_mut().zip(coeff.as_ref().iter()) {
            *acc_limb |= *limb;
        }
    }
    let max_byte_size =
        field_byte_size - acc_or.iter().rev().position(|v| *v != 0).unwrap_or(field_byte_size);
    if max_byte_size == 0 {
        return;
    }
    let number_of_windows = max_byte_size * 8_usize / c + 1;

    for current_window in (0..number_of_windows).rev() {
        for _ in 0..c {
            *acc = acc.double();
        }

        #[derive(Clone, Copy)]
        enum Bucket<C: CurveAffine> {
            None,
            Affine(C),
            Projective(C::Curve),
        }

        impl<C: CurveAffine> Bucket<C> {
            fn add_assign(&mut self, other: &C) {
                *self = match *self {
                    Bucket::None => Bucket::Affine(*other),
                    Bucket::Affine(a) => Bucket::Projective(a + *other),
                    Bucket::Projective(mut a) => {
                        a += *other;
                        Bucket::Projective(a)
                    }
                }
            }

            fn add(self, mut other: C::Curve) -> C::Curve {
                match self {
                    Bucket::None => other,
                    Bucket::Affine(a) => {
                        other += a;
                        other
                    }
                    Bucket::Projective(a) => other + a,
                }
            }
        }

        let mut buckets: Vec<Bucket<C>> = vec![Bucket::None; 1 << (c - 1)];

        for (coeff, base) in coeffs.iter().zip(bases.iter()) {
            let coeff = get_booth_index(current_window, c, coeff.as_ref());
            if coeff.is_positive() {
                buckets[coeff as usize - 1].add_assign(base);
            }
            if coeff.is_negative() {
                buckets[coeff.unsigned_abs() as usize - 1].add_assign(&base.neg());
            }
        }

        // Summation by parts
        // e.g. 3a + 2b + 1c = a +
        //                    (a) + b +
        //                    ((a) + b) + c
        let mut running_sum = C::Curve::identity();
        for exp in buckets.into_iter().rev() {
            running_sum = exp.add(running_sum);
            *acc += &running_sum;
        }
    }
}

/// Performs a multi-scalar multiplication operation.
///
/// This function will panic if coeffs and bases have a different length.
///
/// This will use multithreading if beneficial.
pub fn msm_parallel<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());

    let num_threads = rayon::current_num_threads();
    if coeffs.len() > num_threads {
        let chunk = coeffs.len() / num_threads;
        let num_chunks = coeffs.chunks(chunk).len();
        let mut results = vec![C::Curve::identity(); num_chunks];
        rayon::in_place_scope(|scope| {
            let chunk = coeffs.len() / num_threads;

            for ((coeffs, bases), acc) in
                coeffs.chunks(chunk).zip(bases.chunks(chunk)).zip(results.iter_mut())
            {
                scope.spawn(move |_| {
                    msm_serial(coeffs, bases, acc);
                });
            }
        });
        results.iter().fold(C::Curve::identity(), |a, b| a + b)
    } else {
        let mut acc = C::Curve::identity();
        msm_serial(coeffs, bases, &mut acc);
        acc
    }
}

/// The multi-scalar multiplication `Σ coeffs[i]·bases[i]`: a Pippenger over blst-style tiles,
/// with batched affine buckets from window 7 and XYZZ ones below ([`msm_with_window`]),
/// through the GLV endomorphism ([`CurveAffine::glv`]) for 32..128 terms, and one scalar
/// multiplication per term below 32. Parallel; identity bases contribute nothing.
///
/// # Panics
///
/// If `coeffs` and `bases` have different lengths.
pub fn msm_best<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    // Measured on BLS12-381 G1: GLV halves the doublings, which pays only while they are
    // a large share of the work
    if (32..128).contains(&bases.len()) && C::glv().is_some() {
        return msm_glv_with_window(coeffs, bases, 5);
    }
    msm_with_window(coeffs, bases, window_size(bases.len()))
}

#[cfg(test)]
mod test {
    use std::ops::Neg;

    use ff::{Field, PrimeField};
    use group::{Curve, Group};
    use rand_core::OsRng;

    use crate::{
        CurveAffine,
        bn256::{Fr, G1, G1Affine},
    };

    #[test]
    fn test_booth_encoding() {
        fn mul(scalar: &Fr, point: &G1Affine, window: usize) -> G1Affine {
            let u = scalar.to_repr();
            let n = Fr::NUM_BITS as usize / window + 1;

            let table =
                (0..=1 << (window - 1)).map(|i| point * Fr::from(i as u64)).collect::<Vec<_>>();

            let mut acc = G1::identity();
            for i in (0..n).rev() {
                for _ in 0..window {
                    acc = acc.double();
                }

                let idx = super::get_booth_index(i, window, u.as_ref());

                if idx.is_negative() {
                    acc += table[idx.unsigned_abs() as usize].neg();
                }
                if idx.is_positive() {
                    acc += table[idx.unsigned_abs() as usize];
                }
            }

            acc.to_affine()
        }

        let (scalars, points): (Vec<_>, Vec<_>) = (0..10)
            .map(|_| {
                let scalar = Fr::random(OsRng);
                let point = G1Affine::random(OsRng);
                (scalar, point)
            })
            .unzip();

        for window in 1..10 {
            for (scalar, point) in scalars.iter().zip(points.iter()) {
                let c0 = mul(scalar, point, window);
                let c1 = point * scalar;
                assert_eq!(c0, c1.to_affine());
            }
        }
    }

    fn run_msm_cross<C: CurveAffine>(min_k: usize, max_k: usize) {
        use rayon::iter::{IntoParallelIterator, ParallelIterator};

        let points = (0..1 << max_k)
            .into_par_iter()
            .map(|_| C::Curve::random(OsRng))
            .collect::<Vec<_>>();
        let mut affine_points = vec![C::identity(); 1 << max_k];
        C::Curve::batch_normalize(&points[..], &mut affine_points[..]);
        let points = affine_points;

        let scalars = (0..1 << max_k)
            .into_par_iter()
            .map(|_| C::Scalar::random(OsRng))
            .collect::<Vec<_>>();

        for k in min_k..=max_k {
            let points = &points[..1 << k];
            let scalars = &scalars[..1 << k];

            let e0 = super::msm_best(scalars, points);
            let e1 = super::msm_parallel(scalars, points);
            assert_eq!(e0, e1);
        }
    }

    #[test]
    fn test_xyzz() {
        for n in [0, 1, 2, 31, 32, 33, 300, 1000] {
            let (scalars, points): (Vec<_>, Vec<_>) =
                (0..n).map(|_| (Fr::random(OsRng), G1Affine::random(OsRng))).unzip();
            let expected = super::msm_parallel(&scalars, &points);
            for c in [2, 4, 7, 11] {
                assert_eq!(
                    super::msm_with_window(&scalars, &points, c),
                    expected,
                    "n {n} c {c}"
                );
            }
        }
        // Repeated points and opposite scalars: the doubling and cancelling cases
        let p = G1Affine::random(OsRng);
        let s = Fr::random(OsRng);
        let points = vec![p; 64];
        let scalars: Vec<_> = (0..64).map(|i| if i % 2 == 0 { s } else { -s }).collect();
        assert_eq!(super::msm_with_window(&scalars, &points, 5), G1::identity());
        let scalars = vec![s; 64];
        assert_eq!(
            super::msm_with_window(&scalars, &points, 5),
            (p * s) * Fr::from(64)
        );
    }

    #[test]
    fn test_xyzz_batch_to_curve() {
        use super::Xyzz;
        let p = G1Affine::random(OsRng);
        let q = G1Affine::random(OsRng);
        let mut a = Xyzz::identity();
        a.add_affine(&p.x, &p.y, false);
        a.add_affine(&q.x, &q.y, true); // p - q, with ZZ, ZZZ != 1
        let mut b = Xyzz::identity();
        b.add_affine(&q.x, &q.y, false);
        b.add_affine(&q.x, &q.y, false); // 2q, by the doubling branch
        let points = [Xyzz::identity(), a, Xyzz::identity(), b, Xyzz::identity()];
        let expected = [G1::identity(), p - q, G1::identity(), q + q, G1::identity()];
        assert_eq!(Xyzz::batch_to_curve::<G1Affine>(&points), expected);
        assert!(Xyzz::<crate::bn256::Fq>::batch_to_curve::<G1Affine>(&[]).is_empty());
    }

    /// BLS12-381 G1's GLV constants match, and the MSM agrees
    #[test]
    fn test_glv() {
        use crate::{G1Affine as Bls, G1Projective};
        use ff::PrimeField;
        let (beta, lambda) = Bls::glv().unwrap();
        let p = G1Projective::random(OsRng).to_affine();
        let phi = Bls::from_xy(p.x() * beta, p.y()).unwrap();
        let lambda_s = crate::Fq::from_u128(lambda);
        assert_eq!(phi, (p * lambda_s).to_affine(), "β does not match λ");
        for n in [64, 65, 1000] {
            let (scalars, points): (Vec<_>, Vec<_>) = (0..n)
                .map(|_| {
                    (
                        crate::Fq::random(OsRng),
                        G1Projective::random(OsRng).to_affine(),
                    )
                })
                .unzip();
            let expected = Bls::multi_exp_affine(&points, &scalars);
            for c in [4, 8, 11] {
                assert_eq!(
                    super::msm_glv_with_window(&scalars, &points, c),
                    expected,
                    "n {n} c {c}"
                );
            }
        }
    }

    /// BLS12-381 G1 reads coordinates in place; identity bases (every fifth) must count as zero
    #[test]
    fn test_msm_in_place_with_identities() {
        use crate::{G1Affine as Bls, G1Projective};
        for n in [32, 33, 100, 1000] {
            let (scalars, points): (Vec<_>, Vec<_>) = (0..n)
                .map(|i| {
                    let p = if i % 5 == 0 {
                        <Bls as group::prime::PrimeCurveAffine>::identity()
                    } else {
                        G1Projective::random(OsRng).to_affine()
                    };
                    (crate::Fq::random(OsRng), p)
                })
                .unzip();
            let expected = scalars
                .iter()
                .zip(&points)
                .fold(G1Projective::identity(), |acc, (s, p)| acc + p * s);
            for c in [4, 9, 13] {
                assert_eq!(
                    super::msm_with_window(&scalars, &points, c),
                    expected,
                    "n {n} c {c}"
                );
            }
        }
    }

    /// No terms: the identity, through `CurveAffine::msm` (whichever backend)
    #[test]
    fn test_msm_empty() {
        use crate::{CurveAffine as _, G1Affine as Bls, G1Projective};
        assert_eq!(Bls::msm(&[], &[]), G1Projective::identity());
    }

    /// The fixed-base table agrees with the plain MSM, built at once or grown in steps, over
    /// any prefix of its bases, with identity bases among them
    #[test]
    fn test_fixed_bases() {
        use crate::{G1Affine as Bls, G1Projective};
        let n = 1500;
        let (scalars, points): (Vec<_>, Vec<_>) = (0..n)
            .map(|i| {
                let p = match i % 97 {
                    0 => <Bls as group::prime::PrimeCurveAffine>::identity(),
                    _ => G1Projective::random(OsRng).to_affine(),
                };
                (crate::Fq::random(OsRng), p)
            })
            .unzip();
        for c in [8, 11] {
            let whole = super::FixedBases::<Bls>::new(&points, c);
            let mut grown = super::FixedBases::<Bls>::new(&points[..700], c);
            grown.extend(&points[700..]);
            for m in [0, 31, 700, 1500] {
                let expected = super::msm_best(&scalars[..m], &points[..m]);
                assert_eq!(whole.msm(&scalars[..m]), expected, "c {c} m {m}");
                assert_eq!(grown.msm(&scalars[..m]), expected, "c {c} m {m} grown");
            }
        }
    }

    /// Many threads split the terms into chunks, and the scalar blocks end raggedly: every tile
    /// must still see each term exactly once
    #[test]
    fn test_msm_chunks_and_blocks() {
        use crate::{G1Affine as Bls, G1Projective};
        for n in [1000, 3000] {
            let (scalars, points): (Vec<_>, Vec<_>) = (0..n)
                .map(|_| {
                    (
                        crate::Fq::random(OsRng),
                        G1Projective::random(OsRng).to_affine(),
                    )
                })
                .unzip();
            let expected = scalars
                .iter()
                .zip(&points)
                .fold(G1Projective::identity(), |acc, (s, p)| acc + p * s);
            for threads in [16, 64] {
                let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
                for c in [4, 8, 13, 16] {
                    let got = pool.install(|| super::msm_with_window::<Bls>(&scalars, &points, c));
                    assert_eq!(got, expected, "n {n} threads {threads} c {c}");
                }
            }
        }
    }

    /// Repeated and negated bases: batched affine additions that would double or cancel a
    /// bucket must take the XYZZ route
    #[test]
    fn test_msm_repeated_and_negated_bases() {
        use crate::{G1Affine as Bls, G1Projective};
        let p = G1Projective::random(OsRng).to_affine();
        let q = G1Projective::random(OsRng).to_affine();
        for n in [300, 2000] {
            let points: Vec<Bls> = (0..n).map(|i| [p, -p, q, p][i % 4]).collect();
            // Few distinct scalars, so buckets meet the same point again and again
            let scalars: Vec<_> = (0..n).map(|i| crate::Fq::from([3, 5, 1 << 40][i % 3])).collect();
            let expected = scalars
                .iter()
                .zip(&points)
                .fold(G1Projective::identity(), |acc, (s, p)| acc + p * s);
            for c in [4, 7, 8, 10, 13] {
                assert_eq!(
                    super::msm_with_window(&scalars, &points, c),
                    expected,
                    "n {n} c {c}"
                );
            }
        }
    }

    /// The split is exact, `k1 + k2·λ = k` with `k1 < λ`, on edge cases and at random
    #[test]
    fn test_glv_split() {
        use crate::G1Affine as Bls;
        use ff::PrimeField;
        let (_, lambda) = Bls::glv().unwrap();
        let m = super::glv_reciprocal(lambda);
        let l = crate::Fq::from_u128(lambda);
        let mut ks = vec![
            crate::Fq::ZERO,
            crate::Fq::ONE,
            -crate::Fq::ONE,
            l,
            l - crate::Fq::ONE,
            l + crate::Fq::ONE,
            l * l,
            l * l + l,
        ];
        ks.extend((0..10_000).map(|_| crate::Fq::random(OsRng)));
        for k in ks {
            let (k1, k2) = super::glv_split(k.to_repr().as_ref(), lambda, &m);
            let (k1, k2) = (u128::from_le_bytes(k1), u128::from_le_bytes(k2));
            assert!(k1 < lambda, "k1 not below λ for {k:?}");
            assert_eq!(crate::Fq::from_u128(k1) + crate::Fq::from_u128(k2) * l, k);
        }
    }

    #[test]
    fn test_msm_cross() {
        run_msm_cross::<G1Affine>(14, 18);
    }
}

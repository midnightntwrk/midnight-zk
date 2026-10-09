use std::{
    convert::TryInto,
    ops::{Neg, Range},
};

use ff::{Field, PrimeField};
use group::Group;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator,
};

use crate::{CurveAffine, FieldInto};

const BATCH_SIZE: usize = 64;

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
    for (dst, src) in v.iter_mut().zip(el.iter().skip(skip_bytes)) {
        *dst = *src
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

/// Batch addition.
fn batch_add<C: CurveAffine>(
    size: usize,
    buckets: &mut [BucketAffine<C>],
    points: &[SchedulePoint],
    bases: &[Affine<C>],
) {
    // We are assuming a=0 in the doubling formula.
    debug_assert_eq!(C::a(), C::Base::ZERO);

    let mut t = vec![C::Base::ZERO; size]; // Stores x2 - x1
    let mut z = vec![C::Base::ZERO; size]; // Stores y2 - y1
    let mut acc = C::Base::ONE;

    for (
        (
            SchedulePoint {
                base_idx,
                buck_idx,
                sign,
            },
            t,
        ),
        z,
    ) in points.iter().zip(t.iter_mut()).zip(z.iter_mut())
    {
        if buckets[*buck_idx].is_inf() {
            // We assume bases[*base_idx] != infinity always.
            continue;
        }

        if buckets[*buck_idx].x() == bases[*base_idx].x {
            // y-coordinate matches:
            //  1. y1 == y2 and sign = false or
            //  2. y1 != y2 and sign = true
            //  => ( y1 == y2) xor !sign
            //  (This uses the fact that x1 == x2 and both points satisfy the curve eq.)
            if (buckets[*buck_idx].y() == bases[*base_idx].y) ^ !*sign {
                // Doubling
                let x_squared = bases[*base_idx].x.square();
                *z = buckets[*buck_idx].y() + buckets[*buck_idx].y(); // 2y
                *t = acc * (x_squared + x_squared + x_squared); // acc * 3x^2
                acc *= *z;
                continue;
            }
            // P + (-P)
            buckets[*buck_idx].set_inf();
            continue;
        }
        // Addition
        *z = buckets[*buck_idx].x() - bases[*base_idx].x; // x2 - x1
        if *sign {
            *t = acc * (buckets[*buck_idx].y() - bases[*base_idx].y);
        } else {
            *t = acc * (buckets[*buck_idx].y() + bases[*base_idx].y);
        } // y2 - y1
        acc *= *z;
    }

    acc = acc.invert().expect("Some edge case has not been handled properly");

    for (
        (
            SchedulePoint {
                base_idx,
                buck_idx,
                sign,
            },
            t,
        ),
        z,
    ) in points.iter().zip(t.iter()).zip(z.iter()).rev()
    {
        if buckets[*buck_idx].is_inf() {
            // We assume bases[*base_idx] != infinity always.
            continue;
        }
        let lambda = acc * t;
        acc *= z; // update acc
        let x = lambda.square() - (buckets[*buck_idx].x() + bases[*base_idx].x); // x_result
        if *sign {
            buckets[*buck_idx].set_y(&((lambda * (bases[*base_idx].x - x)) - bases[*base_idx].y));
        } else {
            buckets[*buck_idx].set_y(&((lambda * (bases[*base_idx].x - x)) + bases[*base_idx].y));
        } // y_result = lambda * (x1 - x_result) - y1
        buckets[*buck_idx].set_x(&x);
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
    fn from(point: &C) -> Self {
        let coords = point.coordinates().unwrap();

        Self {
            x: *coords.x(),
            y: *coords.y(),
        }
    }

    fn neg(&self) -> Self {
        Self {
            x: self.x,
            y: -self.y,
        }
    }

    /// A bucket's sum of input points: on the curve and in their subgroup, so unchecked
    fn eval(&self) -> C {
        C::from_xy_unchecked(self.x, self.y)
    }
}

#[derive(Debug, Clone)]
enum BucketAffine<C: CurveAffine> {
    None,
    Point(Affine<C>),
}

#[derive(Debug, Clone)]
enum Bucket<C: CurveAffine> {
    None,
    Point(C::Curve),
}

impl<C: CurveAffine> Bucket<C> {
    fn add_assign(&mut self, point: &C, sign: bool) {
        *self = match *self {
            Bucket::None => Bucket::Point({
                if sign {
                    point.to_curve()
                } else {
                    point.to_curve().neg()
                }
            }),
            Bucket::Point(a) => {
                if sign {
                    Self::Point(a + point)
                } else {
                    Self::Point(a - point)
                }
            }
        }
    }

    fn add(&self, other: &BucketAffine<C>) -> C::Curve {
        match (self, other) {
            (Self::Point(this), BucketAffine::Point(other)) => *this + other.eval(),
            (Self::Point(this), BucketAffine::None) => *this,
            (Self::None, BucketAffine::Point(other)) => other.eval().to_curve(),
            (Self::None, BucketAffine::None) => C::Curve::identity(),
        }
    }
}

impl<C: CurveAffine> BucketAffine<C> {
    fn assign(&mut self, point: &Affine<C>, sign: bool) -> bool {
        match *self {
            Self::None => {
                *self = Self::Point(if sign { *point } else { point.neg() });
                true
            }
            Self::Point(_) => false,
        }
    }

    fn x(&self) -> C::Base {
        match self {
            Self::None => panic!("::x None"),
            Self::Point(a) => a.x,
        }
    }

    fn y(&self) -> C::Base {
        match self {
            Self::None => panic!("::y None"),
            Self::Point(a) => a.y,
        }
    }

    fn is_inf(&self) -> bool {
        match self {
            Self::None => true,
            Self::Point(_) => false,
        }
    }

    fn set_x(&mut self, x: &C::Base) {
        match self {
            Self::None => panic!("::set_x None"),
            Self::Point(a) => a.x = *x,
        }
    }

    fn set_y(&mut self, y: &C::Base) {
        match self {
            Self::None => panic!("::set_y None"),
            Self::Point(a) => a.y = *y,
        }
    }

    fn set_inf(&mut self) {
        match self {
            Self::None => {}
            Self::Point(_) => *self = Self::None,
        }
    }
}

struct Schedule<C: CurveAffine> {
    buckets: Vec<BucketAffine<C>>,
    set: [SchedulePoint; BATCH_SIZE],
    ptr: usize,
}

#[derive(Debug, Clone, Default)]
struct SchedulePoint {
    base_idx: usize,
    buck_idx: usize,
    sign: bool,
}

impl SchedulePoint {
    fn new(base_idx: usize, buck_idx: usize, sign: bool) -> Self {
        Self {
            base_idx,
            buck_idx,
            sign,
        }
    }
}

impl<C: CurveAffine> Schedule<C> {
    fn new(c: usize) -> Self {
        let set = (0..BATCH_SIZE)
            .map(|_| SchedulePoint::default())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        Self {
            buckets: vec![BucketAffine::None; 1 << (c - 1)],
            set,
            ptr: 0,
        }
    }

    fn contains(&self, buck_idx: usize) -> bool {
        self.set[..self.ptr].iter().any(|sch| sch.buck_idx == buck_idx)
    }

    fn execute(&mut self, bases: &[Affine<C>]) {
        if self.ptr != 0 {
            batch_add(self.ptr, &mut self.buckets, &self.set, bases);
            self.ptr = 0;
            self.set.iter_mut().for_each(|sch| *sch = SchedulePoint::default());
        }
    }

    fn add(&mut self, bases: &[Affine<C>], base_idx: usize, buck_idx: usize, sign: bool) {
        if !self.buckets[buck_idx].assign(&bases[base_idx], sign) {
            self.set[self.ptr] = SchedulePoint::new(base_idx, buck_idx, sign);
            self.ptr += 1;
        }

        if self.ptr == self.set.len() {
            self.execute(bases);
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

    // Variable time: which buckets are touched depends on the scalars anyway
    fn is_identity(&self) -> bool {
        self.zz.is_zero_vartime() && self.zzz.is_zero_vartime()
    }

    /// `self += (x2, y2)`, or `-= ` if `negate`, for an affine point `(x2, y2)` on the curve
    /// (EFD madd-2008-s, and mdbl-2008-s-1 when the points are equal). Like blst, every result
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
            self.x = *x2;
            self.y = *y2;
            self.zz = F::ONE;
            self.zzz = F::ONE;
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
            // Equal points: double (x2, y2)
            let mut u = F::ZERO;
            F::add_into(&mut u, y2, y2);
            F::square_into(&mut self.zz, &u); // V
            F::mul_into(&mut self.zzz, &self.zz, &u); // W
            let mut s = F::ZERO;
            F::mul_into(&mut s, x2, &self.zz);
            let mut x2sq = F::ZERO;
            F::square_into(&mut x2sq, x2);
            let mut m = F::ZERO;
            F::add_into(&mut m, &x2sq, &x2sq);
            m += &x2sq;
            F::square_into(&mut self.x, &m);
            self.x -= &s;
            self.x -= &s;
            s -= &self.x;
            s *= &m;
            F::mul_into(&mut self.y, &self.zzz, y2);
            F::rsub_assign(&mut self.y, &s);
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

/// One scalar multiplication per term, in parallel, then their sum: best for a few terms
#[doc(hidden)]
pub fn msm_pointwise<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    coeffs
        .par_iter()
        .zip(bases.par_iter())
        .map(|(s, b)| b.to_curve() * s)
        .reduce(C::Curve::identity, |a, b| a + b)
}

/// Pippenger with XYZZ buckets (blst's design), parallel over tiles of windows × chunks of
/// the terms; window size `c`. Below 32 terms, one scalar multiplication per term instead.
#[doc(hidden)]
pub fn msm_xyzz_with_window<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    c: usize,
) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    if coeffs.len() < 32 {
        return msm_pointwise(coeffs, bases);
    }
    let nbits = C::Scalar::NUM_BITS as usize;
    if bases.first().is_some_and(|b| b.xy_ref().is_some()) {
        // Coordinates read in place, scalars converted by the tiles as they need them; an
        // identity base gets a zero scalar, so it is never added
        let zero = C::Scalar::ZERO.to_repr();
        let repr = |r: Range<usize>| {
            let repr = |i: usize| match bool::from(bases[i].is_identity()) {
                true => zero,
                false => coeffs[i].to_repr(),
            };
            r.map(repr).collect()
        };
        let xy = |i: usize| bases[i].xy_ref().unwrap();
        return msm_xyzz_core::<C, _, _, _>(coeffs.len(), repr, xy, nbits, c);
    }
    // In parallel only when there is enough work to pay for the scheduling
    let par = coeffs.len() >= 1 << 12;
    let prepare = |(s, b): (&C::Scalar, &C)| (s.to_repr(), Affine::from(b));
    let not_identity = |(_, b): &(&C::Scalar, &C)| !bool::from(b.is_identity());
    let (scalars, points): (Vec<_>, Vec<_>) = if par {
        coeffs
            .par_iter()
            .zip(bases.par_iter())
            .filter(not_identity)
            .map(prepare)
            .unzip()
    } else {
        coeffs.iter().zip(bases).filter(not_identity).map(prepare).unzip()
    };
    let repr = |r: Range<usize>| scalars[r].to_vec();
    msm_xyzz_core::<C, _, _, _>(
        scalars.len(),
        repr,
        |i| (&points[i].x, &points[i].y),
        nbits,
        c,
    )
}

/// `k = k2·λ + k1` with `k1 < λ`, for a little-endian `k < 2^128 λ`: the GLV halves,
/// little-endian
#[doc(hidden)]
pub fn glv_split(k: &[u8], lambda: u128) -> ([u8; 16], [u8; 16]) {
    let mut bytes = [0u8; 32];
    bytes[..k.len()].copy_from_slice(k);
    let lo = u128::from_le_bytes(bytes[..16].try_into().unwrap());
    let hi = u128::from_le_bytes(bytes[16..].try_into().unwrap());
    debug_assert!(hi < lambda, "scalar too large to split");
    // Long division of (hi, lo) by λ, a bit at a time; the remainder stays below λ
    let (mut rem, mut q) = (hi, 0u128);
    for i in (0..128).rev() {
        let carry = rem >> 127;
        rem = (rem << 1) | ((lo >> i) & 1);
        q <<= 1;
        if carry == 1 || rem >= lambda {
            rem = rem.wrapping_sub(lambda);
            q |= 1;
        }
    }
    (rem.to_le_bytes(), q.to_le_bytes())
}

/// `⌊2^256 / λ⌋` as little-endian limbs (129 bits for a 128-bit `λ`), by long division:
/// the Barrett constant for [`glv_split_fast`]
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

/// [`glv_split`] by Barrett reduction with `m = glv_reciprocal(λ)`: `(k·m) >> 256` is at most
/// 2 below `⌊k/λ⌋`, and the remainder is corrected by subtracting `λ`
#[doc(hidden)]
pub fn glv_split_fast(k: &[u8], lambda: u128, m: &[u64; 3]) -> ([u8; 16], [u8; 16]) {
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

/// [`msm_xyzz_with_window`] through a GLV endomorphism ([`CurveAffine::glv`]): twice the terms,
/// with 128-bit scalars, so half the windows and doublings.
#[doc(hidden)]
pub fn msm_xyzz_glv_with_window<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    c: usize,
) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    let Some((beta, lambda)) = C::glv() else {
        return msm_xyzz_with_window(coeffs, bases, c);
    };
    let m = glv_reciprocal(lambda);
    if coeffs.len() < 32 {
        return msm_pointwise(coeffs, bases);
    }
    let not_identity = |(_, b): &(&C::Scalar, &C)| !bool::from(b.is_identity());
    let split = |(s, b): (&C::Scalar, &C)| {
        let (k1, k2) = glv_split_fast(s.to_repr().as_ref(), lambda, &m);
        let p = Affine::from(b);
        let phi = Affine {
            x: p.x * beta,
            y: p.y,
        };
        [(k1, p), (k2, phi)]
    };
    let (scalars, points): (Vec<[u8; 16]>, Vec<Affine<C>>) = if coeffs.len() < 1 << 12 {
        coeffs.iter().zip(bases).filter(not_identity).flat_map(split).unzip()
    } else {
        coeffs
            .par_iter()
            .zip(bases.par_iter())
            .filter(not_identity)
            .flat_map_iter(split)
            .unzip()
    };
    let repr = |r: Range<usize>| scalars[r].to_vec();
    msm_xyzz_core::<C, _, _, _>(
        scalars.len(),
        repr,
        |i| (&points[i].x, &points[i].y),
        128,
        c,
    )
}

/// The XYZZ Pippenger's window size for `n` terms, measured on BLS12-381 G1
/// (`examples/msm_tune.rs` sweeps it): x86-64 on a Ryzen 5950X (32 threads), aarch64 on an
/// Apple M3 Max (12 performance and 4 efficiency cores), which wants wider windows.
#[doc(hidden)]
pub fn xyzz_window(n: usize) -> usize {
    let k = n.max(1).ilog2();
    if cfg!(target_arch = "aarch64") {
        match k {
            0..=5 => 5,
            6 => 5,
            7..=8 => 6,
            9 => 7,
            10 => 8,
            11 => 10,
            12 => 11,
            13 => 10,
            14..=15 => 11,
            16 => 12,
            _ => 13,
        }
    } else {
        match k {
            0..=5 => 5,
            6 => 4,
            7..=8 => 5,
            9 => 6,
            10..=14 => 9,
            15 => 10,
            _ => 13,
        }
    }
}

/// The point-chunk count for window size `c`: the least cost, as parallel rounds times one
/// tile's work (its bucket additions, then summing its buckets); chunks of the terms give
/// more tiles when there are fewer windows than threads, as in blst's `breakdown`
fn xyzz_chunks(n: usize, nbits: usize, c: usize, threads: usize) -> usize {
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

/// Scalars converted together by [`msm_xyzz_core`]'s tiles
const SCALAR_BLOCK: usize = 256;

/// The XYZZ Pippenger over `n` affine points `xy(i)` (none the identity) and little-endian
/// scalars of `nbits` bits, `repr(range)` giving those in `range`.
///
/// The scalars are converted lazily, a block at a time, by whichever tile first needs a block,
/// so the conversion runs in parallel with no fork-join of its own. Each tile visits its
/// blocks starting at its own offset, so the first tiles, which start together, convert
/// different blocks rather than queue on one.
fn msm_xyzz_core<'a, C: CurveAffine, S: AsRef<[u8]> + Send + Sync, R, XY>(
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
    let chunks = xyzz_chunks(n, nbits, c, threads);
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
    rayon::in_place_scope(|scope| {
        for _ in 0..threads.min(tiles) {
            let done_tx = done_tx.clone();
            let (results, pending, next, xy) = (&results, &pending, &next, &xy);
            let (blocks, repr) = (&blocks, &repr);
            scope.spawn(move |_| {
                let mut buckets = vec![Xyzz::identity(); 1 << (c - 1)];
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
                                let (x, y) = xy(i);
                                buckets[d.unsigned_abs() as usize - 1].add_affine(x, y, d < 0);
                            }
                        }
                    }
                    let _ = results[t].set(integrate_and_clear(&mut buckets[..used]));
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
    let c = if bases.len() < 4 {
        1
    } else if bases.len() < 32 {
        3
    } else {
        (f64::from(bases.len() as u32)).ln().ceil() as usize
    };
    msm_serial_with_window(coeffs, bases, acc, c)
}

/// [`msm_serial`] with window size `c`
#[doc(hidden)]
pub fn msm_serial_with_window<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    acc: &mut C::Curve,
    c: usize,
) {
    let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();

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

/// The multi-scalar multiplication `Σ coeffs[i]·bases[i]`: an XYZZ-bucket Pippenger, through
/// the GLV endomorphism ([`CurveAffine::glv`]) for 32..128 terms, and one scalar
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
        return msm_xyzz_glv_with_window(coeffs, bases, 5);
    }
    msm_xyzz_with_window(coeffs, bases, xyzz_window(bases.len()))
}

/// The previous [`msm_best`]: a batch-affine Pippenger with window size `c`, parallel over
/// the windows; kept for comparison
#[doc(hidden)]
pub fn msm_batch_affine_with_window<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    c: usize,
) -> C::Curve {
    // Filter out identities. Transform scalars to bytes and bases to affine.
    let (coeffs, (bases, bases_local)): (Vec<_>, (Vec<_>, Vec<_>)) = coeffs
        .par_iter()
        .zip(bases.par_iter())
        .filter(|(_, b)| !bool::from(b.is_identity()))
        .map(|(c, b)| (c.to_repr(), (*b, Affine::from(b))))
        .unzip();

    // number of windows
    let number_of_windows = C::Scalar::NUM_BITS as usize / c + 1;
    // accumumator for each window
    let mut acc = vec![C::Curve::identity(); number_of_windows];
    acc.par_iter_mut().enumerate().for_each(|(w, acc)| {
        // jacobian buckets for already scheduled points
        let mut j_bucks = vec![Bucket::<C>::None; 1 << (c - 1)];

        // schedular for affine addition
        let mut sched = Schedule::new(c);

        for (base_idx, coeff) in coeffs.iter().enumerate() {
            let buck_idx = get_booth_index(w, c, coeff.as_ref());

            if buck_idx != 0 {
                // parse bucket index
                let sign = buck_idx.is_positive();
                let buck_idx = buck_idx.unsigned_abs() as usize - 1;

                if sched.contains(buck_idx) {
                    // greedy accumulation
                    j_bucks[buck_idx].add_assign(&bases[base_idx], sign);
                } else {
                    // also flushes the schedule if full
                    sched.add(&bases_local, base_idx, buck_idx, sign);
                }
            }
        }

        // flush the schedule
        sched.execute(&bases_local);

        // summation by parts
        // e.g. 3a + 2b + 1c = a +
        //                    (a) + b +
        //                    ((a) + b) + c
        let mut running_sum = C::Curve::identity();
        for (j_buck, a_buck) in j_bucks.iter().zip(sched.buckets.iter()).rev() {
            running_sum += j_buck.add(a_buck);
            *acc += running_sum;
        }
    });
    // Horner's rule over the windows, most significant first: `c` doublings between
    // windows, 256 in all, instead of shifting each window by `c·w` doublings
    acc.into_iter().rev().fold(C::Curve::identity(), |sum, window| {
        (0..c).fold(sum, |sum, _| sum.double()) + window
    })
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
                    super::msm_xyzz_with_window(&scalars, &points, c),
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
        assert_eq!(
            super::msm_xyzz_with_window(&scalars, &points, 5),
            G1::identity()
        );
        let scalars = vec![s; 64];
        assert_eq!(
            super::msm_xyzz_with_window(&scalars, &points, 5),
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

    /// BLS12-381 G1's GLV constants match, `glv_split` is exact, and the MSM agrees
    #[test]
    fn test_glv() {
        use crate::{G1Affine as Bls, G1Projective};
        use ff::PrimeField;
        let (beta, lambda) = Bls::glv().unwrap();
        let p = G1Projective::random(OsRng).to_affine();
        let phi = Bls::from_xy(p.x() * beta, p.y()).unwrap();
        let lambda_s = crate::Fq::from_u128(lambda);
        assert_eq!(phi, (p * lambda_s).to_affine(), "β does not match λ");
        for k in [
            crate::Fq::ZERO,
            crate::Fq::ONE,
            -crate::Fq::ONE,
            crate::Fq::random(OsRng),
        ] {
            let (k1, k2) = super::glv_split(k.to_repr().as_ref(), lambda);
            let (k1, k2) = (u128::from_le_bytes(k1), u128::from_le_bytes(k2));
            assert!(k1 < lambda);
            assert_eq!(
                crate::Fq::from_u128(k1) + crate::Fq::from_u128(k2) * lambda_s,
                k
            );
        }
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
                    super::msm_xyzz_glv_with_window(&scalars, &points, c),
                    expected,
                    "n {n} c {c}"
                );
            }
        }
    }

    /// BLS12-381 G1 reads coordinates in place; identity bases (every fifth) must count as zero
    #[test]
    fn test_xyzz_in_place_with_identities() {
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
                    super::msm_xyzz_with_window(&scalars, &points, c),
                    expected,
                    "n {n} c {c}"
                );
            }
        }
    }

    /// Many threads split the terms into chunks, and the scalar blocks end raggedly: every tile
    /// must still see each term exactly once
    #[test]
    fn test_xyzz_chunks_and_blocks() {
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
                    let got =
                        pool.install(|| super::msm_xyzz_with_window::<Bls>(&scalars, &points, c));
                    assert_eq!(got, expected, "n {n} threads {threads} c {c}");
                }
            }
        }
    }

    /// The Barrett split agrees with the long division, on edge cases and at random
    #[test]
    fn test_glv_split_fast() {
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
            let r = k.to_repr();
            assert_eq!(
                super::glv_split_fast(r.as_ref(), lambda, &m),
                super::glv_split(r.as_ref(), lambda)
            );
        }
    }

    #[test]
    fn test_msm_cross() {
        run_msm_cross::<G1Affine>(14, 18);
    }
}

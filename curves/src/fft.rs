use std::any::TypeId;

use ff::Field;
use group::{GroupOpsOwned, ScalarMulOwned};

use crate::bls12_381::Fq;
pub use crate::{CurveAffine, CurveExt};

/// This represents an element of a group with basic operations that can be
/// performed. This allows an FFT implementation (for example) to operate
/// generically over either a field or elliptic curve group.
pub trait FftGroup<Scalar: Field>:
    Copy + Send + Sync + 'static + GroupOpsOwned + ScalarMulOwned<Scalar>
{
}

impl<T, Scalar> FftGroup<Scalar> for T
where
    Scalar: Field,
    T: Copy + Send + Sync + 'static + GroupOpsOwned + ScalarMulOwned<Scalar>,
{
}

/// Reverse the low `log_n` bits of `n`. Requires `log_n > 0`.
fn bitreverse(n: usize, log_n: u32) -> usize {
    n.reverse_bits() >> (usize::BITS - log_n)
}

/// Precompute twiddle factors `[1, ω, ω², …, ω^(n/2 - 1)]` for an FFT of size
/// `2^log_n`.
pub fn compute_twiddles<Scalar: Field>(omega: &Scalar, log_n: u32) -> Vec<Scalar> {
    let half_n = 1usize << (log_n - 1);
    let mut twiddles = Vec::with_capacity(half_n);
    let mut w = Scalar::ONE;
    for _ in 0..half_n {
        twiddles.push(w);
        w *= omega;
    }
    twiddles
}

/// Performs a radix-2 Fast-Fourier Transformation (FFT) on a vector of size
/// `n = 2^log_n`. Interprets `a` as the coefficients of a polynomial of degree
/// `n - 1` and transforms it into evaluations at each of the `n` distinct
/// powers of `omega`. This transformation is invertible by providing `ω⁻¹` in
/// place of `ω` and dividing each resulting element by `n`.
///
/// Uses multithreading if beneficial.
pub fn best_fft<Scalar: Field, G: FftGroup<Scalar>>(a: &mut [G], omega: Scalar, log_n: u32) {
    let twiddles = compute_twiddles(&omega, log_n);
    best_fft_with_twiddles(a, &twiddles, log_n);
}

/// Same as [`best_fft`] but uses precomputed twiddle factors.
/// Use [`compute_twiddles`] to generate the twiddle array.
pub fn best_fft_with_twiddles<Scalar: Field, G: FftGroup<Scalar>>(
    a: &mut [G],
    twiddles: &[Scalar],
    log_n: u32,
) {
    let n = a.len();
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk, k);
        }
    }

    let log_threads = rayon::current_num_threads().ilog2();
    if log_n <= log_threads {
        let mut chunk = 2_usize;
        let mut twiddle_chunk = n / 2;
        for _ in 0..log_n {
            a.chunks_mut(chunk).for_each(|coeffs| {
                let (left, right) = coeffs.split_at_mut(chunk / 2);

                // Case when twiddle factor is one.
                let (a, left) = left.split_at_mut(1);
                let (b, right) = right.split_at_mut(1);
                let t = b[0];
                b[0] = a[0];
                a[0] += &t;
                b[0] -= &t;

                left.iter_mut().zip(right.iter_mut()).enumerate().for_each(|(i, (a, b))| {
                    let mut t = *b;
                    t *= &twiddles[(i + 1) * twiddle_chunk];
                    *b = *a;
                    *a += &t;
                    *b -= &t;
                });
            });
            chunk *= 2;
            twiddle_chunk /= 2;
        }
    } else {
        recursive_butterfly_arithmetic(a, n, 1, twiddles)
    }
}

/// FFT for the `coeff_to_extended` pattern: the first `n_real` entries of `a`
/// hold coefficients and the rest are zero-padded out to `2^log_n`. Exploits
/// the zero-padded structure to skip butterfly work on all-zero subtrees.
///
/// Uses pruned DIF (Gentleman-Sande) when `G` is the BLS12-381 scalar field
/// [`Fq`]; falls back to standard DIT for other fields. The TypeId check is
/// monomorphized to a constant — zero runtime cost.
pub fn fft_coeff_to_extended<Scalar: Field, G: FftGroup<Scalar>>(
    a: &mut [G],
    twiddles: &[Scalar],
    log_n: u32,
    n_real: usize,
) {
    if TypeId::of::<G>() == TypeId::of::<Fq>() && TypeId::of::<Scalar>() == TypeId::of::<Fq>() {
        // SAFETY: G == Fq == Scalar verified by TypeId. Fq is #[repr(transparent)].
        let a = unsafe { &mut *(a as *mut [G] as *mut [Fq]) };
        let tw = unsafe { &*(twiddles as *const [Scalar] as *const [Fq]) };
        fft_dif_pruned_fq(a, tw, log_n, n_real);
    } else {
        best_fft_with_twiddles(a, twiddles, log_n);
    }
}

/// Pruned DIF (Gentleman-Sande) FFT for zero-padded input. `a[0..n_real]` are
/// data, `a[n_real..n]` are zero.
///
/// DIF does large-stride butterflies first (on cold data) and small-stride
/// last (leaving data warm for the final bit-reversal). The pruning skips
/// butterflies whose operands are both zero and replaces `(data, 0)`
/// butterflies with a single multiply.
fn fft_dif_pruned_fq(a: &mut [Fq], twiddles: &[Fq], log_n: u32, n_real: usize) {
    let n = a.len();
    assert_eq!(n, 1 << log_n);
    recursive_dif_pruned(a, n, 1, twiddles, n_real);
    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk, k);
        }
    }
}

/// Recursive DIF butterflies assuming the first `nz` entries of `a` are
/// potentially non-zero and the remaining `n - nz` are zero. Maintains this
/// "data-at-front" invariant across recursive calls.
fn recursive_dif_pruned(a: &mut [Fq], n: usize, tc: usize, tw: &[Fq], nz: usize) {
    if nz == 0 {
        return;
    }
    if n == 2 {
        // Base case. GS butterfly on (a[0], a[1]). Correct whether a[1] is
        // zero (nz == 1) or not, since (a, 0; tw) → (a, a·tw).
        gs(a, 0, 1, &tw[0]);
        return;
    }

    let h = n / 2;

    if nz <= h {
        // Right half is entirely zero. The GS butterfly (a, 0; tw) simplifies
        // to (a, a·tw): the low half keeps a[i], the high half becomes a[i]·tw.
        // The tail of the left half stays zero.
        for i in 0..nz {
            a[i + h] = a[i];
            a[i + h] *= &tw[i * tc];
        }
    } else {
        // Both halves carry data. Full butterflies across the split. Pairs
        // with i >= nz - h have a[i+h] == 0, which the butterfly still
        // handles correctly (one extra mul each; not worth a special case).
        for i in 0..h {
            gs(a, i, i + h, &tw[i * tc]);
        }
    }

    // After the split, each half holds exactly `min(nz, h)` potentially
    // non-zero entries, placed at the front.
    let child_nz = nz.min(h);
    let (left, right) = a.split_at_mut(h);
    rayon::join(
        || recursive_dif_pruned(left, h, tc * 2, tw, child_nz),
        || recursive_dif_pruned(right, h, tc * 2, tw, child_nz),
    );
}

/// In-place Gentleman-Sande butterfly on `a[i]` and `a[j]` with twiddle `t`:
/// (a[i], a[j]) ← (a[i] + a[j], (a[i] - a[j])·t).
#[inline(always)]
fn gs(a: &mut [Fq], i: usize, j: usize, t: &Fq) {
    // SAFETY: i != j and both in bounds — callers always supply i = k, j = k + h
    // with k < h <= a.len()/2.
    unsafe {
        let p = a.as_mut_ptr();
        Fq::gs_butterfly(&mut *p.add(i), &mut *p.add(j), t);
    }
}

/// Recursive Cooley-Tukey (DIT) butterflies. Used by [`best_fft_with_twiddles`]
/// when the FFT size exceeds the available parallelism.
pub fn recursive_butterfly_arithmetic<Scalar: Field, G: FftGroup<Scalar>>(
    a: &mut [G],
    n: usize,
    twiddle_chunk: usize,
    twiddles: &[Scalar],
) {
    if n == 2 {
        let t = a[1];
        a[1] = a[0];
        a[0] += &t;
        a[1] -= &t;
    } else {
        let (left, right) = a.split_at_mut(n / 2);
        rayon::join(
            || recursive_butterfly_arithmetic(left, n / 2, twiddle_chunk * 2, twiddles),
            || recursive_butterfly_arithmetic(right, n / 2, twiddle_chunk * 2, twiddles),
        );

        // Case when twiddle factor is one.
        let (a, left) = left.split_at_mut(1);
        let (b, right) = right.split_at_mut(1);
        let t = b[0];
        b[0] = a[0];
        a[0] += &t;
        b[0] -= &t;

        left.iter_mut().zip(right.iter_mut()).enumerate().for_each(|(i, (a, b))| {
            let mut t = *b;
            t *= &twiddles[(i + 1) * twiddle_chunk];
            *b = *a;
            *a += &t;
            *b -= &t;
        });
    }
}

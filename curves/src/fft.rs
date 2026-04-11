use ff::Field;
use group::{GroupOpsOwned, ScalarMulOwned};

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

/// Performs a radix-$2$ Fast-Fourier Transformation (FFT) on a vector of size
/// $n = 2^k$, when provided `log_n` = $k$ and an element of multiplicative
/// order $n$ called `omega` ($\omega$). The result is that the vector `a`, when
/// interpreted as the coefficients of a polynomial of degree $n - 1$, is
/// transformed into the evaluations of this polynomial at each of the $n$
/// distinct powers of $\omega$. This transformation is invertible by providing
/// $\omega^{-1}$ in place of $\omega$ and dividing each resulting field element
/// by $n$.
///
/// This will use multithreading if beneficial.
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
    fn bitreverse(mut n: usize, l: usize) -> usize {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    let threads = rayon::current_num_threads();
    let log_threads = threads.ilog2();
    let n = a.len();
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n as usize);
        if k < rk {
            a.swap(rk, k);
        }
    }

    if log_n <= log_threads {
        let mut chunk = 2_usize;
        let mut twiddle_chunk = n / 2;
        for _ in 0..log_n {
            a.chunks_mut(chunk).for_each(|coeffs| {
                let (left, right) = coeffs.split_at_mut(chunk / 2);

                // case when twiddle factor is one
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

/// FFT for the coeff_to_extended pattern (zero-padded n_real → extended_len).
/// Routes to pruned DIF when `G` is `Fq`, falls back to standard DIT otherwise.
/// The TypeId check is monomorphized to a constant — zero runtime cost.
pub fn fft_coeff_to_extended<Scalar: Field, G: FftGroup<Scalar>>(
    a: &mut [G],
    twiddles: &[Scalar],
    log_n: u32,
    n_real: usize,
) {
    use std::any::TypeId;
    if TypeId::of::<G>() == TypeId::of::<crate::bls12_381::Fq>() {
        // Safety: G == Fq verified by TypeId. Fq is #[repr(transparent)].
        let a = unsafe { &mut *(a as *mut [G] as *mut [crate::bls12_381::Fq]) };
        let tw = unsafe { &*(twiddles as *const [Scalar] as *const [crate::bls12_381::Fq]) };
        fft_dif_pruned_fq(a, tw, log_n, n_real);
    } else {
        best_fft_with_twiddles(a, twiddles, log_n);
    }
}

/// DIF (Gentleman-Sande) FFT with bit-reversal output.
/// Uses `Fq::gs_butterfly` for the fused DIF butterfly.
///
/// DIF does large-stride butterflies first (on cold data) and small-stride
/// last (leaving data warm for the final bit-reversal). This gives -8% to -14%
/// over DIT on typical prover workloads.
pub fn fft_dif_fq(a: &mut [crate::bls12_381::Fq], twiddles: &[crate::bls12_381::Fq], log_n: u32) {
    fn bitreverse(mut n: usize, l: usize) -> usize {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }
    let n = a.len();
    assert_eq!(n, 1 << log_n);
    recursive_dif(a, n, 1, twiddles);
    for k in 0..n {
        let rk = bitreverse(k, log_n as usize);
        if k < rk {
            a.swap(rk, k);
        }
    }
}

/// Pruned DIF FFT for zero-padded input (first `n_real` elements are data,
/// rest are zeros). Skips butterfly work on all-zero subtrees and uses
/// simplified merges when one half is entirely zero.
///
/// Gives -18% to -24% on coeff_to_extended workloads (zero-padded n → 4n).
pub fn fft_dif_pruned_fq(
    a: &mut [crate::bls12_381::Fq],
    twiddles: &[crate::bls12_381::Fq],
    log_n: u32,
    n_real: usize,
) {
    fn bitreverse(mut n: usize, l: usize) -> usize {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }
    let n = a.len();
    assert_eq!(n, 1 << log_n);
    recursive_dif_pruned(a, n, 1, twiddles, n_real);
    for k in 0..n {
        let rk = bitreverse(k, log_n as usize);
        if k < rk {
            a.swap(rk, k);
        }
    }
}

fn recursive_dif(
    a: &mut [crate::bls12_381::Fq],
    n: usize,
    tc: usize,
    tw: &[crate::bls12_381::Fq],
) {
    use crate::bls12_381::Fq;

    #[inline(always)]
    fn gs(a: &mut [Fq], i: usize, j: usize, t: &Fq) {
        unsafe {
            let p = a.as_mut_ptr();
            Fq::gs_butterfly(&mut *p.add(i), &mut *p.add(j), t);
        }
    }

    if n == 2 {
        gs(a, 0, 1, &tw[0]);
    } else {
        let h = n / 2;
        for i in 0..h {
            gs(a, i, i + h, &tw[i * tc]);
        }
        let (left, right) = a.split_at_mut(h);
        rayon::join(
            || recursive_dif(left, h, tc * 2, tw),
            || recursive_dif(right, h, tc * 2, tw),
        );
    }
}

fn recursive_dif_pruned(
    a: &mut [crate::bls12_381::Fq],
    n: usize,
    tc: usize,
    tw: &[crate::bls12_381::Fq],
    nz: usize,
) {
    use crate::bls12_381::Fq;

    #[inline(always)]
    fn gs(a: &mut [Fq], i: usize, j: usize, t: &Fq) {
        unsafe {
            let p = a.as_mut_ptr();
            Fq::gs_butterfly(&mut *p.add(i), &mut *p.add(j), t);
        }
    }

    if nz == 0 {
        return;
    }
    if n == 2 {
        gs(a, 0, 1, &tw[0]);
        return;
    }

    let h = n / 2;

    if nz <= h {
        // Right half entirely zero. Simplified merge:
        // gs_bfly(a, 0, tw) gives x0 unchanged, x1 = x0 * tw.
        for i in 0..nz {
            a[i + h] = a[i];
            a[i + h] *= &tw[i * tc];
        }
    } else {
        let bfly_end = nz.min(h).max(nz.saturating_sub(h));
        for i in 0..bfly_end {
            gs(a, i, i + h, &tw[i * tc]);
        }
    }

    let left_nz = nz.min(h);
    let right_nz = if nz <= h { nz } else { h };

    let (left, right) = a.split_at_mut(h);
    rayon::join(
        || recursive_dif_pruned(left, h, tc * 2, tw, left_nz),
        || recursive_dif_pruned(right, h, tc * 2, tw, right_nz),
    );
}

/// Precompute twiddle factors (powers of omega) for an FFT of size `2^log_n`.
/// Returns a vector of `2^(log_n-1)` elements.
pub fn compute_twiddles<Scalar: Field>(omega: &Scalar, log_n: u32) -> Vec<Scalar> {
    let n = 1usize << log_n;
    (0..(n / 2))
        .scan(Scalar::ONE, |w, _| {
            let tw = *w;
            *w *= omega;
            Some(tw)
        })
        .collect()
}

/// This perform recursive butterfly arithmetic
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

        // case when twiddle factor is one
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

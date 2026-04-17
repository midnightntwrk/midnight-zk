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

/// Reverse the low `log_n` bits of `n`.
fn bitreverse(mut n: usize, log_n: u32) -> usize {
    let mut r = 0;
    for _ in 0..log_n {
        r = (r << 1) | (n & 1);
        n >>= 1;
    }
    r
}

/// Precompute twiddle factors `[1, ω, ω², …, ω^(n/2 - 1)]` for an FFT of size
/// `2^log_n`.
pub fn compute_twiddles<Scalar: Field>(omega: &Scalar, log_n: u32) -> Vec<Scalar> {
    let half_n = 1usize << (log_n - 1);
    (0..half_n)
        .scan(Scalar::ONE, |w, _| {
            let tw = *w;
            *w *= omega;
            Some(tw)
        })
        .collect()
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

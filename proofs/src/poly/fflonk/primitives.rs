//! Curve-free math primitives for fflonk. Naming follows the paper
//! (Gabizon–Williamson 2021, `resources/fflonk.pdf`). These are sufficient
//! to express fflonk's algebraic content and are reused by the PCS impl
//! (`commit` / `multi_open` / `multi_prepare`).

use std::marker::PhantomData;

use ff::{Field, PrimeField};

use crate::poly::{Coeff, Polynomial};

/// Paper's `combine_t`: packs `t` polynomials of length `n` into a single
/// polynomial `g` of length `t·n`, encoding `g(X) = Σ_i X^i · f_i(X^t)`.
///
/// Concretely: `out.values[j·t + i] = polys[i].values[j]`. All input polys
/// must have the same length.
///
/// Held as a primitive (rather than calling it from `commit`/`multi_open`)
/// because the production paths operate on raw `&[F]` slot values and
/// inline the same `j*t + i` interleave for zero-copy performance. This
/// function is the canonical reference algorithm and what the test suite
/// drives — keep it in sync if the inlined version changes shape.
///
/// # Panics
/// If `polys` is empty, or its members have unequal lengths.
#[allow(dead_code)]
pub(super) fn combine<F: PrimeField>(polys: &[&Polynomial<F, Coeff>]) -> Polynomial<F, Coeff> {
    let t = polys.len();
    assert!(t > 0, "combine: needs at least one polynomial");
    let n = polys[0].values.len();
    assert!(
        polys.iter().all(|p| p.values.len() == n),
        "combine: all polys must have equal length"
    );

    let mut values = vec![F::ZERO; t * n];
    for (i, f_i) in polys.iter().enumerate() {
        for (j, &c) in f_i.values.iter().enumerate() {
            values[j * t + i] = c;
        }
    }
    Polynomial {
        values,
        _marker: PhantomData,
    }
}

/// Returns a primitive `t`-th root of unity in `F`, where `t` is a power of
/// two not exceeding the field's 2-adicity `F::S`. Computed as
/// `F::ROOT_OF_UNITY^(2^(S − log2 t))`.
///
/// # Panics
/// If `t` is not a power of two, or `log2 t > F::S`.
pub(super) fn primitive_root_of_unity<F: PrimeField>(t: usize) -> F {
    assert!(t.is_power_of_two(), "t must be a power of two");
    let log_t = t.trailing_zeros();
    assert!(log_t <= F::S, "t exceeds field 2-adicity (F::S)");
    let exp: u64 = 1u64 << (F::S - log_t);
    F::ROOT_OF_UNITY.pow_vartime([exp])
}

/// Paper's `roots_t(x)`: returns `[z, z·ω_t, z·ω_t², …, z·ω_t^{t−1}]`,
/// the `t` t-th roots of `x = z^t`, given any `t`-th root `z` of `x`
/// and a primitive `t`-th root of unity `omega_t`.
pub(super) fn roots<F: Field>(z: F, omega_t: F, t: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(t);
    let mut acc = z;
    for _ in 0..t {
        out.push(acc);
        acc *= omega_t;
    }
    out
}

/// Paper's `S̄(root)`: evaluates the vector of claimed evaluations `claimed`
/// as a polynomial at `root`: `Σ_i root^i · claimed[i]`.
///
/// When `root` is a `t`-th root of `x` and `claimed = (f_0(x), …, f_{t-1}(x))`,
/// this equals `g(root)` by Lemma 5.1 of the paper — the forward
/// Vandermonde the verifier uses (no matrix inversion).
pub(super) fn eval_claims_as_poly<F: Field>(claimed: &[F], root: F) -> F {
    let mut acc = F::ZERO;
    let mut root_pow = F::ONE;
    for &c in claimed {
        acc += root_pow * c;
        root_pow *= root;
    }
    acc
}

/// `omega^r` for signed exponents — for negative `r`, computes
/// `(omega^{-r}).invert()`. Used to step rotated logical points
/// `x · omega_n^r` for `r ∈ Z`.
///
/// Currently exercised only from the test suite
/// (`test_bundle_t2_signed_rotations`); the production paths use
/// `t_th_root(logical, t)` rather than building roots arithmetically from
/// `omega_tn`. Held in place pending the rotation-arithmetic optimization that
/// would replace repeated `sqrt` with `s · omega_tn^r`.
#[allow(dead_code)]
pub(super) fn pow_omega_signed<F: Field>(omega: F, r: i64) -> F {
    if r >= 0 {
        omega.pow_vartime([r as u64])
    } else {
        omega.pow_vartime([(-r) as u64]).invert().unwrap()
    }
}

/// Returns one specific `t`-th root of `x`, computed by `log2(t)` applications
/// of `Field::sqrt`. Deterministic — both prover and verifier compute the same
/// root, which is what fflonk needs (the t roots of `x` are then
/// `{z, z·ω_t, …, z·ω_t^{t-1}}`).
///
/// # Panics
/// If `t` is not a power of two, or if `x` is not a `t`-th power in `F`
/// (intermediate `sqrt()` returns `None`). For fflonk, the caller guarantees
/// `x` is a `t`-th power by construction (queries' logical points are
/// `s^t · ω_n^r` for some `s`).
pub(super) fn t_th_root<F: PrimeField>(x: F, t: usize) -> F {
    assert!(t.is_power_of_two(), "t must be a power of two");
    let log_t = t.trailing_zeros();
    let mut r = x;
    for _ in 0..log_t {
        r = Option::<F>::from(r.sqrt())
            .expect("t_th_root: input is not a square — protocol-level error");
    }
    r
}

/// Precomputed roots of unity needed by fflonk for a vector of groups at
/// evaluation-domain size `2^log_n`. Built once per shape, reused across
/// prove and verify.
///
/// - `omega_n`: primitive `n`-th root of unity (the eval-domain ω).
/// - `omega_tn[i]`: primitive `(t_i · n)`-th root of unity, satisfying
///   `omega_tn[i]^{t_i} == omega_n`. Lets us compute `t_i`-th roots of rotated
///   logical points as `(s · omega_tn[i]^r)^{t_i} = s^{t_i} · omega_n^r`.
/// - `omega_t[i]`: primitive `t_i`-th root of unity. Used together with the
///   base root to enumerate the `t_i` t-th roots of one rotated logical point.
#[allow(dead_code)]
#[derive(Clone, Debug)]
pub(super) struct FflonkRoots<F: PrimeField> {
    pub(super) omega_n: F,
    pub(super) omega_tn: Vec<F>,
    pub(super) omega_t: Vec<F>,
}

#[allow(dead_code)]
impl<F: PrimeField> FflonkRoots<F> {
    /// Build precomputations for groups of sizes `t_i` at domain size
    /// `2^log_n`. Asserts each `t_i · n` fits in the field's 2-adicity, and
    /// (in `new`) the invariant `omega_tn[i]^{t_i} == omega_n`.
    ///
    /// Currently exercised only from the test suite — the production
    /// paths recompute `omega_t` on demand via `primitive_root_of_unity`
    /// and use `t_th_root` rather than `omega_tn`. This struct stays as
    /// the canonical home for the precompute once the rotation-
    /// arithmetic optimization lands.
    pub(super) fn new(ts: &[usize], log_n: u32) -> Self {
        let omega_n: F = F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - log_n)]);
        let omega_tn: Vec<F> = ts
            .iter()
            .map(|&t| {
                assert!(t.is_power_of_two(), "t must be a power of two");
                let log_tn = log_n + t.trailing_zeros();
                assert!(log_tn <= F::S, "t·n exceeds field 2-adicity (F::S)");
                F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - log_tn)])
            })
            .collect();
        let omega_t: Vec<F> = ts.iter().map(|&t| primitive_root_of_unity(t)).collect();
        for (i, &t) in ts.iter().enumerate() {
            assert_eq!(
                omega_tn[i].pow_vartime([t as u64]),
                omega_n,
                "ω_{{t·n}}^t should equal ω_n"
            );
        }
        Self {
            omega_n,
            omega_tn,
            omega_t,
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_curves::Fq as Fr;

    use super::*;
    use crate::poly::Polynomial;

    fn poly(coeffs: &[u64]) -> Polynomial<Fr, Coeff> {
        Polynomial {
            values: coeffs.iter().map(|&c| Fr::from(c)).collect(),
            _marker: PhantomData,
        }
    }

    #[test]
    fn combine_interleaves_coefficients() {
        // f_0 = 1 + 2X, f_1 = 3 + 4X → g = 1 + 3X + 2X² + 4X³.
        let f0 = poly(&[1, 2]);
        let f1 = poly(&[3, 4]);
        let g = combine(&[&f0, &f1]);
        assert_eq!(
            g.values,
            [Fr::from(1), Fr::from(3), Fr::from(2), Fr::from(4)]
        );
    }

    #[test]
    fn primitive_root_has_correct_order() {
        for log_t in 1..=5u32 {
            let t = 1usize << log_t;
            let w: Fr = primitive_root_of_unity(t);
            assert_eq!(w.pow_vartime([t as u64]), Fr::ONE);
            assert_ne!(w.pow_vartime([(t / 2) as u64]), Fr::ONE);
        }
    }

    #[test]
    fn t_th_root_roundtrip() {
        for log_t in 1..=4u32 {
            let t = 1usize << log_t;
            // Pick a t-th power: x = y^t for some y.
            let y = Fr::from(7);
            let x = y.pow_vartime([t as u64]);
            let z = t_th_root(x, t);
            assert_eq!(z.pow_vartime([t as u64]), x);
        }
    }

    #[test]
    fn eval_claims_as_poly_matches_g() {
        // f_0 = 1 + 2X, f_1 = 3 + 4X → g(Y) = 1 + 3Y + 2Y² + 4Y³ in Y = X over t=2.
        // At Y = ω_2 = −1: g(−1) = 1 − 3 + 2 − 4 = −4.
        // f_0(x) = 1 + 2x, f_1(x) = 3 + 4x where x = Y² = 1, so claims = (3, 7).
        // S̄(−1) = 3 + (−1)·7 = −4. ✓
        let claims = [Fr::from(3), Fr::from(7)];
        let omega2: Fr = primitive_root_of_unity(2);
        assert_eq!(omega2, -Fr::ONE);
        assert_eq!(eval_claims_as_poly(&claims, omega2), -Fr::from(4));
    }
}

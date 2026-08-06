use ff::{Field, PrimeField};

// -------------------------------------------------------------------------
// Curve-free fflonk math. Naming follows the paper
// (https://eprint.iacr.org/2021/1167.pdf).
// -------------------------------------------------------------------------

/// Paper's `combine_t`: interleaves up to `t` coefficient slots of equal
/// length `n` into `g` of length `t·n`, where `g[j·t + i] = slots[i][j]` —
/// encoding `g(X) = Σ_i X^i · f_i(X^t)`. Passing fewer than `t` slots leaves
/// the trailing (pad) slots zero, so a padded bundle can pass its real slots
/// only.
///
/// # Panics
/// If `slots.len() > t`, or the slots have unequal lengths.
pub(super) fn combine<F: Field>(slots: &[&[F]], t: usize) -> Vec<F> {
    let n = slots.first().map_or(0, |s| s.len());
    assert!(
        slots.len() <= t,
        "combine: {} slots exceeds t = {t}",
        slots.len()
    );
    assert!(
        slots.iter().all(|s| s.len() == n),
        "combine: all slots must have equal length"
    );
    let mut values = vec![F::ZERO; t * n];
    for (i, slot) in slots.iter().enumerate() {
        for (j, &c) in slot.iter().enumerate() {
            values[j * t + i] = c;
        }
    }
    values
}

/// Returns a primitive `t`-th root of unity in `F`, where `t` is a power of
/// two not exceeding the field's 2-adicity `F::S`. Computed as
/// `F::ROOT_OF_UNITY^(2^(S − log2 t))`. This is the same value
/// `EvaluationDomain::new(1, log2 t)` derives for its `omega`; computed here
/// standalone to avoid building a whole domain for the small `t` fflonk uses.
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

/// Paper's `roots_t(x)`: returns `[z, z ω_t, z ω_t², ..., z ω_t^{t−1}]`, the
/// `t` t-th roots of `x = z^t`, given any `t`-th root `z` of `x` and a
/// primitive `t`-th root of unity `omega_t`.
pub(super) fn roots<F: Field>(z: F, omega_t: F, t: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(t);
    let mut acc = z;
    for _ in 0..t {
        out.push(acc);
        acc *= omega_t;
    }
    out
}

/// Paper's `S̄(root)`: evaluates the vector of claimed evaluations `claimed` as
/// a polynomial at `root`: `Σ_i root^i · claimed[i]`.
///
/// When `root` is a `t`-th root of `x` and `claimed = (f_0(x), …, f_{t-1}(x))`,
/// this equals `g(root)` by Lemma 5.1 of the paper.
pub(super) fn eval_claims_as_poly<F: Field>(claimed: &[F], root: F) -> F {
    let mut acc = F::ZERO;
    let mut root_pow = F::ONE;
    for &c in claimed {
        acc += root_pow * c;
        root_pow *= root;
    }
    acc
}

/// Returns one specific `t`-th root of `x`, computed by `log2(t)` applications
/// of `Field::sqrt`. Deterministic as prover and verifier compute the same root
/// (the `t` roots of `x` are then `{z, z ω_t, ..., z ω_t^{t-1}}`).
///
/// # Panics
/// If `t` is not a power of two, or if `x` is not a `t`-th power in `F`
/// (intermediate `sqrt()` returns `None`). For fflonk, the caller guarantees
/// `x` is a `t`-th power by construction (logical points are `s^t · ω_n^r`).
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

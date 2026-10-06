//! Helpers of the fflonk scheme: the combination `g` of a chunk and the roots
//! it is opened at.

use std::{iter, marker::PhantomData};

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::poly::{
    Coeff, Error, EvaluationDomain, Polynomial, PolynomialBasis, PolynomialRepresentation,
};

/// `g(X) = Σ_i X^i f_i(X^t)`, for `polys` the polynomials `f_0, ..., f_{k-1}`,
/// in any basis, and `t` the next power of two of `k`.
///
/// # Panics
///
/// Panics if the field has no roots of unity of order `n · t`, for `n` the
/// length of the polynomials.
pub(super) fn compute_g<F, B>(polys: &[&Polynomial<F, B>]) -> Polynomial<F, Coeff>
where
    F: WithSmallOrderMulGroup<3>,
    B: PolynomialRepresentation,
{
    let t = polys.len().next_power_of_two();
    let n = polys.iter().map(|poly| poly.len()).max().unwrap_or(0);
    let log_order = n.next_power_of_two().ilog2() + t.ilog2();
    assert!(
        log_order <= F::S,
        "the field has no roots of unity of order 2^{log_order} for fflonk"
    );
    // TODO: In this first version, we are converting to coefficients.
    // We could try to compute g directly in the given base.
    let domain =
        (!matches!(B::BASIS, PolynomialBasis::Coeff)).then(|| EvaluationDomain::new(1, n.ilog2()));
    // The slots of the `t - k` dummy polynomials padding the `k` given ones to
    // `t` are left zero.
    let mut values = vec![F::ZERO; t * n];
    for (i, poly) in polys.iter().enumerate() {
        let converted;
        let coeffs = match &domain {
            None => &poly.values,
            Some(domain) => {
                converted = B::self_to_coeff(domain, (*poly).clone());
                &converted.values
            }
        };
        for (j, coeff) in coeffs.iter().enumerate() {
            values[t * j + i] = *coeff;
        }
    }
    Polynomial {
        values,
        _marker: PhantomData,
    }
}

/// The `t`-th roots of `point`, for a power of two `t`.
///
/// # Errors
///
/// Returns [`Error::OpeningError`] if `point` is not a `t`-th power.
///
/// # Panics
///
/// Panics if `t` is not a power of two.
pub(super) fn roots<F: PrimeField>(point: F, t: usize) -> Result<Vec<F>, Error> {
    assert!(
        t.is_power_of_two(),
        "fflonk roots of order {t}, not a power of two"
    );
    let log_t = t.trailing_zeros();
    let mut root = point;
    for _ in 0..log_t {
        root = Option::from(root.sqrt()).ok_or(Error::OpeningError)?;
    }
    let omega = F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - log_t)]);
    Ok(iter::successors(Some(root), |r| Some(*r * omega)).take(t).collect())
}

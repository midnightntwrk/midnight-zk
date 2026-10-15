//! Small polynomial helpers of the folding protocol: `pow_i(β⃗)`, the
//! perturbator `F(X)` and the univariate polynomials on the folding domain
//! `{0, 1}`.

use ff::Field;
use rayon::prelude::*;

use crate::utils::arithmetic::eval_polynomial;

/// `(x, x², x⁴, …)`: `len` successive squares, starting at `x`.
pub(crate) fn squares<F: Field>(x: F, len: usize) -> Vec<F> {
    std::iter::successors(Some(x), |p| Some(p.square())).take(len).collect()
}

/// `pow_i(β⃗) = Π_b β_b^{i_b}` for every `i ∈ [0, 2^{|β⃗|})`, where `i_b` is
/// bit `b` of `i`.
pub(crate) fn pow_vector<F: Field>(betas: &[F]) -> Vec<F> {
    let mut pows = Vec::with_capacity(1 << betas.len());
    pows.push(F::ONE);
    for beta in betas {
        let upper: Vec<F> = pows.par_iter().map(|p| *p * beta).collect();
        pows.extend(upper);
    }
    pows
}

/// Coefficients of the perturbator `F(X) = Σᵢ powᵢ(β⃗ + X·δ⃗)·fᵢ` (degree
/// `|β⃗|`), computed bottom-up: level `b` combines the entries that differ in
/// bit `b` of `i` as `even + (β_b + X·δ_b)·odd`.
pub(crate) fn perturbator<F: Field>(f: &[F], betas: &[F], deltas: &[F]) -> Vec<F> {
    assert_eq!(f.len(), 1 << betas.len());
    assert_eq!(betas.len(), deltas.len());
    let mut level: Vec<Vec<F>> = f.iter().map(|v| vec![*v]).collect();
    for (beta, delta) in betas.iter().zip(deltas) {
        level = level
            .par_chunks(2)
            .map(|pair| {
                let (even, odd) = (&pair[0], &pair[1]);
                let mut out = even.clone();
                out.push(F::ZERO);
                for (i, o) in odd.iter().enumerate() {
                    out[i] += *beta * o;
                    out[i + 1] += *delta * o;
                }
                out
            })
            .collect();
    }
    level.pop().expect("one polynomial is left")
}

/// `Σᵢ aᵢ·bᵢ`, in parallel.
pub(crate) fn inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    a.par_iter()
        .zip(b.par_iter())
        .map(|(a, b)| *a * b)
        .reduce(|| F::ZERO, |x, y| x + y)
}

/// `L₀(x) = 1 − x`, the Lagrange polynomial of `0` on the folding domain
/// `{0, 1}` (that of `1` is `L₁(x) = x`).
pub(crate) fn l0<F: Field>(x: F) -> F {
    F::ONE - x
}

/// `Z(x) = x·(x − 1)`, the vanishing polynomial of `{0, 1}`.
pub(crate) fn vanishing<F: Field>(x: F) -> F {
    x * (x - F::ONE)
}

/// The new error term `e' = F(α)·L₀(γ) + Z(γ)·K(γ)`.
pub(crate) fn next_error<F: Field>(f_alpha: F, k_coeffs: &[F], gamma: F) -> F {
    f_alpha * l0(gamma) + vanishing(gamma) * eval_polynomial(k_coeffs, gamma)
}

/// Coefficients of the polynomial of degree `< points.len()` through
/// `(points[j], evals[j])`, for distinct `points` (Lagrange interpolation).
pub(crate) fn interpolate<F: Field>(points: &[F], evals: &[F]) -> Vec<F> {
    assert_eq!(points.len(), evals.len());
    let mut coeffs = vec![F::ZERO; points.len()];
    for (j, (xj, yj)) in points.iter().zip(evals).enumerate() {
        // basis_j(X) = Π_{m≠j} (X − x_m) / (x_j − x_m)
        let mut basis = vec![F::ONE];
        let mut denominator = F::ONE;
        for xm in points.iter().enumerate().filter(|(m, _)| *m != j).map(|(_, xm)| xm) {
            basis.insert(0, F::ZERO);
            for i in 0..basis.len() - 1 {
                let next = basis[i + 1];
                basis[i] -= *xm * next;
            }
            denominator *= *xj - xm;
        }
        let scale = *yj * denominator.invert().expect("distinct points");
        for (c, b) in coeffs.iter_mut().zip(basis) {
            *c += scale * b;
        }
    }
    coeffs
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_curves::Fq;
    use rand_core::OsRng;

    use super::*;

    #[test]
    fn perturbator_matches_pow_vector() {
        let betas: Vec<Fq> = (0..4).map(|_| Fq::random(OsRng)).collect();
        let deltas: Vec<Fq> = (0..4).map(|_| Fq::random(OsRng)).collect();
        let f: Vec<Fq> = (0..16).map(|_| Fq::random(OsRng)).collect();
        let coeffs = perturbator(&f, &betas, &deltas);
        let x = Fq::random(OsRng);
        let shifted: Vec<Fq> = betas.iter().zip(&deltas).map(|(b, d)| *b + x * d).collect();
        assert_eq!(
            eval_polynomial(&coeffs, x),
            inner_product(&pow_vector(&shifted), &f)
        );
    }

    #[test]
    fn interpolate_recovers_polynomial() {
        let coeffs: Vec<Fq> = (0..5).map(|_| Fq::random(OsRng)).collect();
        let points: Vec<Fq> = (2..7u64).map(Fq::from).collect();
        let evals: Vec<Fq> = points.iter().map(|x| eval_polynomial(&coeffs, *x)).collect();
        assert_eq!(interpolate(&points, &evals), coeffs);
    }
}

//! Small field helpers of the folding protocol: `pow_i(β⃗)`, the perturbator
//! `F(X)` and the univariate polynomials on the folding domain `{0, …, k}`.

use ff::Field;
use rayon::prelude::*;

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

/// `[0, 1, …, k]` as field elements, the folding domain.
fn domain<F: Field>(k: usize) -> Vec<F> {
    std::iter::successors(Some(F::ZERO), |p| Some(*p + F::ONE))
        .take(k + 1)
        .collect()
}

/// `[L₀(x), …, L_k(x)]`: the Lagrange basis of the folding domain
/// `{0, 1, …, k}` evaluated at `x`, with `L_j(x) = Π_{m≠j} (x − m)/(j − m)`.
pub(crate) fn lagrange_basis<F: Field>(k: usize, x: F) -> Vec<F> {
    let nodes = domain::<F>(k);
    nodes
        .iter()
        .enumerate()
        .map(|(j, xj)| {
            let (numerator, denominator) = nodes
                .iter()
                .enumerate()
                .filter(|(m, _)| *m != j)
                .fold((F::ONE, F::ONE), |(num, den), (_, xm)| {
                    (num * (x - xm), den * (*xj - xm))
                });
            numerator * denominator.invert().expect("distinct nodes")
        })
        .collect()
}

/// `Z(x) = Π_{j=0..k} (x − j)`, the vanishing polynomial of `{0, 1, …, k}`.
pub(crate) fn vanishing<F: Field>(k: usize, x: F) -> F {
    domain::<F>(k).iter().fold(F::ONE, |acc, xj| acc * (x - xj))
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_curves::Fq;
    use rand_core::OsRng;

    use super::*;
    use crate::utils::arithmetic::eval_polynomial;

    fn random_vec(len: usize) -> Vec<Fq> {
        (0..len).map(|_| Fq::random(OsRng)).collect()
    }

    #[test]
    fn perturbator_matches_direct_evaluation() {
        let (betas, deltas, f) = (random_vec(4), random_vec(4), random_vec(16));
        let coeffs = perturbator(&f, &betas, &deltas);
        assert_eq!(coeffs.len(), 5);
        for _ in 0..3 {
            let x = Fq::random(OsRng);
            let direct: Fq = (0..16)
                .map(|i| {
                    let pow: Fq = (0..4)
                        .filter(|b| (i >> b) & 1 == 1)
                        .map(|b| betas[b] + x * deltas[b])
                        .product();
                    pow * f[i]
                })
                .sum();
            assert_eq!(eval_polynomial(&coeffs, x), direct);
        }
    }

    #[test]
    fn pow_vector_matches_bitwise_product() {
        let betas = random_vec(4);
        let pows = pow_vector(&betas);
        assert_eq!(pows.len(), 16);
        for (i, pow) in pows.iter().enumerate() {
            let expected: Fq = (0..4).filter(|b| (i >> b) & 1 == 1).map(|b| betas[b]).product();
            assert_eq!(*pow, expected);
        }
    }

    #[test]
    fn interpolate_reproduces_evaluations() {
        let (points, evals) = (random_vec(6), random_vec(6));
        let coeffs = interpolate(&points, &evals);
        assert_eq!(coeffs.len(), 6);
        for (x, y) in points.iter().zip(&evals) {
            assert_eq!(eval_polynomial(&coeffs, *x), *y);
        }
    }

    #[test]
    fn lagrange_basis_sums_to_one() {
        for k in 1..=3 {
            let basis = lagrange_basis(k, Fq::random(OsRng));
            assert_eq!(basis.len(), k + 1);
            assert_eq!(basis.iter().sum::<Fq>(), Fq::ONE);
        }
    }

    #[test]
    fn lagrange_basis_is_kronecker_on_the_domain() {
        for k in 1..=3 {
            for i in 0..=k {
                let basis = lagrange_basis(k, Fq::from(i as u64));
                for (j, l) in basis.iter().enumerate() {
                    assert_eq!(*l, if i == j { Fq::ONE } else { Fq::ZERO });
                }
            }
        }
    }

    #[test]
    fn lagrange_basis_k1_is_affine() {
        let x = Fq::random(OsRng);
        assert_eq!(lagrange_basis(1, x), vec![Fq::ONE - x, x]);
    }

    #[test]
    fn vanishing_zero_on_domain() {
        for k in 1..=3 {
            for i in 0..=k {
                assert_eq!(vanishing(k, Fq::from(i as u64)), Fq::ZERO);
            }
            assert_ne!(vanishing(k, Fq::from(k as u64 + 1)), Fq::ZERO);
        }
    }

    #[test]
    fn vanishing_k1_is_x_times_x_minus_one() {
        let x = Fq::random(OsRng);
        assert_eq!(vanishing(1, x), x * (x - Fq::ONE));
    }
}

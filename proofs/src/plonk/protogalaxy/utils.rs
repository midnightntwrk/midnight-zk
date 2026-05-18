use std::{
    marker::PhantomData,
    ops::{Add, Mul},
};

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator,
    IntoParallelRefMutIterator, ParallelIterator,
};

use crate::{
    poly::{Coeff, EvaluationDomain, LagrangeCoeff, Polynomial},
    utils::arithmetic::eval_polynomial,
};

/// A single logup (LogUp) trace in folding form: polys in coefficient form.
pub(crate) struct FoldingLogupTrace<F: PrimeField> {
    pub multiplicities: Polynomial<F, Coeff>,
    pub helper_polys: Vec<Polynomial<F, Coeff>>,
    pub aggregator_poly: Polynomial<F, Coeff>,
}

/// A single PLONK prover trace lifted for protogalaxy folding.
///
/// Advice and instance polynomials are kept in Lagrange (evaluation) form so
/// that `evaluate_numerator::<LagrangeCoeff>` can be called directly.
/// Logup, trash, and permutation polynomials are kept in coefficient form
/// (they are converted internally by `evaluate_numerator`).
pub(crate) struct FoldingProverTrace<F: PrimeField> {
    pub advice_polys: Vec<Polynomial<F, LagrangeCoeff>>,
    pub instance_polys: Vec<Polynomial<F, LagrangeCoeff>>,
    pub lookups: Vec<FoldingLogupTrace<F>>,
    pub trash_polys: Vec<Polynomial<F, Coeff>>,
    /// Flattened permutation product polynomials (one per set).
    pub perm_polys: Vec<Polynomial<F, Coeff>>,
    pub challenges: Vec<F>,
    pub beta: F,
    pub gamma: F,
    pub theta: Vec<F>,
    pub trash_challenge: F,
    pub y: Vec<F>,
}

impl<F: PrimeField> FoldingProverTrace<F> {
    /// Create a zero-valued trace with the same dimensions as `other`.
    pub fn zero_like(other: &Self) -> Self {
        let n = other.advice_polys.first().map_or(0, |p| p.values.len());
        let n_coeff = other.perm_polys.first().map_or(
            other.trash_polys.first().map_or(n, |p| p.values.len()),
            |p| p.values.len(),
        );

        let zero_lag = || Polynomial {
            values: vec![F::ZERO; n],
            _marker: PhantomData,
        };
        let zero_coeff = || Polynomial {
            values: vec![F::ZERO; n_coeff],
            _marker: PhantomData,
        };

        let lookups = other
            .lookups
            .iter()
            .map(|l| FoldingLogupTrace {
                multiplicities: zero_coeff(),
                helper_polys: l.helper_polys.iter().map(|_| zero_coeff()).collect(),
                aggregator_poly: zero_coeff(),
            })
            .collect();

        FoldingProverTrace {
            advice_polys: (0..other.advice_polys.len()).map(|_| zero_lag()).collect(),
            instance_polys: (0..other.instance_polys.len()).map(|_| zero_lag()).collect(),
            lookups,
            trash_polys: (0..other.trash_polys.len()).map(|_| zero_coeff()).collect(),
            perm_polys: (0..other.perm_polys.len()).map(|_| zero_coeff()).collect(),
            challenges: vec![F::ZERO; other.challenges.len()],
            beta: F::ZERO,
            gamma: F::ZERO,
            theta: vec![F::ZERO; other.theta.len()],
            trash_challenge: F::ZERO,
            y: vec![F::ZERO; other.y.len()],
        }
    }
}

impl<F: PrimeField> Add<&FoldingProverTrace<F>> for FoldingProverTrace<F> {
    type Output = Self;

    fn add(mut self, rhs: &FoldingProverTrace<F>) -> Self {
        self.advice_polys
            .par_iter_mut()
            .zip(rhs.advice_polys.par_iter())
            .for_each(|(a, b)| *a = a.clone() + b);
        self.instance_polys
            .par_iter_mut()
            .zip(rhs.instance_polys.par_iter())
            .for_each(|(a, b)| *a = a.clone() + b);
        for (l, r) in self.lookups.iter_mut().zip(rhs.lookups.iter()) {
            l.multiplicities = l.multiplicities.clone() + &r.multiplicities;
            l.helper_polys
                .iter_mut()
                .zip(r.helper_polys.iter())
                .for_each(|(a, b)| *a = a.clone() + b);
            l.aggregator_poly = l.aggregator_poly.clone() + &r.aggregator_poly;
        }
        self.trash_polys
            .par_iter_mut()
            .zip(rhs.trash_polys.par_iter())
            .for_each(|(a, b)| *a = a.clone() + b);
        self.perm_polys
            .par_iter_mut()
            .zip(rhs.perm_polys.par_iter())
            .for_each(|(a, b)| *a = a.clone() + b);
        self.challenges
            .iter_mut()
            .zip(rhs.challenges.iter())
            .for_each(|(a, b)| *a += b);
        self.beta += rhs.beta;
        self.gamma += rhs.gamma;
        self.theta
            .iter_mut()
            .zip(rhs.theta.iter())
            .for_each(|(a, b)| *a += b);
        self.trash_challenge += rhs.trash_challenge;
        self.y
            .iter_mut()
            .zip(rhs.y.iter())
            .for_each(|(a, b)| *a += b);
        self
    }
}

impl<F: PrimeField> Mul<F> for FoldingProverTrace<F> {
    type Output = Self;

    fn mul(mut self, scalar: F) -> Self {
        self.advice_polys
            .par_iter_mut()
            .for_each(|p| *p = p.clone() * scalar);
        self.instance_polys
            .par_iter_mut()
            .for_each(|p| *p = p.clone() * scalar);
        for l in self.lookups.iter_mut() {
            l.multiplicities = l.multiplicities.clone() * scalar;
            l.helper_polys
                .iter_mut()
                .for_each(|p| *p = p.clone() * scalar);
            l.aggregator_poly = l.aggregator_poly.clone() * scalar;
        }
        self.trash_polys
            .par_iter_mut()
            .for_each(|p| *p = p.clone() * scalar);
        self.perm_polys
            .par_iter_mut()
            .for_each(|p| *p = p.clone() * scalar);
        self.challenges.iter_mut().for_each(|c| *c *= scalar);
        self.beta *= scalar;
        self.gamma *= scalar;
        self.theta.iter_mut().for_each(|c| *c *= scalar);
        self.trash_challenge *= scalar;
        self.y.iter_mut().for_each(|c| *c *= scalar);
        self
    }
}

/// Computes all 2^|v| subset-product combinations.
///
/// `pow_vec(v)[i]` = product of `v[j]` for each bit `j` set in `i`.
pub(crate) fn pow_vec<F: Field>(vector: &[F]) -> Vec<F> {
    let mut res = vec![F::ONE];
    for x in vector {
        let extended: Vec<F> = res.iter().map(|v| *v * x).collect();
        res.extend(extended);
    }
    res
}

/// Generic linear combination `∑ scalars[i] * elements[i]` via Horner's method.
///
/// Filters out zero-scalar terms and uses in-place Horner accumulation to
/// avoid cloning the buffer multiple times.
pub(crate) fn linear_combination<F, T>(mut buffer: T, elements: &[&T], scalars: &[F]) -> T
where
    F: Field,
    T: for<'a> Add<&'a T, Output = T> + Mul<F, Output = T>,
{
    assert_eq!(elements.len(), scalars.len());

    let (elements, scalars): (Vec<&T>, Vec<&F>) = elements
        .iter()
        .zip(scalars.iter())
        .filter(|(_, s)| !s.is_zero_vartime())
        .unzip();

    let k = elements.len();
    let mut scalars_owned: Vec<F> = scalars.into_iter().cloned().collect();
    scalars_owned.push(F::ONE);

    let mut c = F::ZERO;
    for i in 0..k {
        buffer = buffer * c;
        buffer = buffer + elements[i];
        c = scalars_owned[i] * scalars_owned[i + 1].invert().unwrap();
    }
    buffer * c
}

/// Evaluates the Lagrange basis polynomials of `domain` at `beta`.
///
/// `result[i] = L_i(beta) = Z_n(beta) * ω^i / (n * (beta - ω^i))`
pub(crate) fn eval_lagrange_on_beta<F: PrimeField + WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    beta: &F,
) -> Vec<F> {
    let n = domain.n as usize;
    let omega = domain.get_omega();
    let n_fe = F::from(n as u64);
    let fixed = (beta.pow([n as u64]) - F::ONE) * n_fe.invert().unwrap();

    let mut omegas = Vec::with_capacity(n);
    omegas.push(F::ONE);
    for _ in 1..n {
        let last = *omegas.last().unwrap();
        omegas.push(last * omega);
    }

    omegas
        .into_par_iter()
        .map(|wi| fixed * wi * (*beta - wi).invert().unwrap())
        .collect()
}

/// Interpolates `k` traces over the dk-domain, returning one `FoldingProverTrace`
/// per extended dk-domain point.
///
/// At dk-extended point `t`, the returned trace is `∑_i L_i(x_t) * traces[i]`.
pub(crate) fn batch_traces<F: PrimeField + WithSmallOrderMulGroup<3>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingProverTrace<F>],
) -> Vec<FoldingProverTrace<F>> {
    let lagrange_polys: Vec<_> = (0..traces.len())
        .map(|i| {
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            l
        })
        .map(|p| dk_domain.lagrange_to_coeff(p))
        .map(|p| dk_domain.coeff_to_extended(p))
        .collect();

    let ext_len = lagrange_polys[0].values.len();

    (0..ext_len)
        .map(|t| {
            let buf = FoldingProverTrace::zero_like(traces[0]);
            let coeffs: Vec<F> = lagrange_polys.iter().map(|l| l.values[t]).collect();
            linear_combination(buf, traces, &coeffs)
        })
        .collect()
}

/// Folds `traces` into a single trace at `gamma` via Lagrange interpolation.
pub(crate) fn fold_traces<F: PrimeField + WithSmallOrderMulGroup<3>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingProverTrace<F>],
    gamma: &F,
) -> FoldingProverTrace<F> {
    let lagrange_polys: Vec<_> = (0..traces.len())
        .map(|i| {
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            l
        })
        .map(|p| dk_domain.lagrange_to_coeff(p))
        .collect();

    let lagrange_at_gamma: Vec<F> = lagrange_polys
        .iter()
        .map(|p| eval_polynomial(&p.values, *gamma))
        .collect();

    let buf = FoldingProverTrace::zero_like(traces[0]);
    linear_combination(buf, traces, &lagrange_at_gamma)
}

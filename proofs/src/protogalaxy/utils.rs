use std::ops::{Add, Mul};

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator,
};

use crate::{
    plonk::{
        lookup,
        lookup::verifier::PermutationCommitments,
        permutation,
        traces::{FoldingProverTrace, VerifierFoldingTrace},
        vanishing,
    },
    poly::{commitment::PolynomialCommitmentScheme, EvaluationDomain, Polynomial},
};
use crate::plonk::trash;

/// Given a vector v, computes a vector of length 2^|v| whose i-th element
/// is the product of {v_j : bin(i)_j = 1}. Where bin(i)_j is the
/// j-th (little-endian) bit of i.
pub(crate) fn pow_vec<F: Field>(vector: &[F]) -> Vec<F> {
    let mut res = vec![F::ONE];
    for x in vector {
        res.extend(res.clone().iter().map(|v| *v * x));
    }
    res
}

/// Computes a linear combination between the elements and the scalars.
/// Namely, `sum_i scalars[i] * elements[i]`.
///
/// # Panics
///
/// If the |elements| != |scalars|.
///
/// # Notes
///
/// This function works for any elements of type `T` and scalars of type
/// `F: Field` such that `T: Add<&T, Output = T> + Mul<F, Output = T>`, even
/// if these `Add` and `Mul` traits are implemented in-place (mutating self).
/// Type `T` does not need to implement `Copy` or `Clone`.
///
/// Note however that this function does not mutate the inputs, it only
/// mutates the buffer, in which the result is stored.
// We achieve this by computing a different linear combination using
// Horner's method. For that, first filter out all the elements whose
// corresponding scalar is zero, then we need to convert the scalars into a
// different form.
// Concretely, let k = |elements| = |scalars|. Let c_0 = 0, and scalar[k] = 1.
// Then, for every i ∈ [1, k] let c_i = scalars[i-1] / scalars[i].
//
// Then we compute the linear combination as:
// ```
// for i = 0 to k-1:
//   buffer *= c_i
//   buffer += elements[i]
// return buffer * c_k
// ```
//
// Note that at the end of this execution, the buffer contains:
//    c_1 * c_2 * ... * c_k * elements[0]
//  + c_2 * ... * c_k * elements[1]
//  + ...
//  + c_k * elements[k-1]
//
// Finally, note that, given how we defined c_i, we have:
//   c_1 * c_2 * ... * c_k = scalars[0],
//         c_2 * ... * c_k = scalars[1],
//   ...
//                     c_k = scalars[k-1]
// as desired.
pub(crate) fn linear_combination<F, T>(mut buffer: T, elements: &[&T], scalars: &[F]) -> T
where
    F: Field,
    T: for<'a> Add<&'a T, Output = T> + Mul<F, Output = T>,
{
    assert_eq!(elements.len(), scalars.len());

    // Filter out elements whose scalar is zero.
    let (elements, scalars): (Vec<&T>, Vec<&F>) = (elements.iter())
        .zip(scalars.iter())
        .filter(|(_, s)| !s.is_zero_vartime())
        .unzip();

    let k = elements.len();
    let mut scalars = scalars.into_iter().cloned().collect::<Vec<_>>();
    scalars.push(F::ONE);
    let mut c = F::ZERO;

    for i in 0..k {
        buffer = buffer * c;
        buffer = buffer + elements[i];
        c = scalars[i] * scalars[i + 1].invert().unwrap();
    }

    buffer * c
}

/// A folding trace where, instead of field elements, we have polynomials.
/// It is represented as a vector of folding traces, where the i-th folding
/// trace represents the evaluation of the polynomial at the i-th domain point.
pub type LiftedFoldingTrace<F> = Vec<FoldingProverTrace<F>>;

/// Computes \sum_{j = 0}^k L_j(X) ω_j, where ω_j is the j-th trace,
/// for j = 0, ..., k. The `degree` is the maximum degree of the
/// constraint system.
///
/// TODO: Improve the memory peak that this function leads to.
/// We could handle each output folding trace one by one instead.
pub fn batch_traces<F: PrimeField + WithSmallOrderMulGroup<3>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingProverTrace<F>],
) -> LiftedFoldingTrace<F> {
    let lagrange_polys = (0..traces.len())
        .map(|i| {
            // For the moment we only support batching of traces of dimension one.
            assert_eq!(traces[i].advice_polys.len(), 1);
            let mut l = dk_domain.empty_lagrange();
            l[i] = F::ONE;
            l
        })
        .map(|p| dk_domain.lagrange_to_coeff(p))
        .map(|p| dk_domain.coeff_to_extended(p))
        .collect::<Vec<_>>();

    let dk_domain_size = lagrange_polys[0].num_coeffs();
    assert_eq!(dk_domain_size, dk_domain.extended_len());

    (0..dk_domain.extended_len())
        .map(|i| {
            let buffer = FoldingProverTrace::with_same_dimensions(traces[0]);
            let coordinate_i_lagrange = lagrange_polys
                .iter()
                .map(|poly| poly.values[i])
                .collect::<Vec<_>>();

            linear_combination(buffer, traces, &coordinate_i_lagrange)
        })
        .collect()
}

impl<F: PrimeField> FoldingProverTrace<F> {
    /// Initialise a folding prover trace.
    pub fn init(
        domain_size: usize,
        num_fixed_polys: usize,
        num_advice_polys: usize,
        num_instance_polys: usize,
        num_lookups: usize,
        num_trashcans: usize,
        num_permutation_sets: usize,
        num_challenges: usize,
        num_theta: usize,
        num_y: usize,
    ) -> Self {
        let mut lookups = Vec::with_capacity(num_lookups);
        for _ in 0..num_lookups {
            lookups.push(lookup::prover::CommittedLagrange {
                permuted_input_poly: Polynomial::init(domain_size),
                permuted_table_poly: Polynomial::init(domain_size),
                product_poly: Polynomial::init(domain_size),
            });
        }

        let mut trashcans = Vec::with_capacity(num_trashcans);
        for _ in 0..num_trashcans {
            trashcans.push(trash::prover::CommittedLagrange { trash_poly: Polynomial::init(domain_size) })
        }

        let mut permutation_sets = Vec::with_capacity(num_permutation_sets);
        for _ in 0..num_permutation_sets {
            permutation_sets.push(permutation::prover::CommittedSet {
                permutation_product_poly: Polynomial::init(domain_size),
            });
        }
        FoldingProverTrace {
            fixed_polys: vec![Polynomial::init(domain_size); num_fixed_polys],
            advice_polys: vec![vec![Polynomial::init(domain_size); num_advice_polys]],
            instance_polys: vec![vec![Polynomial::init(domain_size); num_instance_polys]],
            instance_values: vec![vec![Polynomial::init(domain_size); num_instance_polys]],
            vanishing: vanishing::prover::Committed {
                random_poly: Polynomial::init(domain_size),
            },
            lookups: vec![lookups],
            permutations: vec![permutation::prover::Committed {
                sets: permutation_sets,
            }],
            trashcans: vec![trashcans],
            challenges: vec![F::ZERO; num_challenges],
            beta: F::ZERO,
            gamma: F::ZERO,
            trash_challenge: F::ZERO,
            theta: vec![F::ZERO; num_theta],
            y: vec![F::ZERO; num_y],
        }
    }

    /// Initialises a `FoldingProverTrace` with the same dimensions as the given
    /// trace.
    pub(crate) fn with_same_dimensions(trace: &Self) -> Self {
        let trace_domain_size = trace.fixed_polys[0].num_coeffs();
        FoldingProverTrace::init(
            trace_domain_size,
            trace.fixed_polys.len(),
            trace.advice_polys[0].len(),
            trace.instance_polys[0].len(),
            trace.lookups[0].len(),
            trace.trashcans[0].len(),
            trace.permutations[0].sets.len(),
            trace.challenges.len(),
            trace.theta.len(),
            trace.y.len(),
        )
    }
}

impl<F: PrimeField> Add<&FoldingProverTrace<F>> for FoldingProverTrace<F> {
    type Output = Self;

    /// TODO: parallelize.
    fn add(mut self, rhs: &FoldingProverTrace<F>) -> Self {
        // Verifying a single outer vector is enough, as the type guarantees
        // the rest
        assert_eq!(self.advice_polys.len(), rhs.advice_polys.len());

        assert_eq!(self.fixed_polys.len(), rhs.fixed_polys.len());
        assert_eq!(self.challenges.len(), rhs.challenges.len());

        self.fixed_polys
            .par_iter_mut()
            .zip(rhs.fixed_polys.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += rhs;
            });

        (0..self.advice_polys.len()).for_each(|i| {
            assert_eq!(self.advice_polys[i].len(), rhs.advice_polys[i].len());
            assert_eq!(self.instance_polys[i].len(), rhs.instance_polys[i].len());
            assert_eq!(self.lookups[i].len(), rhs.lookups[i].len());
            assert_eq!(
                self.permutations[i].sets.len(),
                rhs.permutations[i].sets.len()
            );

            self.advice_polys[i]
                .par_iter_mut()
                .zip(rhs.advice_polys[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    *lhs += rhs;
                });

            (self.instance_polys[i].par_iter_mut())
                .zip(rhs.instance_polys[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    *lhs += rhs;
                });
            self.lookups[i]
                .par_iter_mut()
                .zip(rhs.lookups[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    lhs.permuted_input_poly += &rhs.permuted_input_poly;
                    lhs.permuted_table_poly += &rhs.permuted_table_poly;
                    lhs.product_poly += &rhs.product_poly;
                });

            (self.permutations[i].sets.par_iter_mut())
                .zip(rhs.permutations[i].sets.par_iter())
                .for_each(|(lhs, rhs)| {
                    lhs.permutation_product_poly += &rhs.permutation_product_poly;
                });
        });

        self.challenges
            .par_iter_mut()
            .zip(rhs.challenges.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        self.beta += rhs.beta;
        self.gamma += rhs.gamma;
        self.theta
            .par_iter_mut()
            .zip(rhs.theta.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });
        self.y
            .par_iter_mut()
            .zip(rhs.y.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        self
    }
}

impl<F: PrimeField> Mul<F> for FoldingProverTrace<F> {
    type Output = Self;

    fn mul(mut self, scalar: F) -> Self {
        self.fixed_polys.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        (0..self.advice_polys.len()).for_each(|i| {
            self.advice_polys[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
            self.instance_polys[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
            self.lookups[i].par_iter_mut().for_each(|lhs| {
                lhs.permuted_input_poly *= scalar;
                lhs.permuted_table_poly *= scalar;
                lhs.product_poly *= scalar;
            });
            self.permutations[i].sets.par_iter_mut().for_each(|lhs| {
                lhs.permutation_product_poly *= scalar;
            });
        });

        self.challenges.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });
        self.beta *= scalar;
        self.gamma *= scalar;

        self.theta.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        self.y.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        self
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> VerifierFoldingTrace<F, PCS> {
    /// Initialise an empty verifier folding trace
    pub fn init(
        num_fixed_polys: usize,
        num_advice_polys: usize,
        num_lookups: usize,
        num_trashcans: usize,
        num_permutation_sets: usize,
        num_challenges: usize,
        num_theta: usize,
        num_y: usize,
    ) -> Self {
        let mut lookups = Vec::with_capacity(num_lookups);
        for _ in 0..num_lookups {
            lookups.push(lookup::verifier::Committed {
                permuted: PermutationCommitments {
                    permuted_input_commitment: PCS::Commitment::default(),
                    permuted_table_commitment: PCS::Commitment::default(),
                },
                product_commitment: PCS::Commitment::default(),
            });
        }
        let mut trashcans = Vec::with_capacity(num_trashcans);
        for _ in 0..num_trashcans {
            trashcans.push(trash::verifier::Committed { trash_commitment: PCS::Commitment::default() })
        }
        VerifierFoldingTrace {
            advice_commitments: vec![vec![PCS::Commitment::default(); num_advice_polys]],
            fixed_commitments: vec![PCS::Commitment::default(); num_fixed_polys],
            vanishing: vanishing::verifier::Committed {
                random_poly_commitment: PCS::Commitment::default(),
            },
            lookups: vec![lookups],
            permutations: vec![permutation::verifier::Committed {
                permutation_product_commitments: vec![
                    PCS::Commitment::default();
                    num_permutation_sets
                ],
            }],
            trashcans: vec![trashcans],
            challenges: vec![F::ZERO; num_challenges],
            beta: F::ZERO,
            gamma: F::ZERO,
            trash_challenge: F::ZERO,
            theta: vec![F::ZERO; num_theta],
            y: vec![F::ZERO; num_y],
        }
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Add<&VerifierFoldingTrace<F, PCS>>
    for VerifierFoldingTrace<F, PCS>
{
    type Output = Self;

    /// TODO: parallelize.
    fn add(mut self, rhs: &VerifierFoldingTrace<F, PCS>) -> Self {
        // Verifying a single outer vector is enough, as the type guarantees
        // the rest
        assert_eq!(self.advice_commitments.len(), rhs.advice_commitments.len());

        assert_eq!(self.fixed_commitments.len(), rhs.fixed_commitments.len());
        assert_eq!(self.challenges.len(), rhs.challenges.len());

        self.fixed_commitments
            .par_iter_mut()
            .zip(rhs.fixed_commitments.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs = lhs.clone() + rhs.clone();
            });

        (0..self.advice_commitments.len()).for_each(|i| {
            assert_eq!(
                self.advice_commitments[i].len(),
                rhs.advice_commitments[i].len()
            );
            assert_eq!(self.lookups[i].len(), rhs.lookups[i].len());
            assert_eq!(
                self.permutations[i].permutation_product_commitments.len(),
                rhs.permutations[i].permutation_product_commitments.len()
            );

            self.advice_commitments[i]
                .par_iter_mut()
                .zip(rhs.advice_commitments[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    *lhs = lhs.clone() + rhs.clone();
                });

            self.lookups[i]
                .par_iter_mut()
                .zip(rhs.lookups[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    lhs.permuted.permuted_input_commitment =
                        lhs.permuted.permuted_input_commitment.clone()
                            + rhs.permuted.permuted_input_commitment.clone();
                    lhs.permuted.permuted_table_commitment =
                        lhs.permuted.permuted_table_commitment.clone()
                            + rhs.permuted.permuted_table_commitment.clone();
                    lhs.product_commitment =
                        lhs.product_commitment.clone() + rhs.product_commitment.clone();
                });

            (self.permutations[i]
                .permutation_product_commitments
                .par_iter_mut())
            .zip(
                rhs.permutations[i]
                    .permutation_product_commitments
                    .par_iter(),
            )
            .for_each(|(lhs, rhs)| {
                *lhs = lhs.clone() + rhs.clone();
            });
        });

        self.challenges
            .par_iter_mut()
            .zip(rhs.challenges.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        self.beta += rhs.beta;
        self.gamma += rhs.gamma;

        self.theta
            .par_iter_mut()
            .zip(rhs.theta.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        self.y
            .par_iter_mut()
            .zip(rhs.y.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        self
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Mul<F> for VerifierFoldingTrace<F, PCS> {
    type Output = Self;

    fn mul(mut self, scalar: F) -> Self {
        self.fixed_commitments.par_iter_mut().for_each(|p| {
            *p = p.clone() * scalar;
        });

        (0..self.advice_commitments.len()).for_each(|i| {
            self.advice_commitments[i].par_iter_mut().for_each(|p| {
                *p = p.clone() * scalar;
            });
            self.lookups[i].par_iter_mut().for_each(|lhs| {
                lhs.permuted.permuted_input_commitment =
                    lhs.permuted.permuted_input_commitment.clone() * scalar;
                lhs.permuted.permuted_table_commitment =
                    lhs.permuted.permuted_table_commitment.clone() * scalar;
                lhs.product_commitment = lhs.product_commitment.clone() * scalar;
            });
            self.permutations[i]
                .permutation_product_commitments
                .par_iter_mut()
                .for_each(|lhs| {
                    *lhs = lhs.clone() * scalar;
                });
        });

        self.challenges.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });
        self.beta *= scalar;
        self.gamma *= scalar;

        self.theta.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        self.y.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        self
    }
}

#[cfg(test)]
mod tests {
    use midnight_curves::Fq as F;

    use super::*;

    #[test]
    fn test_linear_combination() {
        let to_field = |v: &[u64]| -> Vec<F> { v.iter().cloned().map(F::from).collect() };
        [
            (vec![], vec![], 0),
            (vec![7], vec![13], 91),
            (vec![42, 7], vec![0, 13], 91),
            (vec![1, 2], vec![1, 10], 21),
            (vec![1, 2, 3], vec![1, 10, 100], 321),
            (vec![1, 2, 3, 4], vec![1, 10, 100, 1000], 4321),
        ]
        .iter()
        .for_each(|(elements, scalars, expected)| {
            let buffer = F::default();
            let elements = to_field(elements);
            let ref_elements = elements.iter().collect::<Vec<_>>();
            let result = linear_combination(buffer, &ref_elements, &to_field(scalars));
            assert_eq!(result, F::from(*expected as u64));
        });
    }

    #[test]
    fn test_pow_vec() {
        let to_field = |v: &[u64]| -> Vec<F> { v.iter().cloned().map(F::from).collect() };
        let input = vec![2, 3, 5];
        let expected = vec![1, 2, 3, 6, 5, 10, 15, 30];
        assert_eq!(pow_vec(&to_field(&input)), to_field(&expected));
    }
}

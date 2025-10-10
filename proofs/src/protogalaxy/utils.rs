use std::ops::{Add, Mul};
use std::time::Instant;

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
        trash, vanishing,
    },
    poly::{commitment::PolynomialCommitmentScheme, EvaluationDomain, Polynomial},
};
use crate::utils::arithmetic::parallelize;

// /// Given a vector v, computes a vector of length 2^|v| whose i-th element
// /// is the product of {v_j : bin(i)_j = 1}. Where bin(i)_j is the
// /// j-th (little-endian) bit of i.
// pub fn pow_vec<F: Field>(vector: &[F]) -> Vec<F> {
//     let mut res = vec![F::ONE];
//     for x in vector {
//         res.extend(res.clone().iter().map(|v| *v * x));
//     }
//     res
// }

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
    let (elements, scalars): (Vec<&T>, Vec<&F>) = elements.iter()
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
#[allow(unused)]
pub fn batch_traces<F: PrimeField + WithSmallOrderMulGroup<3>>(
    dk_domain: &EvaluationDomain<F>,
    traces: &[&FoldingProverTrace<F>],
) -> LiftedFoldingTrace<F> {
    let now = Instant::now();
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
    println!("Lagrange polys: {:?}", now.elapsed().as_millis());

    let dk_domain_size = lagrange_polys[0].num_coeffs();
    assert_eq!(dk_domain_size, dk_domain.extended_len());
    println!("Domain size: {:?}", dk_domain_size);

    let buffer = FoldingProverTrace::with_same_dimensions(traces[0]);
    println!("+ with same dims: {:?}", now.elapsed().as_millis());

    // TODO: fixed with traces_fft
    // I need to compute \sum_i L_i(X)w_i
    // The way I do it is represent L_i(X) in evaluation form, with
    // d*k evaluations. Then, for each evaluation e_j, I do
    // for j in [0, d*k] : r_j <- \sum_i e_j * w_i
    // The idea is very simple - one simply computes \sum_i L_i(X)w_i over the
    // non extended domain, which is a sum of the w_i's, and then
    // we do a double FFT, one to move to coefficient form (k log k), and
    // one to move to extended domain, which is (dk log dk). Given that
    // we already have one evaluation of the polynomial G(X), we could
    // get only (d - 1)k evaluations ((d - 1) k log (d-1)k).

    let res = (0..dk_domain.extended_len())
        .map(|i| {
            let coordinate_i_lagrange =
                lagrange_polys.iter().map(|poly| poly.values[i]).collect::<Vec<_>>();

            linear_combination(buffer.clone(), traces, &coordinate_i_lagrange)
        })
        .collect();
    println!( "+ linear comb: {:?}", now.elapsed().as_millis());
    res
}

impl<F: PrimeField> FoldingProverTrace<F> {
    /// Initialises a `FoldingProverTrace` with the same dimensions as the given
    /// trace.
    #[allow(unsafe_code)]
    pub(crate) fn unsafe_with_same_dimensions(trace: &Self) -> Self {
        let trace_domain_size = trace.fixed_polys[0].num_coeffs();

        let lookups = (0..trace.lookups[0].len()).map(|_|{
            lookup::prover::CommittedLagrange {
                permuted_input_poly: Polynomial::unsafe_init(trace_domain_size),
                permuted_table_poly: Polynomial::unsafe_init(trace_domain_size),
                product_poly: Polynomial::unsafe_init(trace_domain_size),
            }
        }).collect();

        let trashcans = (0..trace.trashcans[0].len()).map(|_| {
            trash::prover::CommittedLagrange {
                trash_poly: Polynomial::unsafe_init(trace_domain_size),
            }
        }).collect();

        let mut permutation_sets = (0..trace.permutations[0].sets.len()).map(|_| {
            permutation::prover::CommittedSet {
                permutation_product_poly: Polynomial::unsafe_init(trace_domain_size),
            }
        }).collect();

        FoldingProverTrace {
            fixed_polys: (0..trace.fixed_polys.len()).map(|_| Polynomial::unsafe_init(trace_domain_size)).collect(),
            advice_polys: vec![(0..trace.advice_polys[0].len()).map(|_| Polynomial::unsafe_init(trace_domain_size)).collect()],
            instance_polys: vec![(0..trace.instance_polys[0].len()).map(|_| Polynomial::unsafe_init(trace_domain_size)).collect()],
            instance_values: vec![(0..trace.instance_values[0].len()).map(|_| Polynomial::unsafe_init(trace_domain_size)).collect()],
            vanishing: vanishing::prover::Committed {
                random_poly: Polynomial::unsafe_init(trace_domain_size),
            },
            lookups: vec![lookups],
            permutations: vec![permutation::prover::Committed {
                sets: permutation_sets,
            }],
            trashcans: vec![trashcans],
            challenges: vec![F::ZERO; trace.challenges.len()],
            beta: F::ZERO,
            gamma: F::ZERO,
            trash_challenge: F::ZERO,
            theta: vec![F::ZERO; trace.theta.len()],
            y: vec![vec![F::ZERO; trace.y[0].len()]],
        }
    }

    /// Initialises a `FoldingProverTrace` with the same dimensions as the given
    /// trace.
    pub(crate) fn with_same_dimensions(trace: &Self) -> Self {
        let trace_domain_size = trace.fixed_polys[0].num_coeffs();
        let mut lookups = Vec::with_capacity(trace.lookups[0].len());
        for _ in 0..trace.lookups[0].len() {
            lookups.push(lookup::prover::CommittedLagrange {
                permuted_input_poly: Polynomial::init(trace_domain_size),
                permuted_table_poly: Polynomial::init(trace_domain_size),
                product_poly: Polynomial::init(trace_domain_size),
            });
        }

        let mut trashcans = Vec::with_capacity(trace.trashcans[0].len());
        for _ in 0..trace.trashcans[0].len() {
            trashcans.push(trash::prover::CommittedLagrange {
                trash_poly: Polynomial::init(trace_domain_size),
            })
        }

        let mut permutation_sets = Vec::with_capacity(trace.permutations[0].sets.len());
        for _ in 0..trace.permutations[0].sets.len() {
            permutation_sets.push(permutation::prover::CommittedSet {
                permutation_product_poly: Polynomial::init(trace_domain_size),
            });
        }
        FoldingProverTrace {
            fixed_polys: vec![Polynomial::init(trace_domain_size); trace.fixed_polys.len()],
            advice_polys: vec![vec![Polynomial::init(trace_domain_size); trace.advice_polys[0].len()]],
            instance_polys: vec![vec![Polynomial::init(trace_domain_size); trace.instance_polys[0].len()]],
            instance_values: vec![vec![Polynomial::init(trace_domain_size); trace.instance_values[0].len()]],
            vanishing: vanishing::prover::Committed {
                random_poly: Polynomial::init(trace_domain_size),
            },
            lookups: vec![lookups],
            permutations: vec![permutation::prover::Committed {
                sets: permutation_sets,
            }],
            trashcans: vec![trashcans],
            challenges: vec![F::ZERO; trace.challenges.len()],
            beta: F::ZERO,
            gamma: F::ZERO,
            trash_challenge: F::ZERO,
            theta: vec![F::ZERO; trace.theta.len()],
            y: vec![vec![F::ZERO; trace.y[0].len()]],
        }
    }
}

impl<F: PrimeField> Add<&FoldingProverTrace<F>> for FoldingProverTrace<F> {
    type Output = Self;

    /// TODO: parallelize.
    fn add(self, rhs: &FoldingProverTrace<F>) -> Self {
        // Verifying a single outer vector is enough, as the type guarantees
        // the rest
        assert_eq!(self.advice_polys.len(), rhs.advice_polys.len());

        let FoldingProverTrace {
            mut fixed_polys,
            mut advice_polys,
            mut instance_polys,
            mut instance_values,
            mut vanishing,
            mut lookups,
            mut permutations,
            mut trashcans,
            mut challenges,
            mut beta,
            mut gamma,
            mut trash_challenge,
            mut theta,
            mut y
        } = self;

        parallelize(&mut fixed_polys, |lhs, start| {
            for (lhs, rhs) in lhs.iter_mut().zip(rhs.fixed_polys[start..].iter()) {
                *lhs += rhs;
            }
        });

        (0..advice_polys.len()).for_each(|i| {
            parallelize(&mut advice_polys[i], |lhs, start| {
                for (lhs, rhs) in lhs.iter_mut().zip(rhs.advice_polys[i][start..].iter()) {
                    *lhs += rhs;
                }
            });

            parallelize(&mut instance_polys[i], |lhs, start| {
                for (lhs, rhs) in lhs.iter_mut().zip(rhs.instance_polys[i][start..].iter()) {
                    *lhs += rhs;
                }
            });
            parallelize(&mut instance_values[i], |lhs, start| {
                for (lhs, rhs) in lhs.iter_mut().zip(rhs.instance_values[i][start..].iter()) {
                    *lhs += rhs;
                }
            });
            parallelize(&mut lookups[i], |lhs, start| {
                for (lhs, rhs) in lhs.iter_mut().zip(rhs.lookups[i][start..].iter()) {
                    lhs.permuted_input_poly += &rhs.permuted_input_poly;
                    lhs.permuted_table_poly += &rhs.permuted_table_poly;
                    lhs.product_poly += &rhs.product_poly;
                }
            });
            parallelize(&mut permutations[i].sets, |lhs, start| {
                for (lhs, rhs) in lhs.iter_mut().zip(rhs.permutations[i].sets[start..].iter()) {
                    lhs.permutation_product_poly += &rhs.permutation_product_poly;
                }
            });

            vanishing.random_poly += &rhs.vanishing.random_poly;

            trashcans[i]
                .iter_mut()
                .zip(rhs.trashcans[i].iter())
                .for_each(|(lhs, rhs)| {
                    lhs.trash_poly += &rhs.trash_poly;
                });

            y[i].iter_mut().zip(rhs.y[i].iter()).for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });
        });

        challenges
            .iter_mut()
            .zip(rhs.challenges.iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        beta += rhs.beta;
        gamma += rhs.gamma;
        theta.iter_mut().zip(rhs.theta.iter()).for_each(|(lhs, rhs)| {
            *lhs += *rhs;
        });

        trash_challenge += rhs.trash_challenge;

        FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            trash_challenge,
            theta,
            y,
        }
    }
}

impl<F: PrimeField> Mul<F> for FoldingProverTrace<F> {
    type Output = Self;

    fn mul(self, scalar: F) -> Self {
        let FoldingProverTrace {
            mut fixed_polys,
            mut advice_polys,
            mut instance_polys,
            mut instance_values,
            mut vanishing,
            mut lookups,
            mut permutations,
            mut trashcans,
            mut challenges,
            mut beta,
            mut gamma,
            mut trash_challenge,
            mut theta,
            mut y
        } = self;

        fixed_polys.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        (0..advice_polys.len()).for_each(|i| {
            advice_polys[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
            instance_polys[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
            instance_values[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
            lookups[i].par_iter_mut().for_each(|p| {
                p.permuted_input_poly *= scalar;
                p.permuted_table_poly *= scalar;
                p.product_poly *= scalar;
            });
            permutations[i].sets.par_iter_mut().for_each(|p| {
                p.permutation_product_poly *= scalar;
            });
            vanishing.random_poly *= scalar;
            trashcans[i].par_iter_mut().for_each(|p| {
                p.trash_poly *= scalar;
            });

            y[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
        });

        challenges.iter_mut().for_each(|p| {
            *p *= scalar;
        });
        beta *= scalar;
        gamma *= scalar;

        theta.iter_mut().for_each(|p| {
            *p *= scalar;
        });

        trash_challenge *= scalar;

        Self {
            fixed_polys,
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            trash_challenge,
            theta,
            y,
        }
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> VerifierFoldingTrace<F, PCS> {
    /// Initialise an empty verifier folding trace
    #[allow(clippy::too_many_arguments)]
    pub fn with_same_dimensions(
        trace: &Self,
    ) -> Self {
        let num_fixed_polys: usize = trace.fixed_commitments.len();
        let num_advice_polys: usize = trace.advice_commitments[0].len();
        let num_instance_commitments: usize = trace.instance_commitments[0].len();
        let num_instances: usize = trace.instance_polys[0].len();
        let size_instances: usize = if num_instances != 0 {trace.instance_polys[0][0].len()} else {0};
        let num_lookups: usize = trace.lookups[0].len();
        let num_trashcans: usize = trace.trashcans[0].len();
        let num_permutation_sets: usize = trace.permutations[0].permutation_product_commitments.len();
        let num_challenges: usize = trace.challenges.len();
        let num_theta: usize = trace.theta.len();
        let num_y: usize = trace.y[0].len();

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
            trashcans.push(trash::verifier::Committed {
                trash_commitment: PCS::Commitment::default(),
            })
        }
        VerifierFoldingTrace {
            advice_commitments: vec![vec![PCS::Commitment::default(); num_advice_polys]],
            instance_commitments: vec![vec![PCS::Commitment::default(); num_instance_commitments]],
            instance_polys: vec![vec![vec![F::ZERO; size_instances]; num_instances]],
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
            y: vec![vec![F::ZERO; num_y]],
        }
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Add<&VerifierFoldingTrace<F, PCS>>
    for VerifierFoldingTrace<F, PCS>
{
    type Output = Self;

    /// TODO: parallelize.
    fn add(self, rhs: &VerifierFoldingTrace<F, PCS>) -> Self {
        // Verifying a single outer vector is enough, as the type guarantees
        // the rest
        assert_eq!(self.advice_commitments.len(), rhs.advice_commitments.len());

        let VerifierFoldingTrace {
            mut advice_commitments,
            mut instance_commitments,
            mut instance_polys,
            mut fixed_commitments,
            mut vanishing,
            mut lookups,
            mut permutations,
            mut trashcans,
            mut challenges,
            mut beta,
            mut gamma,
            mut trash_challenge,
            mut theta,
            mut y
        } = self;

        fixed_commitments
            .par_iter_mut()
            .zip(rhs.fixed_commitments.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs = lhs.clone() + rhs.clone();
            });

        (0..advice_commitments.len()).for_each(|i| {
            assert_eq!(
                advice_commitments[i].len(),
                rhs.advice_commitments[i].len()
            );
            assert_eq!(lookups[i].len(), rhs.lookups[i].len());
            assert_eq!(
                permutations[i].permutation_product_commitments.len(),
                rhs.permutations[i].permutation_product_commitments.len()
            );

            advice_commitments[i]
                .par_iter_mut()
                .zip(rhs.advice_commitments[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    *lhs = lhs.clone() + rhs.clone();
                });

            instance_commitments[i]
                .par_iter_mut()
                .zip(rhs.instance_commitments[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    *lhs = lhs.clone() + rhs.clone();
                });
            instance_polys[i]
                .par_iter_mut()
                .zip(rhs.instance_polys[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    lhs.par_iter_mut().zip(rhs.par_iter()).for_each(|(lhs,rhs)| *lhs += rhs);
                });

            lookups[i]
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

            permutations[i].permutation_product_commitments.par_iter_mut()
                .zip(rhs.permutations[i].permutation_product_commitments.par_iter())
                .for_each(|(lhs, rhs)| {
                    *lhs = lhs.clone() + rhs.clone();
                });

            vanishing.random_poly_commitment = vanishing.random_poly_commitment.clone() + rhs.vanishing.random_poly_commitment.clone();
            trashcans[i].par_iter_mut()
                .zip(rhs.trashcans[i].par_iter())
                .for_each(|(lhs, rhs)| {
                    lhs.trash_commitment = lhs.trash_commitment.clone() + rhs.trash_commitment.clone();
                });

            y[i].par_iter_mut().zip(rhs.y[i].par_iter()).for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });
        });

        challenges
            .par_iter_mut()
            .zip(rhs.challenges.par_iter())
            .for_each(|(lhs, rhs)| {
                *lhs += *rhs;
            });

        beta += rhs.beta;
        gamma += rhs.gamma;

        theta.par_iter_mut().zip(rhs.theta.par_iter()).for_each(|(lhs, rhs)| {
            *lhs += *rhs;
        });

        trash_challenge += rhs.trash_challenge;

        Self {
            advice_commitments,
            instance_commitments,
            instance_polys,
            fixed_commitments,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            trash_challenge,
            theta,
            y,
        }
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> Mul<F> for VerifierFoldingTrace<F, PCS> {
    type Output = Self;

    fn mul(self, scalar: F) -> Self {
        let VerifierFoldingTrace {
            mut advice_commitments,
            mut instance_commitments,
            mut instance_polys,
            mut fixed_commitments,
            mut vanishing,
            mut lookups,
            mut permutations,
            mut trashcans,
            mut challenges,
            mut beta,
            mut gamma,
            mut trash_challenge,
            mut theta,
            mut y
        } = self;

        fixed_commitments.par_iter_mut().for_each(|p| {
            *p = p.clone() * scalar;
        });

        (0..advice_commitments.len()).for_each(|i| {
            advice_commitments[i].par_iter_mut().for_each(|p| {
                *p = p.clone() * scalar;
            });
            instance_commitments[i]
                .par_iter_mut()
                .for_each(|p| {
                    *p = p.clone() * scalar;
                });
            instance_polys[i]
                .par_iter_mut()
                .for_each(|p| {
                    p.par_iter_mut().for_each(|val| *val *= scalar);
                });
            lookups[i].par_iter_mut().for_each(|lhs| {
                lhs.permuted.permuted_input_commitment =
                    lhs.permuted.permuted_input_commitment.clone() * scalar;
                lhs.permuted.permuted_table_commitment =
                    lhs.permuted.permuted_table_commitment.clone() * scalar;
                lhs.product_commitment = lhs.product_commitment.clone() * scalar;
            });
            permutations[i]
                .permutation_product_commitments
                .par_iter_mut()
                .for_each(|lhs| {
                    *lhs = lhs.clone() * scalar;
                });

            vanishing.random_poly_commitment = vanishing.random_poly_commitment.clone() * scalar;
            trashcans[i].par_iter_mut().for_each(|p| {
                p.trash_commitment = p.trash_commitment.clone() * scalar;
            });

            y[i].par_iter_mut().for_each(|p| {
                *p *= scalar;
            });
        });

        challenges.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });
        beta *= scalar;
        gamma *= scalar;

        theta.par_iter_mut().for_each(|p| {
            *p *= scalar;
        });

        trash_challenge *= scalar;

        Self {
            advice_commitments,
            instance_commitments,
            instance_polys,
            fixed_commitments,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            trash_challenge,
            theta,
            y,
        }
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

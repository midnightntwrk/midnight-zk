//! Representation of a Trace for a batch of proofs that are being generated
//! simultaneously.

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{lookup, permutation, trash, vanishing},
    poly::{commitment::PolynomialCommitmentScheme, Coeff, LagrangeCoeff, Polynomial},
};

/// Prover's trace of a set of proofs. This type guarantees that the size of the
/// outer vector of its fields has the same size.
#[derive(Debug)]
pub struct ProverTrace<F: PrimeField> {
    pub(crate) advice_polys: Vec<Vec<Polynomial<F, LagrangeCoeff>>>,
    pub(crate) instance_polys: Vec<Vec<Polynomial<F, Coeff>>>,
    #[allow(dead_code)]
    // This field will be useful for split accumulation
    pub(crate) instance_values: Vec<Vec<Polynomial<F, LagrangeCoeff>>>,
    pub(crate) vanishing: vanishing::prover::Committed<F>,
    pub(crate) trashcans: Vec<Vec<trash::prover::Committed<F>>>,
    pub(crate) lookups: Vec<Vec<lookup::prover::CommittedLagrange<F>>>,
    pub(crate) permutations: Vec<permutation::prover::Committed<F>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) trash_challenge: F,
    pub(crate) y: F,
}

/// Verifier's trace of a set of proofs. This type guarantees that the size of
/// the outer vector of its fields has the same size.
#[derive(Debug)]
pub struct VerifierTrace<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) advice_commitments: Vec<Vec<PCS::Commitment>>,
    pub(crate) vanishing: vanishing::verifier::Committed<F, PCS>,
    pub(crate) lookups: Vec<Vec<lookup::verifier::Committed<F, PCS>>>,
    pub(crate) trashcans: Vec<Vec<trash::verifier::Committed<F, PCS>>>,
    pub(crate) permutations: Vec<permutation::verifier::Committed<F, PCS>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) trash_challenge: F,
    pub(crate) y: F,
}

/// Trace of a set of proofs folded with folding. This type guarantees that the
/// size of the outer vector of its fields has the same size. It contains the
/// folded fixed_polynomials, allowing for folding of different circuits.
// TODO: REMOVE CLONE - JUST FOR DEBUGGING
#[derive(Clone, Debug)]
pub struct FoldingProverTrace<F: PrimeField> {
    pub(crate) fixed_polys: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) advice_polys: Vec<Vec<Polynomial<F, LagrangeCoeff>>>,
    pub(crate) instance_polys: Vec<Vec<Polynomial<F, Coeff>>>,
    pub(crate) instance_values: Vec<Vec<Polynomial<F, LagrangeCoeff>>>,
    pub(crate) vanishing: vanishing::prover::Committed<F>,
    pub(crate) lookups: Vec<Vec<lookup::prover::CommittedLagrange<F>>>,
    pub(crate) permutations: Vec<permutation::prover::Committed<F>>,
    pub(crate) trashcans: Vec<Vec<trash::prover::Committed<F>>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) y: F,
    pub(crate) trash_challenge: F,
}

impl<F: WithSmallOrderMulGroup<3>> ProverTrace<F> {
    /// Convert a plonk trace, into a folding trace. This includes the
    /// fixed_polynomials, enabling folding of circuits with different fixed
    /// polynomials.
    pub fn into_folding_trace(
        self,
        fixed_polys: Vec<Polynomial<F, LagrangeCoeff>>,
    ) -> FoldingProverTrace<F> {
        let ProverTrace {
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
            theta,
            y,
            trash_challenge,
        } = self;
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
            theta,
            y,
            trash_challenge,
        }
    }

    /// Convert a [ProverTrace] from a folding trace.
    pub fn from_folding_trace(trace: FoldingProverTrace<F>) -> Self {
        let FoldingProverTrace {
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
            theta,
            y,
            trash_challenge,
            ..
        } = trace;
        Self {
            advice_polys,
            instance_polys,
            instance_values,
            vanishing,
            trashcans,
            lookups,
            permutations,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
        }
    }
}

impl<F: WithSmallOrderMulGroup<3>> FoldingProverTrace<F> {
    /// Commit to the folding trace, to check its validity with the folded
    /// commitments
    pub fn commit<PCS: PolynomialCommitmentScheme<F>>(
        &self,
        params: &PCS::Parameters,
    ) -> VerifierFoldingTrace<F, PCS> {
        let nb_proofs = self.advice_polys.len();
        // We currently only support one proof at a time - though we'll make this
        // generic.
        assert_eq!(nb_proofs, 1);

        let mut advice_commitments = Vec::with_capacity(nb_proofs);
        let mut lookups = Vec::with_capacity(nb_proofs);
        let mut permutations = Vec::with_capacity(nb_proofs);
        let mut trashcans = Vec::with_capacity(nb_proofs);

        for i in 0..nb_proofs {
            let committed_advice = self.advice_polys[i]
                .iter()
                .map(|p| PCS::commit_lagrange(params, p))
                .collect::<Vec<_>>();
            let committed_lookups = self.lookups[i]
                .iter()
                .map(|l| lookup::verifier::Committed {
                    permuted: PermutationCommitments {
                        permuted_input_commitment: PCS::commit_lagrange(
                            params,
                            &l.permuted_input_poly,
                        ),
                        permuted_table_commitment: PCS::commit_lagrange(
                            params,
                            &l.permuted_table_poly,
                        ),
                    },
                    product_commitment: PCS::commit_lagrange(params, &l.product_poly),
                })
                .collect::<Vec<_>>();
            let committed_permutations = permutation::verifier::Committed {
                permutation_product_commitments: self.permutations[i]
                    .sets
                    .iter()
                    .map(|p| PCS::commit_lagrange(params, &p.permutation_product_poly))
                    .collect::<Vec<_>>(),
            };

            let committed_trashcans = self.trashcans[i].iter().map(|t| trash::verifier::Committed {
                trash_commitment: PCS::commit(params, &t.trash_poly),
            }).collect::<Vec<_>>();

            advice_commitments.push(committed_advice);
            lookups.push(committed_lookups);
            permutations.push(committed_permutations);
            trashcans.push(committed_trashcans);
        }

        VerifierFoldingTrace {
            advice_commitments,
            fixed_commitments: self
                .fixed_polys
                .iter()
                .map(|p| PCS::commit_lagrange(params, p))
                .collect::<Vec<_>>(),
            vanishing: vanishing::verifier::Committed {
                random_poly_commitment: PCS::commit(params, &self.vanishing.random_poly),
            },
            lookups,
            permutations,
            trashcans,
            challenges: self.challenges.clone(),
            beta: self.beta,
            gamma: self.gamma,
            theta: self.theta,
            y: self.y,
            trash_challenge: self.trash_challenge,
        }
    }
}

/// Verifier's trace of a set of proofs. This type guarantees that the size of
/// the outer vector of its fields has the same size.
// TODO: Missing the instances here :thinking-face:
#[derive(Debug)]
pub struct VerifierFoldingTrace<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> {
    pub(crate) advice_commitments: Vec<Vec<PCS::Commitment>>,
    pub(crate) fixed_commitments: Vec<PCS::Commitment>,
    pub(crate) vanishing: vanishing::verifier::Committed<F, PCS>,
    pub(crate) lookups: Vec<Vec<lookup::verifier::Committed<F, PCS>>>,
    pub(crate) permutations: Vec<permutation::verifier::Committed<F, PCS>>,
    pub(crate) trashcans: Vec<Vec<trash::verifier::Committed<F, PCS>>>,
    pub(crate) challenges: Vec<F>,
    pub(crate) beta: F,
    pub(crate) gamma: F,
    pub(crate) theta: F,
    pub(crate) y: F,
    pub(crate) trash_challenge: F,
}

impl<F: WithSmallOrderMulGroup<3>, PCS: PolynomialCommitmentScheme<F>> PartialEq
    for VerifierFoldingTrace<F, PCS>
{
    fn eq(&self, other: &Self) -> bool {
        assert!(
            self.advice_commitments
                .iter()
                .zip(other.advice_commitments.iter())
                .all(|(lhs, rhs)| {
                    assert_eq!(lhs.len(), rhs.len());
                    lhs.iter().zip(rhs.iter()).all(|(a, b)| a == b)
                }),
            "advice"
        );
        assert!(
            self.fixed_commitments
                .iter()
                .zip(other.fixed_commitments.iter())
                .all(|(a, b)| a == b),
            "fixed"
        );
        assert!(
            self.vanishing.random_poly_commitment == other.vanishing.random_poly_commitment,
            "vanishing"
        );
        assert!(
            self.lookups
                .iter()
                .zip(other.lookups.iter())
                .all(|(lhs, rhs)| {
                    lhs.iter().zip(rhs.iter()).all(|(a, b)| {
                        a.permuted.permuted_input_commitment == b.permuted.permuted_input_commitment
                            && a.permuted.permuted_table_commitment
                                == b.permuted.permuted_table_commitment
                            && a.product_commitment == b.product_commitment
                    })
                }),
            "lookups"
        );
        assert!(
            self.permutations
                .iter()
                .zip(other.permutations.iter())
                .all(|(lhs, rhs)| {
                    lhs.permutation_product_commitments
                        .iter()
                        .zip(rhs.permutation_product_commitments.iter())
                        .all(|(a, b)| a == b)
                }),
            "permutations"
        );
        self.challenges == other.challenges
            && self.beta == other.beta
            && self.gamma == other.gamma
            && self.theta == other.theta
            && self.y == other.y
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> VerifierTrace<F, PCS> {
    /// Convert a plonk trace, into a folding trace. This includes the
    /// fixed_polynomials, enabling folding of circuits with different fixed
    /// polynomials.
    pub fn into_folding_trace(
        self,
        fixed_commitments: &[PCS::Commitment],
    ) -> VerifierFoldingTrace<F, PCS> {
        let VerifierTrace {
            advice_commitments,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
        } = self;
        VerifierFoldingTrace {
            advice_commitments,
            fixed_commitments: fixed_commitments.to_owned(),
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
        }
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> From<VerifierFoldingTrace<F, PCS>>
    for VerifierTrace<F, PCS>
{
    fn from(value: VerifierFoldingTrace<F, PCS>) -> Self {
        let VerifierFoldingTrace {
            advice_commitments,
            vanishing,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            y,
            trash_challenge,
            ..
        } = value;
        Self {
            advice_commitments,
            vanishing,
            lookups,
            trashcans,
            permutations,
            challenges,
            beta,
            gamma,
            trash_challenge,
            theta,
            y,
        }
    }
}

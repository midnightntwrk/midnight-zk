use std::{collections::HashMap, hash::Hash, iter};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use group::ff::BatchInvert;
use rand_core::{CryptoRng, RngCore};

use super::{
    super::{circuit::Expression, Error, ProvingKey},
    Argument,
};
use crate::{
    dev::util::bench,
    plonk::evaluation::evaluate,
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, EvaluationDomain, LagrangeCoeff, Polynomial,
        ProverQuery, Rotation,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::{eval_polynomial, parallelize},
};

#[derive(Debug)]
pub(crate) struct Permuted<F: PrimeField> {
    compressed_input_expression: Polynomial<F, LagrangeCoeff>,
    permuted_input_expression: Polynomial<F, LagrangeCoeff>,
    compressed_table_expression: Polynomial<F, LagrangeCoeff>,
    permuted_table_expression: Polynomial<F, LagrangeCoeff>,
}

// TODO: REMOVE CLONE - JUST FOR DEBUGGING
#[derive(Clone, Debug)]
pub(crate) struct CommittedLagrange<F: PrimeField> {
    pub(crate) permuted_input_poly: Polynomial<F, LagrangeCoeff>,
    pub(crate) permuted_table_poly: Polynomial<F, LagrangeCoeff>,
    pub(crate) product_poly: Polynomial<F, LagrangeCoeff>,
}

// TODO: REMOVE CLONE - JUST FOR DEBUGGING
#[derive(Clone, Debug)]
pub(crate) struct Committed<F: PrimeField> {
    pub(crate) permuted_input_poly: Polynomial<F, Coeff>,
    pub(crate) permuted_table_poly: Polynomial<F, Coeff>,
    pub(crate) product_poly: Polynomial<F, Coeff>,
}

pub(crate) struct Evaluated<F: PrimeField> {
    constructed: Committed<F>,
}

impl<F: WithSmallOrderMulGroup<3> + Ord + Hash> Argument<F> {
    /// Given a Lookup with input expressions [A_0, A_1, ..., A_{m-1}] and table
    /// expressions [S_0, S_1, ..., S_{m-1}], this method
    /// - constructs A_compressed = \theta^{m-1} A_0 + theta^{m-2} A_1 + ... +
    ///   \theta A_{m-2} + A_{m-1} and S_compressed = \theta^{m-1} S_0 +
    ///   theta^{m-2} S_1 + ... + \theta S_{m-2} + S_{m-1},
    /// - permutes A_compressed and S_compressed using permute_expression_pair()
    ///   helper, obtaining A' and S', and
    /// - constructs `Permuted<C>` struct using permuted_input_value = A', and
    ///   permuted_table_expression = S'.
    ///
    /// The `Permuted<C>` struct is used to update the Lookup, and is then
    /// returned.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_permuted<
        'a,
        'params: 'a,
        CS: PolynomialCommitmentScheme<F>,
        R: RngCore,
        T: Transcript,
    >(
        &self,
        pk: &ProvingKey<F, CS>,
        params: &'params CS::Parameters,
        domain: &EvaluationDomain<F>,
        theta: &[F],
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
        challenges: &'a [F],
        mut rng: R,
        transcript: &mut T,
    ) -> Result<Permuted<F>, Error>
    where
        F: FromUniformBytes<64>,
        CS::Commitment: Hashable<T::Hash>,
    {
        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<F>]| {
            println!("Size expressions: {:?}. Size theta: {:?}", expressions.len(), theta.len());
            let compressed_expression = expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec(evaluate(
                        expression,
                        domain.n as usize,
                        1,
                        fixed_values,
                        advice_values,
                        instance_values,
                        challenges,
                    ))
                })
                .zip(theta.iter())
                .fold(domain.empty_lagrange(), |acc, (expression, &theta)| {
                    acc + expression * theta
                });
            compressed_expression
        };

        // Get values of input expressions involved in the lookup and compress them
        let compressed_input_expression = compress_expressions(&self.input_expressions);

        // Get values of table expressions involved in the lookup and compress them
        let compressed_table_expression = compress_expressions(&self.table_expressions);

        // Permute compressed (InputExpression, TableExpression) pair
        let (permuted_input_expression, permuted_table_expression) =
            bench("Permute expression pair", || {
                permute_expression_pair(
                    pk,
                    domain,
                    &mut rng,
                    &compressed_input_expression,
                    &compressed_table_expression,
                )
            })?;

        bench("Commit to lookup expressions", || {
            // Commit to permuted input expression
            let permuted_input_commitment = CS::commit_lagrange(params, &permuted_input_expression);

            // Commit to permuted table expression
            let permuted_table_commitment = CS::commit_lagrange(params, &permuted_table_expression);

            // Hash permuted input commitment
            transcript.write(&permuted_input_commitment)?;

            // Hash permuted table commitment
            transcript.write(&permuted_table_commitment)?;
            Ok::<_, Error>(())
        })?;

        Ok(Permuted {
            compressed_input_expression,
            permuted_input_expression,
            compressed_table_expression,
            permuted_table_expression,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Permuted<F> {
    /// Given a Lookup with input expressions, table expressions, and the
    /// permuted input expression and permuted table expression, this method
    /// constructs the grand product polynomial over the lookup. The grand
    /// product polynomial is used to populate the `Product<C>` struct. The
    /// `Product<C>` struct is added to the Lookup and finally returned by the
    /// method.
    pub(crate) fn commit_product<CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        self,
        pk: &ProvingKey<F, CS>,
        params: &CS::Parameters,
        beta: F,
        gamma: F,
        mut rng: impl RngCore + CryptoRng,
        transcript: &mut T,
    ) -> Result<CommittedLagrange<F>, Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let blinding_factors = pk.vk.cs.blinding_factors();
        // Goal is to compute the products of fractions
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... +
        // \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... +
        //              \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where a_j(X) is the jth input expression in this lookup,
        // where a'(X) is the compression of the permuted input expressions,
        // s_j(X) is the jth table expression in this lookup,
        // s'(X) is the compression of the permuted table expressions,
        // and i is the ith row of the expression.
        let mut lookup_product = vec![F::ZERO; pk.vk.n() as usize];
        bench("Batch invert", || {
            // Denominator uses the permuted input expression and permuted table expression
            parallelize(&mut lookup_product, |lookup_product, start| {
                for ((lookup_product, permuted_input_value), permuted_table_value) in lookup_product
                    .iter_mut()
                    .zip(self.permuted_input_expression[start..].iter())
                    .zip(self.permuted_table_expression[start..].iter())
                {
                    *lookup_product =
                        (beta + permuted_input_value) * &(gamma + permuted_table_value);
                }
            });

            // Batch invert to obtain the denominators for the lookup product
            // polynomials
            lookup_product.iter_mut().batch_invert();
            Ok::<_, Error>(())
        })?;

        bench("Finish computation", || {
            // Finish the computation of the entire fraction by computing the numerators
            // (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta
            // a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
            // * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta
            //   s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
            parallelize(&mut lookup_product, |product, start| {
                for (i, product) in product.iter_mut().enumerate() {
                    let i = i + start;

                    *product *= &(self.compressed_input_expression[i] + &beta);
                    *product *= &(self.compressed_table_expression[i] + &gamma);
                }
            });
            Ok::<_, Error>(())
        })?;

        // The product vector is a vector of products of fractions of the form
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... +
        // \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... +
        //              \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where there are m input expressions and m table expressions,
        // a_j(\omega^i) is the jth input expression in this lookup,
        // a'j(\omega^i) is the permuted input expression,
        // s_j(\omega^i) is the jth table expression in this lookup,
        // s'(\omega^i) is the permuted table expression,
        // and i is the ith row of the expression.

        let z = bench("Compute z", || {
            // Compute the evaluations of the lookup product polynomial
            // over our domain, starting with z[0] = 1
            Ok::<_, Error>(
                iter::once(F::ONE)
                    .chain(lookup_product)
                    .scan(F::ONE, |state, cur| {
                        *state *= &cur;
                        Some(*state)
                    })
                    // Take all rows including the "last" row which should
                    // be a boolean (and ideally 1, else soundness is broken)
                    .take(pk.vk.n() as usize - blinding_factors)
                    // Chain random blinding factors.
                    .chain((0..blinding_factors).map(|_| F::random(&mut rng)))
                    .collect::<Vec<_>>(),
            )
        })?;
        assert_eq!(z.len(), pk.vk.n() as usize);
        let z = pk.vk.domain.lagrange_from_vec(z);

        #[cfg(feature = "sanity-checks")]
        // This test works only with intermediate representations in this method.
        // It can be used for debugging purposes.
        {
            // While in Lagrange representation, check that product is correctly constructed
            let u = (pk.vk.n() as usize) - (blinding_factors + 1);

            // l_0(X) * (1 - z(X)) = 0
            assert_eq!(z[0], F::ONE);

            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X)
            //   + ... + s_{m-1}(X) + \gamma)
            for i in 0..u {
                let mut left = z[i + 1];
                let permuted_input_value = &self.permuted_input_expression[i];

                let permuted_table_value = &self.permuted_table_expression[i];

                left *= &(beta + permuted_input_value);
                left *= &(gamma + permuted_table_value);

                let mut right = z[i];
                let mut input_term = self.compressed_input_expression[i];
                let mut table_term = self.compressed_table_expression[i];

                input_term += &(beta);
                table_term += &(gamma);
                right *= &(input_term * &table_term);

                assert_eq!(left, right);
            }

            // l_last(X) * (z(X)^2 - z(X)) = 0
            // Assertion will fail only when soundness is broken, in which
            // case this z[u] value will be zero. (bad!)
            assert_eq!(z[u], F::ONE);
        }

        bench("Commit to Z polynomial (lookup)", || {
            let product_commitment = CS::commit_lagrange(params, &z);

            // Hash product commitment
            transcript.write(&product_commitment)?;
            Ok::<_, Error>(())
        })?;

        Ok(CommittedLagrange::<F> {
            permuted_input_poly: self.permuted_input_expression,
            permuted_table_poly: self.permuted_table_expression,
            product_poly: z,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>> CommittedLagrange<F> {
    pub(crate) fn evaluate<T: Transcript, CS: PolynomialCommitmentScheme<F>>(
        self,
        pk: &ProvingKey<F, CS>,
        x: F,
        transcript: &mut T,
    ) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let domain = &pk.vk.domain;
        let x_inv = domain.rotate_omega(x, Rotation::prev());
        let x_next = domain.rotate_omega(x, Rotation::next());

        let committed_coeff = Committed {
            permuted_input_poly: domain.lagrange_to_coeff(self.permuted_input_poly),
            permuted_table_poly: domain.lagrange_to_coeff(self.permuted_table_poly),
            product_poly: domain.lagrange_to_coeff(self.product_poly),
        };

        let product_eval = eval_polynomial(&committed_coeff.product_poly, x);
        let product_next_eval = eval_polynomial(&committed_coeff.product_poly, x_next);
        let permuted_input_eval = eval_polynomial(&committed_coeff.permuted_input_poly, x);
        let permuted_input_inv_eval = eval_polynomial(&committed_coeff.permuted_input_poly, x_inv);
        let permuted_table_eval = eval_polynomial(&committed_coeff.permuted_table_poly, x);

        // Hash each advice evaluation
        for eval in iter::empty()
            .chain(Some(product_eval))
            .chain(Some(product_next_eval))
            .chain(Some(permuted_input_eval))
            .chain(Some(permuted_input_inv_eval))
            .chain(Some(permuted_table_eval))
        {
            transcript.write(&eval)?;
        }

        Ok(Evaluated {
            constructed: committed_coeff,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3> + Hash> Evaluated<F> {
    pub(crate) fn open<'a, CS: PolynomialCommitmentScheme<F>>(
        &'a self,
        pk: &'a ProvingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = ProverQuery<'a, F>> + Clone {
        let x_inv = pk.vk.domain.rotate_omega(x, Rotation::prev());
        let x_next = pk.vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            // Open lookup product commitments at x
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.product_poly,
            }))
            // Open lookup input commitments at x
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.permuted_input_poly,
            }))
            // Open lookup table commitments at x
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.permuted_table_poly,
            }))
            // Open lookup input commitments at x_inv
            .chain(Some(ProverQuery {
                point: x_inv,
                poly: &self.constructed.permuted_input_poly,
            }))
            // Open lookup product commitments at x_next
            .chain(Some(ProverQuery {
                point: x_next,
                poly: &self.constructed.product_poly,
            }))
    }
}

type ExpressionPair<F> = (Polynomial<F, LagrangeCoeff>, Polynomial<F, LagrangeCoeff>);

/// Given a vector of input values A and a vector of table values S,
/// this method permutes A and S to produce A' and S', such that:
/// - like values in A' are vertically adjacent to each other; and
/// - the first row in a sequence of like values in A' is the row that has the
///   corresponding value in S'.
///
/// This method returns (A', S') if no errors are encountered.
fn permute_expression_pair<F, CS: PolynomialCommitmentScheme<F>, R: RngCore>(
    pk: &ProvingKey<F, CS>,
    domain: &EvaluationDomain<F>,
    mut rng: R,
    input_expression: &Polynomial<F, LagrangeCoeff>,
    table_expression: &Polynomial<F, LagrangeCoeff>,
) -> Result<ExpressionPair<F>, Error>
where
    F: WithSmallOrderMulGroup<3> + Hash + Ord + FromUniformBytes<64>,
{
    let blinding_factors = pk.vk.cs.blinding_factors();
    let usable_rows = pk.vk.n() as usize - (blinding_factors + 1);

    let mut permuted_input_expression: Vec<F> = input_expression.to_vec();
    permuted_input_expression.truncate(usable_rows);

    // Sort input lookup expression values
    bench("Sort", || {
        permuted_input_expression.sort();
        Ok::<(), Error>(())
    })?;

    // A HashMap of each unique element in the table expression and its count
    let mut leftover_table_map: HashMap<F, u32> = bench("table expression", || {
        Ok::<HashMap<F, u32>, Error>(table_expression.iter().take(usable_rows).fold(
            HashMap::<F, u32>::new(),
            |mut acc: HashMap<F, u32>, coeff| {
                *acc.entry(*coeff).or_insert(0) += 1;
                acc
            },
        ))
    })?;
    let mut permuted_table_coeffs = vec![F::ZERO; usable_rows];

    let mut repeated_input_rows = bench("Repeated input rows", || {
        permuted_input_expression
            .iter()
            .zip(permuted_table_coeffs.iter_mut())
            .enumerate()
            .filter_map(|(row, (input_value, table_value))| {
                // If this is the first occurrence of `input_value` in the input expression
                if row == 0 || *input_value != permuted_input_expression[row - 1] {
                    *table_value = *input_value;
                    // Remove one instance of input_value from leftover_table_map
                    if let Some(count) = leftover_table_map.get_mut(input_value) {
                        assert!(*count > 0);
                        *count -= 1;
                        None
                    } else {
                        // Return error if input_value not found
                        Some(Err(Error::ConstraintSystemFailure))
                    }
                // If input value is repeated
                } else {
                    Some(Ok(row))
                }
            })
            .collect::<Result<Vec<_>, _>>()
    })?;

    // Populate permuted table at unfilled rows with leftover table elements
    for (coeff, count) in leftover_table_map.iter() {
        for _ in 0..*count {
            permuted_table_coeffs[repeated_input_rows.pop().unwrap()] = *coeff;
        }
    }
    assert!(repeated_input_rows.is_empty());

    permuted_input_expression.extend((0..(blinding_factors + 1)).map(|_| F::random(&mut rng)));
    permuted_table_coeffs.extend((0..(blinding_factors + 1)).map(|_| F::random(&mut rng)));
    assert_eq!(permuted_input_expression.len(), pk.vk.n() as usize);
    assert_eq!(permuted_table_coeffs.len(), pk.vk.n() as usize);

    #[cfg(feature = "sanity-checks")]
    {
        let mut last = None;
        for (a, b) in permuted_input_expression
            .iter()
            .zip(permuted_table_coeffs.iter())
            .take(usable_rows)
        {
            if *a != *b {
                assert_eq!(*a, last.unwrap());
            }
            last = Some(*a);
        }
    }

    Ok((
        domain.lagrange_from_vec(permuted_input_expression),
        domain.lagrange_from_vec(permuted_table_coeffs),
    ))
}

use std::{hash::Hash, iter};

use ff::{BatchInvert, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{evaluation::evaluate, Error, Expression, ProvingKey},
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, LagrangeCoeff, Polynomial,
        ProverQuery, Rotation,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::{eval_polynomial, parallelize},
};
use crate::plonk::logup::FlattenArgument;

#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField> {
    pub(crate) multiplicities: Polynomial<F, Coeff>,
    pub(crate) helper_poly: Polynomial<F, Coeff>,
    pub(crate) aggregator_poly: Polynomial<F, Coeff>,
}

pub(crate) struct Evaluated<F: PrimeField> {
    pub(crate) constructed: Committed<F>,
}

impl<F: WithSmallOrderMulGroup<3> + Hash> FlattenArgument<F> {
    /// Given a logup with compressed input/table expressions, this function
    /// constructs the grand product polynomial over the logup. This is used
    /// to create the `LogDerivative<C>` struct.
    pub(crate) fn commit_logderivative<'a, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        self,
        pk: &ProvingKey<F, CS>,
        params: &CS::Parameters,
        beta: F,
        theta: F,
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
        challenges: &'a [F],
        transcript: &mut T,
    ) -> Result<Committed<F>, Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let domain = pk.vk.get_domain();
        let n = domain.n as usize;
        let eval_expressions = |expressions: &[Expression<F>]| -> Vec<Polynomial<F, LagrangeCoeff>> {
            expressions.iter().map(|expression| {
                pk.vk.domain.lagrange_from_vec(evaluate(
                    expression,
                    n,
                    1,
                    fixed_values,
                    advice_values,
                    instance_values,
                    challenges,
                ))
            }).collect()
        };
        // CHECK: Get the columns of the expressions, and see where is the mismatch wrt the verifier.
        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<F>]| {
            let compressed_expression = eval_expressions(expressions).iter()
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * theta + expression
                });
            compressed_expression
        };

        let compressed_input_expression = self.input_expressions.iter().map(|chunk| compress_expressions(chunk))
            .collect::<Vec<_>>();
        let compressed_table_expression = compress_expressions(&self.table_expressions);

        let multiplicities =
            compute_multiplicities(&compressed_input_expression, &compressed_table_expression);

        // We need to compute the helper commitment, for which we need to do batch
        // inversion for each of the tables.
        let mut table_denoms = vec![F::ZERO; n];
        parallelize(&mut table_denoms, |input, start| {
            // T(X)   = 1 / (f(X)   + beta)
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                *input = beta + compressed_table_expression.values[i];
            }
        });
        table_denoms.iter_mut().batch_invert();

        let input_len = compressed_input_expression.len();
        let mut input_denoms = vec![F::ZERO; input_len * n];

        parallelize(&mut input_denoms, |input, start| {
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                *input = beta + compressed_input_expression[i / n].values[i % n];
            }
        });

        input_denoms.iter_mut().batch_invert();
        let mut helper_poly = vec![F::ZERO; n];

        parallelize(&mut helper_poly, |input, start| {
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                for j in 0..input_len {
                    *input += input_denoms[i + j * n];
                }
            }
        });

        let mut logderivative_poly = vec![F::ZERO; n];
        parallelize(&mut logderivative_poly, |poly, start| {
            for (i, coeff) in poly.iter_mut().enumerate() {
                let i = i + start;
                *coeff = helper_poly[i] - multiplicities[i] * table_denoms[i];
            }
        });

        // We take -1 because the last part is verified by the identity.
        let aggregator_poly = iter::once(F::ZERO)
            .chain(logderivative_poly.iter().cloned().take(n - 1))
            .scan(F::ZERO, |state, cur| {
                *state += cur;
                Some(*state)
            })
            .collect::<Vec<F>>();


        let multiplicities = pk.vk.domain.lagrange_from_vec(multiplicities);
        let helper_poly = pk.vk.domain.lagrange_from_vec(helper_poly);
        let aggregator_poly = pk.vk.domain.lagrange_from_vec(aggregator_poly);

        let multiplicities_commitment = CS::commit_lagrange(params, &multiplicities);
        transcript.write(&multiplicities_commitment)?;

        let helper_commitment = CS::commit_lagrange(params, &helper_poly);
        transcript.write(&helper_commitment)?;

        let aggregator_commitment = CS::commit_lagrange(params, &aggregator_poly);
        transcript.write(&aggregator_commitment)?;

        let multiplicities = pk.vk.domain.lagrange_to_coeff(multiplicities);
        let helper_poly = pk.vk.domain.lagrange_to_coeff(helper_poly);
        let aggregator_poly = pk.vk.domain.lagrange_to_coeff(aggregator_poly);

        // // Checks:
        // // Convert compressed inputs and table from Lagrange to coefficient form
        // let compressed_input_coeff: Vec<_> = compressed_input_expression.iter()
        //     .map(|p| pk.vk.domain.lagrange_to_coeff(p.clone()))
        //     .collect();
        // // Helper poly
        // let challenge = pk.vk.domain.get_omega().pow_vartime([OsRng.next_u64()]); // we are only checking the first line, but well.
        //
        // // Check helper poly in Lagrange form before conversion
        // let helper_eval = eval_polynomial(&helper_poly, challenge);
        //
        // let fs_evals = compressed_input_coeff.iter().map(|p| eval_polynomial(p, challenge) + beta).collect::<Vec<_>>();
        //
        // let partial_products: Vec<F> = (0..fs_evals.len()).map(|i| {
        //     let mut acc = F::ONE;
        //     for j in 0..fs_evals.len() {
        //         if j != i {
        //             acc *= fs_evals[j];
        //         }
        //     }
        //     acc
        // }).collect();
        // let sum_partial_products: F = partial_products.iter().sum();
        // let product: F = fs_evals.iter().product();
        // assert_eq!(helper_eval * product, sum_partial_products);

        Ok(Committed {
            multiplicities,
            helper_poly,
            aggregator_poly,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Committed<F> {
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
        let x_next = domain.rotate_omega(x, Rotation::next());

        let multiplicities_eval = eval_polynomial(&self.multiplicities, x);
        let logderivative_eval = eval_polynomial(&self.helper_poly, x);
        let aggregator_eval = eval_polynomial(&self.aggregator_poly, x);
        let aggregator_eval_next = eval_polynomial(&self.aggregator_poly, x_next);

        for eval in iter::once(multiplicities_eval)
            .chain(Some(logderivative_eval))
            .chain(Some(aggregator_eval))
            .chain(Some(aggregator_eval_next))
        {
            transcript.write(&eval)?;
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluated<F> {
    pub(crate) fn open<'a, CS: PolynomialCommitmentScheme<F>>(
        &'a self,
        pk: &'a ProvingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = ProverQuery<'a, F>> + Clone {
        let x_next = pk.vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            // We need to open the aggregator at 1
            .chain(Some(ProverQuery {
                point: F::ONE,
                poly: &self.constructed.aggregator_poly,
            }))
            // Open the multiplicity column at x
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.multiplicities,
            }))
            // Open the helper polynomial at x
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.helper_poly,
            }))
            // Open aggregator polynomial at x
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.aggregator_poly,
            }))
            // Open aggregator polynomial at x next
            .chain(Some(ProverQuery {
                point: x_next,
                poly: &self.constructed.aggregator_poly,
            }))
    }
}

/// Computes the multiplicity of each value in the polynomial.
///
/// Returns a vector where `result[i]` is the number of times `table[i]` appears
/// in `values`.
pub(crate) fn compute_multiplicities<F>(
    values: &[Polynomial<F, LagrangeCoeff>],
    table: &Polynomial<F, LagrangeCoeff>,
) -> Vec<F>
where
    F: PrimeField + std::hash::Hash + Eq,
{
    use std::collections::HashMap;

    let mut counts = HashMap::<F, u32>::from_iter(table.values.iter().map(|v| (*v, 0)));
    values.iter().for_each(|value| {
        value.iter().for_each(|v| {
            *counts.entry(*v).or_insert(0) += 1;
        })
    });

    table.iter().map(|value| F::from(*counts.get(value).unwrap() as u64)).collect()
}

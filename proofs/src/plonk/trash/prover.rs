use ff::WithSmallOrderMulGroup;

use super::Argument;
use crate::{
    plonk::evaluation::evaluate,
    poly::{EvaluationDomain, LagrangeCoeff, Polynomial},
};

impl<F: WithSmallOrderMulGroup<3>> Argument<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compute_trash_poly<'a>(
        &self,
        domain: &EvaluationDomain<F>,
        trash_challenge: F,
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
    ) -> Polynomial<F, LagrangeCoeff> {
        self.constraint_expressions
            .iter()
            .map(|expression| {
                domain.lagrange_from_vec(evaluate(
                    expression,
                    domain.n as usize,
                    0,
                    fixed_values,
                    advice_values,
                    instance_values,
                ))
            })
            .fold(domain.empty_lagrange(), |acc, expression| {
                acc * trash_challenge + &expression
            })
    }
}

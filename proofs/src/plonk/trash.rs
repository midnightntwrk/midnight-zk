use std::{cmp::max, fmt::Debug};

use ff::{Field, PrimeField};

use super::circuit::Expression;

pub(crate) mod prover;
pub(crate) mod verifier;

#[derive(Clone, Debug)]
pub struct Argument<F: Field> {
    name: String,
    pub(crate) selector: Expression<F>,
    pub(crate) constraint_expressions: Vec<Expression<F>>,
}

impl<F: Field> Argument<F> {
    /// Constructs a new trash argument.
    pub fn new(
        name: String,
        selector: Expression<F>,
        constraint_expressions: Vec<Expression<F>>,
    ) -> Self {
        Argument {
            name,
            selector,
            constraint_expressions,
        }
    }

    pub(crate) fn required_degree(&self) -> usize {
        let degrees = self.constraint_expressions.iter().map(|e| e.degree());
        max(2, degrees.max().unwrap_or(0)) // 2 comes from (1 - q) * trash
    }

    /// The name of this argument.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The selector of this trash argument.
    pub fn selector(&self) -> &Expression<F> {
        &self.selector
    }

    /// The constraints of this trash argument.
    pub fn constraint_expressions(&self) -> &Vec<Expression<F>> {
        &self.constraint_expressions
    }
}

#[derive(Debug)]
pub struct Evaluated<F: PrimeField> {
    trash_eval: F,
}

impl<F: PrimeField> Evaluated<F> {
    pub(crate) fn expressions<'a>(
        &'a self,
        argument: &'a Argument<F>,
        trash_challenge: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        let evaluate_expression = |expr: &Expression<F>| {
            expr.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| fixed_evals[query.index.unwrap()],
                &|query| advice_evals[query.index.unwrap()],
                &|query| instance_evals[query.index.unwrap()],
                &|challenge| challenges[challenge.index()],
                &|a| -a,
                &|a, b| a + &b,
                &|a, b| a * &b,
                &|a, scalar| a * &scalar,
            )
        };

        let compressed_expressions = (argument.constraint_expressions.iter())
            .map(evaluate_expression)
            .fold(F::ZERO, |acc, eval| acc * &trash_challenge + &eval);

        let q = evaluate_expression(argument.selector());
        vec![compressed_expressions - (F::ONE - q) * self.trash_eval].into_iter()
    }
}

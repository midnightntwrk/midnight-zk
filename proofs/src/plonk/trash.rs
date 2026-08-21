use std::{cmp::max, collections::BTreeMap, fmt::Debug};

use ff::{Field, PrimeField};

use super::circuit::Expression;
use crate::{plonk::argument, poly::PolynomialLabel};

pub(crate) mod prover;

#[derive(Clone, Debug)]
pub struct Argument<F: Field> {
    pub(crate) argument_index: usize,
    pub(crate) selector: Expression<F>,
    pub(crate) constraint_expressions: Vec<Expression<F>>,
}

impl<F: Field> Argument<F> {
    /// Constructs a new trash argument.
    pub fn new(
        argument_index: usize,
        selector: Expression<F>,
        constraint_expressions: Vec<Expression<F>>,
    ) -> Self {
        Argument {
            argument_index,
            selector,
            constraint_expressions,
        }
    }

    pub(crate) fn required_degree(&self) -> usize {
        let degrees = self.constraint_expressions.iter().map(|e| e.degree());
        max(2, degrees.max().unwrap_or(0)) // 2 comes from (1 - q) * trash
    }

    /// The name of this argument.
    pub fn name(&self) -> String {
        format!("trash #{}", self.argument_index + 1)
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

impl<F: PrimeField> Argument<F> {
    pub(crate) fn expressions(
        &self,
        evals_map: &BTreeMap<PolynomialLabel, Vec<argument::Evaluation<F>>>,
        trash_challenge: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
    ) -> impl Iterator<Item = F> {
        let trash_label = PolynomialLabel::Trash(self.argument_index);
        let trash_eval = evals_map.get(&trash_label).unwrap()[0].eval();

        let evaluate_expression = |expr: &Expression<F>| {
            expr.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| fixed_evals[query.index.unwrap()],
                &|query| advice_evals[query.index.unwrap()],
                &|query| instance_evals[query.index.unwrap()],
                &|a| -a,
                &|a, b| a + &b,
                &|a, b| a * &b,
                &|a, scalar| a * &scalar,
            )
        };

        let compressed_expressions = (self.constraint_expressions.iter())
            .map(evaluate_expression)
            .fold(F::ZERO, |acc, eval| acc * &trash_challenge + &eval);

        let q = evaluate_expression(self.selector());
        vec![compressed_expressions - (F::ONE - q) * trash_eval].into_iter()
    }
}

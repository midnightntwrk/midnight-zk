use std::{cmp::max, fmt::Debug};

use ff::Field;

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

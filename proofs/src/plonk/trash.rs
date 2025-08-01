use std::{cmp::max, fmt::Debug};

use ff::Field;

use super::circuit::Expression;

pub(crate) mod prover;
pub(crate) mod verifier;

#[derive(Clone, Debug)]
pub struct Argument<F: Field> {
    pub(crate) name: String,
    pub(crate) selector_index: usize,
    pub(crate) constraint_expressions: Vec<Expression<F>>,
}

impl<F: Field> Argument<F> {
    /// Constructs a new trash argument.
    ///
    /// `table_map` is a sequence of `(input, table)` tuples.
    pub fn new(
        name: String,
        selector_index: usize,
        constraint_expressions: Vec<Expression<F>>,
    ) -> Self {
        Argument {
            name,
            selector_index,
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

    /// The selector index of this trash argument.
    pub fn selector_index(&self) -> &usize {
        &self.selector_index
    }

    /// The constraints of this trash argument.
    pub fn constraint_expressions(&self) -> &Vec<Expression<F>> {
        &self.constraint_expressions
    }
}

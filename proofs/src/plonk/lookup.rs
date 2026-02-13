use std::fmt::{self, Debug};

use ff::{Field, PrimeField};

use super::circuit::Expression;

pub(crate) mod prover;
pub(crate) mod verifier;

#[derive(Clone)]
pub struct Argument<F: Field> {
    pub(crate) name: String,
    pub(crate) input_expressions: Vec<Expression<F>>,
    pub(crate) table_expressions: Vec<Expression<F>>,
}

impl<F: Field> Debug for Argument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Argument")
            .field("input_expressions", &self.input_expressions)
            .field("table_expressions", &self.table_expressions)
            .finish()
    }
}

impl<F: Field> Argument<F> {
    /// Constructs a new lookup argument.
    ///
    /// `table_map` is a sequence of `(input, table)` tuples.
    pub fn new<S: AsRef<str>>(name: S, table_map: Vec<(Expression<F>, Expression<F>)>) -> Self {
        let (input_expressions, table_expressions) = table_map.into_iter().unzip();
        Argument {
            name: name.as_ref().to_string(),
            input_expressions,
            table_expressions,
        }
    }

    pub(crate) fn required_degree(&self) -> usize {
        assert_eq!(self.input_expressions.len(), self.table_expressions.len());

        // The first value in the permutation poly should be one.
        // degree 2:
        // l_0(X) * (1 - z(X)) = 0
        //
        // The "last" value in the permutation poly should be a boolean, for
        // completeness and soundness.
        // degree 3:
        // l_last(X) * (z(X)^2 - z(X)) = 0
        //
        // Enable the permutation argument for only the rows involved.
        // degree (2 + input_degree + table_degree) or 4, whichever is larger:
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
        //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1}
        //     s_0(X) + ... + s_{m-1}(X) + \gamma)
        // ) = 0
        //
        // The first two values of a' and s' should be the same.
        // degree 2:
        // l_0(X) * (a'(X) - s'(X)) = 0
        //
        // Either the two values are the same, or the previous
        // value of a' is the same as the current value.
        // degree 3:
        // (1 - (l_last(X) + l_blind(X))) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X))
        // = 0
        let mut input_degree = 1;
        for expr in self.input_expressions.iter() {
            input_degree = std::cmp::max(input_degree, expr.degree());
        }
        let mut table_degree = 1;
        for expr in self.table_expressions.iter() {
            table_degree = std::cmp::max(table_degree, expr.degree());
        }

        // In practice because input_degree and table_degree are initialized to
        // one, the latter half of this max() invocation is at least 4 always,
        // rendering this call pointless except to be explicit in case we change
        // the initialization of input_degree/table_degree in the future.
        std::cmp::max(
            // (1 - (l_last + l_blind)) z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            4,
            // (1 - (l_last + l_blind)) z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta)
            // (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            2 + input_degree + table_degree,
        )
    }

    /// Returns input of this argument
    pub fn input_expressions(&self) -> &Vec<Expression<F>> {
        &self.input_expressions
    }

    /// Returns table of this argument
    pub fn table_expressions(&self) -> &Vec<Expression<F>> {
        &self.table_expressions
    }

    /// Returns name of this argument
    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug)]
pub(crate) struct Evaluated<F: PrimeField> {
    product_eval: F,
    product_next_eval: F,
    permuted_input_eval: F,
    permuted_input_inv_eval: F,
    permuted_table_eval: F,
}

impl<F: PrimeField> Evaluated<F> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_0: F,
        l_last: F,
        l_blind: F,
        argument: &'a Argument<F>,
        theta: F,
        beta: F,
        gamma: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        let active_rows = F::ONE - (l_last + l_blind);

        let product_expression = || {
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X)
            //   + ... + s_{m-1}(X) + \gamma)
            let left = self.product_next_eval
                * &(self.permuted_input_eval + &beta)
                * &(self.permuted_table_eval + &gamma);

            let compress_expressions = |expressions: &[Expression<F>]| {
                expressions
                    .iter()
                    .map(|expression| {
                        expression.evaluate(
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
                    })
                    .fold(F::ZERO, |acc, eval| acc * &theta + &eval)
            };
            let right = self.product_eval
                * &(compress_expressions(&argument.input_expressions) + &beta)
                * &(compress_expressions(&argument.table_expressions) + &gamma);

            (left - &right) * &active_rows
        };

        std::iter::empty()
            .chain(
                // l_0(X) * (1 - z(X)) = 0
                Some(l_0 * &(F::ONE - &self.product_eval)),
            )
            .chain(
                // l_last(X) * (z(X)^2 - z(X)) = 0
                Some(l_last * &(self.product_eval.square() - &self.product_eval)),
            )
            .chain(
                // (1 - (l_last(X) + l_blind(X))) * (
                //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
                //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) +
                //     ... + s_{m-1}(X) + \gamma)
                // ) = 0
                Some(product_expression()),
            )
            .chain(Some(
                // l_0(X) * (a'(X) - s'(X)) = 0
                l_0 * &(self.permuted_input_eval - &self.permuted_table_eval),
            ))
            .chain(Some(
                // (1 - (l_last(X) + l_blind(X))) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0
                (self.permuted_input_eval - &self.permuted_table_eval)
                    * &(self.permuted_input_eval - &self.permuted_input_inv_eval)
                    * &active_rows,
            ))
    }
}

use std::fmt::{self, Debug};

use ff::Field;

use super::circuit::Expression;

pub(crate) mod prover;
pub(crate) mod verifier;

#[derive(Clone)]
/// Batched argument that supports multi-column logup, i.e., check that A_1,
/// ..., A_n \in T.
pub struct BatchedArgument<F: Field> {
    pub(crate) name: String,
    pub(crate) input_expressions: Vec<Vec<Expression<F>>>,
    pub(crate) table_expressions: Vec<Expression<F>>,
}

impl<F: Field> Debug for BatchedArgument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BatchedArgument")
            .field("input_expressions", &self.input_expressions)
            .field("table_expressions", &self.table_expressions)
            .finish()
    }
}

#[derive(Clone)]
/// Argument with guaranteed max size for input expressions depending on the CS
/// degree.
pub struct FlattenArgument<F: Field> {
    pub(crate) name: String,
    pub(crate) input_expressions: Vec<Vec<Expression<F>>>,
    pub(crate) table_expressions: Vec<Expression<F>>,
}

impl<F: Field> Debug for FlattenArgument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FlattenArgument")
            .field("name", &self.name)
            .field("input_expressions", &self.input_expressions)
            .field("table_expressions", &self.table_expressions)
            .finish()
    }
}

impl<F: Field> BatchedArgument<F> {
    /// Computes the number of parallel lookups that one argument can handle
    /// without exceeding the constraint system degree.
    ///
    /// A batched argument generates as many arguments as it can depending on the cs_degree.
    pub(crate) fn nb_parallel_lookups(&self, cs_degree: usize) -> usize {
        // Check if cs_degree is already one above a power of two, otherwise compute it.
        let max_degree = if (cs_degree - 1).is_power_of_two() {
            cs_degree
        } else {
            cs_degree.next_power_of_two() + 1
        };

        // Find the maximum degree across all input expressions
        let lookup_degree = self
            .input_expressions
            .iter()
            .flat_map(|exprs| exprs.iter().map(|expr| expr.degree()))
            .max()
            .unwrap_or(1);

        // The dominating factor of the lookup argument is:
        // h(X) * ∏_j(f_j(X) + β) = Σ_j ∏_{k≠j}(f_k(X) + β)
        // which has degree: 1 + lookup_degree * nb_parallel_lookups
        (max_degree - 1) / lookup_degree
    }

    /// Degree of the lookup argument after batching
    pub(crate) fn degree_batched_argument(&self, cs_degree: usize) -> usize {
        // Find the maximum degree across all input expressions
        let lookup_degree = self
            .input_expressions
            .iter()
            .flat_map(|exprs| exprs.iter().map(|expr| expr.degree()))
            .max()
            .unwrap_or(1);

        self.nb_parallel_lookups(cs_degree) * lookup_degree + 1
    }

    /// Constructs a new lookup argument.
    ///
    /// `table_map` is a sequence of `(input, table)` tuples.
    pub fn new<S: AsRef<str>>(
        name: S,
        table_map: Vec<(Vec<Expression<F>>, Expression<F>)>,
    ) -> Self {
        let (input_expressions, table_expressions): (Vec<Vec<Expression<F>>>, Vec<Expression<F>>) =
            table_map.into_iter().unzip();

        // The input expressions is a 2D array, where the first dimension represents the width
        // of the lookup, while the second represents the size of the parallel lookup (how many
        // columns are we looking up in a single table). The \theta batching happens over the
        // first dimension. Therefore, we transpose the array so that it is easier to handle later.
        let lookup_width = input_expressions.len();
        let nb_parallel_lookups = input_expressions[0].len();
        let mut transposed_input_expressions = vec![vec![Expression::Constant(F::ZERO); lookup_width]; nb_parallel_lookups];

        input_expressions.into_iter().enumerate().for_each(|(i, width)| {
            assert_eq!(width.len(), nb_parallel_lookups);
            width.into_iter().enumerate().for_each(|(j, parallel)| transposed_input_expressions[j][i] = parallel)
        });

        BatchedArgument {
            name: name.as_ref().to_string(),
            input_expressions: transposed_input_expressions,
            table_expressions,
        }
    }

    /// Splits the batched argument into values with the correct size
    pub fn split(&self, cs_degree: usize) -> Vec<FlattenArgument<F>> {
        assert_eq!(self.input_expressions[0].len(), self.table_expressions.len());
        let nb_lookups = self.nb_parallel_lookups(cs_degree);
        let chunk_size = (self.input_expressions.len() + nb_lookups - 1) / nb_lookups;
        self.input_expressions
            .chunks(chunk_size)
            .enumerate()
            .map(|(idx, chunk)| {
                FlattenArgument {
                    name: format!("{}-{:?}", self.name, idx),
                    input_expressions: chunk.to_vec(),
                    table_expressions: self.table_expressions.clone(),
                }}).collect()
    }
}

impl<F: Field> FlattenArgument<F> {
    /// Returns input of this argument
    pub fn input_expressions(&self) -> &Vec<Vec<Expression<F>>> {
        &self.input_expressions
    }

    /// Returns table of this argument
    pub fn table_expressions(&self) -> &Vec<Expression<F>> {
        &self.table_expressions
    }
}

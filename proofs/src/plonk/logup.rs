use std::cmp::max;
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
pub(crate) struct FlattenArgument<F: Field> {
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
    pub(crate) fn required_degree(&self) -> usize {
        let degrees = self.input_expressions.iter().flat_map(|e| e.iter().map(|e| e.degree()));
        max(3, degrees.max().unwrap_or(1) + 1)
    }
    /// Constructs a new logup argument.
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
    pub(crate) fn split(&self) -> Vec<FlattenArgument<F>> {
        // TODO: We are splitting in three. We should do depending on the degree of the
        // CS
        assert_eq!(self.input_expressions[0].len(), self.table_expressions.len());
        self.input_expressions
            .chunks(3)
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

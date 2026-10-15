//! The table side of a LogUp lookup: its evaluations and the classes of equal
//! tuples among its active rows. It depends on the fixed columns only, so it
//! can be built once per proving key.

use std::hash::Hash;

use ff::PrimeField;
use rustc_hash::FxHashMap;

use crate::poly::{LagrangeCoeff, Polynomial};

/// Evaluations of the table expressions and the tuples they form.
///
/// A tuple is a row of a set of polynomials, one per expression. Rows with the
/// same tuple form a class.
#[derive(Clone, Debug)]
pub(crate) struct TableSide<F> {
    /// The evaluation of each table expression.
    pub(crate) evals: Vec<Polynomial<F, LagrangeCoeff>>,
    /// Class of each active row.
    class_of_row: Vec<u32>,
    /// Class of each tuple of the table.
    classes: FxHashMap<Vec<F>, u32>,
    /// `1/t` for each class, where `t` is the number of rows in the class.
    class_size_inv: Vec<F>,
}

impl<F: PrimeField + Hash + Eq> TableSide<F> {
    /// The classes of the tuples among the first `usable_rows` rows of `evals`.
    pub(crate) fn new(evals: Vec<Polynomial<F, LagrangeCoeff>>, usable_rows: usize) -> Self {
        let mut classes = FxHashMap::<Vec<F>, u32>::default();
        let mut class_size = Vec::<u64>::new();
        let class_of_row = (0..usable_rows)
            .map(|row| {
                let tuple: Vec<F> = evals.iter().map(|column| column[row]).collect();
                let next = class_size.len() as u32;
                let class = *classes.entry(tuple).or_insert(next);
                if class == next {
                    class_size.push(0);
                }
                class_size[class as usize] += 1;
                class
            })
            .collect();
        let class_size_inv =
            class_size.into_iter().map(|t| F::from(t).invert().unwrap()).collect();

        Self {
            evals,
            class_of_row,
            classes,
            class_size_inv,
        }
    }

    /// Computes the multiplicity of each table tuple among the input tuples.
    ///
    /// Row `r` of `values[j]` is the `r`-th tuple of the `j`-th input. Returns
    /// a vector where `result[i]` is the number of times the `i`-th table
    /// tuple appears among the selected input tuples.
    ///
    /// When a tuple appears multiple times in the table, the multiplicity is
    /// normalized: if a tuple is looked up `k` times and appears `t` times in
    /// the table, each table position gets multiplicity `k/t`.
    ///
    /// Only tuples in the first `usable_rows` are counted for both inputs and
    /// table. Blinding rows are excluded from the counting but still get a
    /// multiplicity value (zero for tuples not in the active region).
    ///
    /// # Panics
    ///
    /// Panics if any selected input tuple (where the selector is non-zero) is
    /// not present in the table, or if an input does not have as many
    /// polynomials as the table.
    pub(crate) fn multiplicities(
        &self,
        selector: &Polynomial<F, LagrangeCoeff>,
        values: &[&[Polynomial<F, LagrangeCoeff>]],
        usable_rows: usize,
        blinding_values: &[F],
    ) -> Vec<F> {
        let n = selector.len();
        assert_eq!(blinding_values.len(), n - usable_rows);

        // Count how many times each class appears in inputs (only where the
        // selector is non-zero).
        let mut input_counts = vec![0u64; self.class_size_inv.len()];
        let mut tuple = Vec::with_capacity(self.evals.len());
        for input in values.iter() {
            assert_eq!(
                input.len(),
                self.evals.len(),
                "an input and the table have different widths"
            );
            for row in (0..usable_rows).filter(|&row| !selector[row].is_zero_vartime()) {
                tuple.clear();
                tuple.extend(input.iter().map(|column| column[row]));
                let class = self
                    .classes
                    .get(tuple.as_slice())
                    .unwrap_or_else(|| panic!("input tuple {tuple:?} not found in lookup table"));
                input_counts[*class as usize] += 1;
            }
        }

        // Normalized multiplicities: input_count / table_count. Blinding rows
        // get random values to ensure ZK.
        (0..n)
            .map(|i| match self.class_of_row.get(i) {
                Some(&class) => {
                    F::from(input_counts[class as usize]) * self.class_size_inv[class as usize]
                }
                None => blinding_values[i - usable_rows],
            })
            .collect()
    }
}

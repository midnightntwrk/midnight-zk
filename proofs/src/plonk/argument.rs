use ff::PrimeField;

use crate::{plonk::ConstraintSystem, poly::PolynomialLabel};

pub(crate) mod prover;
pub(crate) mod verifier;

#[derive(Copy, Clone, Debug)]
pub(crate) struct Evaluation<F> {
    point: F,
    eval: F,
}

impl<F: PrimeField> Evaluation<F> {
    pub fn eval(&self) -> F {
        self.eval
    }
}

/// The evaluation points at which the polynomial of the given label needs to be
/// evaluated, among `x`, `x_next = omega * x` and
/// `x_last = omega^-(blinding_factors + 1) * x`.
///
/// The opening points are argument-specific, but they are all listed here so
/// that a single implementation serves the whole group, with no trait to
/// dispatch on: `PolynomialLabel` is defined outside the arguments and already
/// names their specifics, so the label alone decides.
pub(crate) fn eval_points<F: PrimeField>(
    cs: &ConstraintSystem<F>,
    label: &PolynomialLabel,
    x: F,
    x_next: F,
    x_last: F,
) -> Vec<F> {
    match label {
        PolynomialLabel::PermutationFixed(_) => vec![x],
        PolynomialLabel::PermutationAccumulator(i) => {
            // Every set but the last is also opened at the last usable row, to
            // chain it to the next one.
            if i + 1 < cs.permutation().num_sets(cs.degree()) {
                vec![x, x_next, x_last]
            } else {
                vec![x, x_next]
            }
        }
        PolynomialLabel::LogupMultiplicities(_) => vec![x],
        PolynomialLabel::LogupHelper(_, _) => vec![x],
        PolynomialLabel::LogupAggregator(_) => vec![x, x_next],
        PolynomialLabel::Trash(_) => vec![x],
        _ => unreachable!(),
    }
}

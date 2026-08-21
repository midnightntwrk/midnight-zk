use ff::PrimeField;

use crate::poly::PolynomialLabel;

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
/// evaluated.
///
/// The opening points are argument-specific, but they are all listed here so
/// that a single implementation serves the whole group, with no trait to
/// dispatch on: `PolynomialLabel` is defined outside the arguments and already
/// names their specifics, so the label alone decides.
fn eval_points<F: PrimeField>(label: &PolynomialLabel, x: F, omega: F) -> Vec<F> {
    match label {
        PolynomialLabel::LogupMultiplicities(_) => vec![x],
        PolynomialLabel::LogupHelper(_, _) => vec![x],
        PolynomialLabel::LogupAggregator(_) => vec![x, omega * x],
        PolynomialLabel::Trash(_) => vec![x],
        _ => unreachable!(),
    }
}

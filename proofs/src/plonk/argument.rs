use std::collections::{BTreeMap, BTreeSet};

use ff::PrimeField;

use crate::{
    plonk::ConstraintSystem,
    poly::{PolynomialLabel, Rotation},
};

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

/// Every rotation of `x` at which a polynomial of `cs` is opened: those
/// [`eval_points`] may use, and those of the instance and fixed queries.
pub(crate) fn rotations<F: PrimeField>(cs: &ConstraintSystem<F>) -> BTreeSet<Rotation> {
    [
        Rotation::cur(),
        Rotation::next(),
        Rotation(-((cs.blinding_factors() + 1) as i32)),
    ]
    .into_iter()
    .chain(cs.advice_queries.iter().map(|&(_, rotation)| rotation))
    .chain(cs.instance_queries.iter().map(|&(_, rotation)| rotation))
    .chain(cs.fixed_queries.iter().map(|&(_, rotation)| rotation))
    .collect()
}

/// The evaluation points at which the polynomial of the given label needs to be
/// evaluated, taken from `x_rotations`: `x` rotated by each of [`rotations`].
///
/// The opening points are argument-specific, but they are all listed here so
/// that a single implementation serves the whole group, with no trait to
/// dispatch on: `PolynomialLabel` is defined outside the arguments and already
/// names their specifics, so the label alone decides.
pub(crate) fn eval_points<F: PrimeField>(
    cs: &ConstraintSystem<F>,
    label: &PolynomialLabel,
    x_rotations: &BTreeMap<Rotation, F>,
) -> Vec<F> {
    let at = |rotation: Rotation| x_rotations[&rotation];
    match label {
        PolynomialLabel::Fixed(i) => cs
            .fixed_queries
            .iter()
            .filter(|(column, _)| column.index() == *i)
            .map(|&(_, rotation)| at(rotation))
            .collect(),
        PolynomialLabel::Advice(i) => cs
            .advice_queries
            .iter()
            .filter(|(column, _)| column.index() == *i)
            .map(|&(_, rotation)| at(rotation))
            .collect(),
        PolynomialLabel::PermutationFixed(_) => vec![at(Rotation::cur())],
        PolynomialLabel::PermutationAccumulator(i) => {
            // Every set but the last is also opened at the last usable row, to
            // chain it to the next one.
            if i + 1 < cs.permutation().num_sets(cs.degree()) {
                vec![
                    at(Rotation::cur()),
                    at(Rotation::next()),
                    at(Rotation(-((cs.blinding_factors() + 1) as i32))),
                ]
            } else {
                vec![at(Rotation::cur()), at(Rotation::next())]
            }
        }
        PolynomialLabel::LogupMultiplicities(_) => vec![at(Rotation::cur())],
        PolynomialLabel::LogupHelper(_, _) => vec![at(Rotation::cur())],
        PolynomialLabel::LogupAggregator(_) => vec![at(Rotation::cur()), at(Rotation::next())],
        PolynomialLabel::Trash(_) => vec![at(Rotation::cur())],
        _ => unreachable!(),
    }
}

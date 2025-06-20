use midnight_proofs::{
    circuit::Layouter,
    plonk::{Error, Expression},
};

use crate::{
    instructions::{ArithInstructions, AssignmentInstructions},
    verifier::types::{AssignedScalar, ScalarChip, SelfEmulationCurve},
};

pub(crate) mod lookup;
pub(crate) mod permutation;

/// Function to evaluate expressions in-circuit.
pub(crate) fn eval_expression<C: SelfEmulationCurve>(
    layouter: &mut impl Layouter<C::ScalarExt>,
    scalar_chip: &ScalarChip<C>,
    advice: &[AssignedScalar<C>],   // advice evals
    fixed: &[AssignedScalar<C>],    // fixed evals
    instance: &[AssignedScalar<C>], // instance evals
    expr: &Expression<C::ScalarExt>,
) -> Result<AssignedScalar<C>, Error> {
    match expr {
        Expression::Constant(k) => scalar_chip.assign_fixed(layouter, *k),
        Expression::Selector(_) => {
            panic!("Virtual selector are removed during optimisation")
        }
        Expression::Fixed(query) => Ok(fixed[query.index().unwrap()].clone()),
        Expression::Advice(query) => Ok(advice[query.index.unwrap()].clone()),
        Expression::Instance(query) => Ok(instance[query.index.unwrap()].clone()),
        Expression::Challenge(_) => panic!("We do not suport multi-phase yet"),
        Expression::Negated(e) => {
            let val = eval_expression::<C>(layouter, scalar_chip, advice, fixed, instance, e)?;
            scalar_chip.neg(layouter, &val)
        }
        Expression::Sum(e1, e2) => {
            let e1 = eval_expression::<C>(layouter, scalar_chip, advice, fixed, instance, e1)?;
            let e2 = eval_expression::<C>(layouter, scalar_chip, advice, fixed, instance, e2)?;
            scalar_chip.add(layouter, &e1, &e2)
        }
        Expression::Product(e1, e2) => {
            let val1 = eval_expression::<C>(layouter, scalar_chip, advice, fixed, instance, e1)?;
            let val2 = eval_expression::<C>(layouter, scalar_chip, advice, fixed, instance, e2)?;
            scalar_chip.mul(layouter, &val1, &val2, None)
        }
        Expression::Scaled(e, k) => {
            let val = eval_expression::<C>(layouter, scalar_chip, advice, fixed, instance, e)?;
            scalar_chip.mul_by_constant(layouter, &val, *k)
        }
    }
}

use ff::WithSmallOrderMulGroup;

use crate::{
    plonk::evaluation::{FlatGraphEvaluator, get_rotation_idx},
    poly::{EvaluationDomain, LagrangeCoeff, Polynomial},
    utils::arithmetic::parallelize,
};

/// The trash polynomial of an argument: on every row, the Horner compression
/// by `trash_challenge` of its constraint expressions, as evaluated by
/// `evaluator`, the argument's flat evaluator.
pub(crate) fn compute_trash_poly<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    evaluator: &FlatGraphEvaluator<F>,
    trash_challenge: F,
    advice_values: &[Polynomial<F, LagrangeCoeff>],
    fixed_values: &[Polynomial<F, LagrangeCoeff>],
    instance_values: &[Polynomial<F, LagrangeCoeff>],
) -> Polynomial<F, LagrangeCoeff> {
    let log_n = domain.k();
    let mut values = vec![F::ZERO; domain.n as usize];
    parallelize(&mut values, |values, start| {
        let mut buffer =
            evaluator.new_values_buffer(&F::ZERO, &F::ZERO, &trash_challenge, &F::ZERO);
        let mut rotations = vec![0; evaluator.rotations.len()];
        for (i, value) in values.iter_mut().enumerate() {
            let idx = start + i;
            for (r, rotation) in evaluator.rotations.iter().enumerate() {
                rotations[r] = get_rotation_idx(idx, *rotation, 0, log_n);
            }
            *value = evaluator.evaluate::<LagrangeCoeff>(
                &mut buffer,
                fixed_values,
                advice_values,
                instance_values,
                &rotations,
                &F::ZERO,
            );
        }
    });
    domain.lagrange_from_vec(values)
}

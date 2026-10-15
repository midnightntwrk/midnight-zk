use ff::WithSmallOrderMulGroup;

use crate::{
    plonk::evaluation::{FlatGraphEvaluator, get_rotation_idx},
    poly::{EvaluationDomain, LagrangeCoeff, Polynomial},
    utils::arithmetic::parallelize,
};

/// Computes `Σ_j c^{m-1-j} · e_j` over the rows, for the constraint
/// expressions `e_j` of a trashcan. `flat` is the flattened graph of
/// [`GraphEvaluator::for_trash`](crate::plonk::evaluation::GraphEvaluator::for_trash)
/// and `trash_powers` are `(1, c, ..., c^{m-1})`.
pub(crate) fn compute_trash_poly<F: WithSmallOrderMulGroup<3>>(
    flat: &FlatGraphEvaluator<F>,
    domain: &EvaluationDomain<F>,
    trash_powers: &[F],
    advice_values: &[Polynomial<F, LagrangeCoeff>],
    fixed_values: &[Polynomial<F, LagrangeCoeff>],
    instance_values: &[Polynomial<F, LagrangeCoeff>],
) -> Polynomial<F, LagrangeCoeff> {
    let n = domain.n as usize;
    let log_n = n.ilog2();
    let mut poly = domain.empty_lagrange();

    parallelize(&mut poly, |values, start| {
        let mut buf = flat.new_values_buffer(&F::ZERO, &[], trash_powers, &[]);
        let mut rots = vec![0usize; flat.rotations.len()];
        for (i, value) in values.iter_mut().enumerate() {
            for (r, rot) in rots.iter_mut().zip(&flat.rotations) {
                *r = get_rotation_idx(start + i, *rot, 0, log_n);
            }
            *value = flat.evaluate::<LagrangeCoeff>(
                &mut buf,
                fixed_values,
                advice_values,
                instance_values,
                &rots,
                &F::ZERO,
            );
        }
    });
    poly
}

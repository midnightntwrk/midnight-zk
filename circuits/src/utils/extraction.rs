//! Utils related to extraction

use extractor_support::{
    circuit::injected::InjectedIR,
    ir::{expr::IRBexpr, CmpOp},
};
use midnight_proofs::{circuit::RegionIndex, plonk::Expression};

/// Short name for the injected IR map.
pub type IR<F> = InjectedIR<RegionIndex, Expression<F>>;

#[inline]
pub fn eq_expr<T>(lhs: T, rhs: T) -> IRBexpr<T> {
    IRBexpr::Cmp(CmpOp::Eq, lhs, rhs)
}

#[inline]
pub fn eq_expr_row<T>(row: usize, lhs: T, rhs: T) -> IRBexpr<(usize, T)> {
    eq_expr((row, lhs), (row, rhs))
}

#[inline]
pub fn cexpr<F>(i: impl Into<F>) -> Expression<F> {
    Expression::Constant(i.into())
}

#[inline]
pub fn implies<T>(lhs: IRBexpr<T>, rhs: IRBexpr<T>) -> IRBexpr<T> {
    IRBexpr::Implies(Box::new(lhs), Box::new(rhs))
}

//! Utils related to extraction

use extractor_support::{circuit::injected::InjectedIR, ir::stmt::IRStmt};
use midnight_proofs::{
    circuit::{Cell, RegionIndex},
    plonk::Expression,
};

mod sealed {
    pub trait Sealed {}
}

/// Short name for the injected IR map.
pub type IR<F> = InjectedIR<RegionIndex, Expression<F>>;

impl<F> sealed::Sealed for IR<F> {}

pub trait IRExt<F>: sealed::Sealed {
    fn inject(&mut self, index: RegionIndex, stmt: IRStmt<(usize, Expression<F>)>);

    fn inject_in_cell(&mut self, cell: Cell, stmt: IRStmt<Expression<F>>) {
        self.inject(cell.region_index, stmt.with(cell.row_offset))
    }

    fn inject_many_in_cell(
        &mut self,
        cell: Cell,
        stmts: impl IntoIterator<Item = IRStmt<Expression<F>>>,
    );
}

impl<F> IRExt<F> for IR<F> {
    fn inject(&mut self, index: RegionIndex, stmt: IRStmt<(usize, Expression<F>)>) {
        self.entry(index).or_default().push(stmt)
    }

    fn inject_many_in_cell(
        &mut self,
        cell: Cell,
        stmts: impl IntoIterator<Item = IRStmt<Expression<F>>>,
    ) {
        self.entry(cell.region_index)
            .or_default()
            .extend(stmts.into_iter().map(|stmt| stmt.with(cell.row_offset)))
    }
}

//! Traits and types for storing arbitrary types into cells in a circuit.

use ff::{Field, PrimeField};
use midnight_proofs::circuit::{AssignedCell, Layouter};

use crate::{
    cells::{CellReprSize, ctx::OCtx},
    circuit::injected::InjectedIR,
    error::Error,
};

/// Trait for serializing arbitrary types to a set of circuit cells.
pub trait StoreIntoCells<F: Field, C>: CellReprSize {
    /// Stores an instance of Self into a set of cells.
    fn store(
        self,
        ctx: &mut OCtx,
        chip: &C,
        layouter: &mut impl Layouter<F>,
        injected_ir: &mut InjectedIR<F>,
    ) -> Result<(), Error>;
}

impl<F: PrimeField, C> StoreIntoCells<F, C> for AssignedCell<F, F> {
    fn store(
        self,
        ctx: &mut OCtx,
        _: &C,
        layouter: &mut impl Layouter<F>,
        _: &mut InjectedIR<F>,
    ) -> Result<(), Error> {
        ctx.assign_next(self, layouter)
    }
}

impl<const N: usize, F: PrimeField, C, T: StoreIntoCells<F, C>> StoreIntoCells<F, C> for [T; N] {
    fn store(
        self,
        ctx: &mut OCtx,
        chip: &C,
        layouter: &mut impl Layouter<F>,
        injected_ir: &mut InjectedIR<F>,
    ) -> Result<(), Error> {
        self.into_iter().try_for_each(|t| t.store(ctx, chip, layouter, injected_ir))
    }
}

impl<F: Field, C> StoreIntoCells<F, C> for () {
    fn store(
        self,
        _ctx: &mut OCtx,
        _chip: &C,
        _layouter: &mut impl Layouter<F>,
        _injected_ir: &mut InjectedIR<F>,
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl<F: Field, C, A1: StoreIntoCells<F, C>, A2: StoreIntoCells<F, C>> StoreIntoCells<F, C>
    for (A1, A2)
{
    fn store(
        self,
        ctx: &mut OCtx,
        chip: &C,
        layouter: &mut impl Layouter<F>,
        injected_ir: &mut InjectedIR<F>,
    ) -> Result<(), Error> {
        self.0.store(ctx, chip, layouter, injected_ir)?;
        self.1.store(ctx, chip, layouter, injected_ir)
    }
}

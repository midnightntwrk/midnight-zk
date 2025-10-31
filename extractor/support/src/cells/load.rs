//! Traits and types for loading arbitrary types from cells in a circuit.

use std::mem::MaybeUninit;

use ff::{Field, PrimeField};
use midnight_proofs::circuit::{AssignedCell, Layouter};
use num_bigint::BigUint;

use crate::{
    cells::{CellReprSize, ctx::ICtx},
    circuit::injected::InjectedIR,
    error::Error,
};

/// Trait for deserializing arbitrary types from a set of circuit cells.
pub trait LoadFromCells<F: Field, C>: Sized + CellReprSize {
    /// Loads an instance of Self from a set of cells.
    fn load(
        ctx: &mut ICtx,
        chip: &C,
        layouter: &mut impl Layouter<F>,
        injected_ir: &mut InjectedIR<F>,
    ) -> Result<Self, Error>;
}

impl<F: PrimeField, C> LoadFromCells<F, C> for AssignedCell<F, F> {
    fn load(
        ctx: &mut ICtx,
        _: &C,
        layouter: &mut impl Layouter<F>,
        _: &mut InjectedIR<F>,
    ) -> Result<Self, Error> {
        ctx.assign_next(layouter)
    }
}

impl<const N: usize, F: PrimeField, C, T: LoadFromCells<F, C>> LoadFromCells<F, C> for [T; N] {
    fn load(
        ctx: &mut ICtx,
        chip: &C,
        layouter: &mut impl Layouter<F>,
        injected_ir: &mut InjectedIR<F>,
    ) -> Result<Self, Error> {
        let mut out: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];
        for e in &mut out[..] {
            e.write(T::load(ctx, chip, layouter, injected_ir)?);
        }
        Ok(out.map(|e| unsafe { e.assume_init() }))
    }
}

macro_rules! load_const {
    ($t:ty) => {
        impl<C, F: PrimeField> LoadFromCells<F, C> for $t {
            fn load(
                ctx: &mut ICtx,
                _chip: &C,
                _layouter: &mut impl Layouter<F>,
                _injected_ir: &mut InjectedIR<F>,
            ) -> Result<Self, Error> {
                ctx.primitive_constant()
            }
        }
    };
}

load_const!(bool);
load_const!(u8);
load_const!(usize);
load_const!(BigUint);

impl<F: Field, C> LoadFromCells<F, C> for () {
    fn load(
        _: &mut ICtx,
        _: &C,
        _: &mut impl Layouter<F>,
        _: &mut InjectedIR<F>,
    ) -> Result<Self, Error> {
        Ok(())
    }
}

macro_rules! load_tuple {
    ($($t:ident),+) => {
        impl<F:Field,C,$( $t: LoadFromCells<F,C>, )+> LoadFromCells<F,C> for (
                $( $t, )+
            )
        {
            fn load(
                ctx: &mut ICtx,
                chip: &C,
                layouter: &mut impl Layouter<F>,
                injected_ir: &mut InjectedIR<F>,
            ) -> Result<Self, Error> {
                Ok(($( $t::load(ctx, chip, layouter, injected_ir)?, )+))
            }
        }
    };
}

load_tuple!(A1, A2);
load_tuple!(A1, A2, A3);
load_tuple!(A1, A2, A3, A4);
load_tuple!(A1, A2, A3, A4, A5);

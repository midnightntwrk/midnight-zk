//! Supporting types for loading and storing from cells.

use std::{
    ops::{Deref, DerefMut},
    str::FromStr,
};

use ff::{Field, PrimeField};
use midnight_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Any, Column, ColumnType, Instance},
};

use crate::{error::Error, parse_field};

/// A cell in the table.
#[derive(Debug)]
pub struct Cell<C: ColumnType> {
    col: Column<C>,
    row: usize,
}

impl<C: ColumnType> Cell<C> {
    /// Creates a new cell.
    pub fn new(col: Column<C>, row: usize) -> Self {
        Self { col, row }
    }

    /// Creates a new cell in row 0.
    pub fn first_row(col: Column<C>) -> Self {
        Self::new(col, 0)
    }

    /// Returns the column of the cell.
    pub fn col(&self) -> Column<C> {
        self.col
    }

    /// Returns the row of the cell.
    pub fn row(&self) -> usize {
        self.row
    }
}

impl<C: ColumnType> From<(Column<C>, usize)> for Cell<C> {
    fn from((col, row): (Column<C>, usize)) -> Self {
        Self::new(col, row)
    }
}

/// A description for an input. Comprises an instance cell that represents the
/// actual input and an advice cell that is used for integrating better with
/// regions.
#[derive(Debug)]
pub struct InputDescr {
    cell: Cell<Any>,
    temp: Cell<Advice>,
}

impl InputDescr {
    /// Creates a new input description.
    pub fn new(cell: Cell<Any>, temp: Column<Advice>) -> Self {
        Self {
            cell,
            temp: Cell::first_row(temp),
        }
    }

    /// Returns the column of the instance cell.
    pub fn col(&self) -> Column<Any> {
        self.cell.col()
    }

    /// Tries to cast the column to the expected type.
    pub fn try_col<C, E>(&self) -> Result<Column<C>, Error>
    where
        C: ColumnType,
        Column<Any>: TryInto<Column<C>, Error = E>,
        Error: From<E>,
    {
        Ok(self.col().try_into()?)
    }

    /// Returns the row of the instance cell.
    pub fn row(&self) -> usize {
        self.cell.row()
    }

    /// Returns the column of the helper advice cell.
    pub fn temp(&self) -> Column<Advice> {
        self.temp.col()
    }

    /// Returns the row of the helper advice cell.
    pub fn temp_offset(&self) -> usize {
        self.temp.row()
    }
}

impl From<OutputDescr> for InputDescr {
    fn from(descr: OutputDescr) -> Self {
        InputDescr {
            cell: (Column::<Any>::from(descr.cell.col()), descr.cell.row).into(),
            temp: descr.helper,
        }
    }
}

/// A description for an output. Comprises an instance cell acting as the output
/// and a support advice cell.
#[derive(Debug)]
pub struct OutputDescr {
    cell: Cell<Instance>,
    helper: Cell<Advice>,
}

impl OutputDescr {
    /// Creates a new output description.
    pub fn new(cell: Cell<Instance>, helper: Column<Advice>) -> Self {
        Self {
            cell,
            helper: Cell {
                col: helper,
                row: 0,
            },
        }
    }

    fn set_to_zero<F: Field>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let helper_cell = layouter.assign_region(
            || "output == 0",
            |mut region| {
                region.assign_advice_from_constant(
                    || "helper",
                    self.helper.col,
                    self.helper.row,
                    F::ZERO,
                )
            },
        )?;
        log::debug!("Output {self:?} was constrained to be equal to zero");
        layouter.constrain_instance(helper_cell.cell(), self.cell.col, self.cell.row)?;
        Ok(())
    }

    fn assign<F: Field, V>(
        &self,
        value: impl Into<AssignedCell<V, F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let cell = value.into();
        log::debug!(
            "Constraining instance cell ({}, {}) to be equal to {:?}",
            self.cell.col().index(),
            self.cell.row(),
            cell.cell()
        );
        layouter.constrain_instance(cell.cell(), self.cell.col(), self.cell.row())?;
        Ok(())
    }
}

/// Context type for the [`LoadFromCells`] and [`StoreIntoCells`] traits.
pub struct IOCtx<'io, IO> {
    io: Box<dyn Iterator<Item = IO> + 'io>,
}

impl<'io, IO> IOCtx<'io, IO> {
    /// Creates a new IO context.
    pub fn new(io: impl Iterator<Item = IO> + 'io) -> Self {
        Self { io: Box::new(io) }
    }

    /// Returns the next IO object or fails if there aren't any more objects.
    pub fn next(&mut self) -> Result<IO, Error> {
        self.io.next().ok_or_else(|| Error::NotEnoughIOCells)
    }
}

impl<IO> std::fmt::Debug for IOCtx<'_, IO> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IOCtx").field("io", &"<iterator>").finish()
    }
}

/// Context type for the [`LoadFromCells`] trait.
pub struct ICtx<'i, 's> {
    inner: IOCtx<'i, InputDescr>,
    constants: Box<dyn Iterator<Item = &'s str> + 's>,
}

impl<'i, 's> ICtx<'i, 's> {
    /// Creates a new input context.
    pub fn new(i: impl Iterator<Item = InputDescr> + 'i, constants: &'s [String]) -> Self {
        Self {
            inner: IOCtx::new(i),
            constants: Box::new(constants.iter().map(|s| s.as_str())),
        }
    }

    /// Tries to parse a constant as a field element.
    pub fn field_constant<F: PrimeField>(&mut self) -> Result<F, Error> {
        self.constants
            .next()
            .ok_or_else(|| Error::NotEnoughConstants)
            .and_then(parse_field::<F>)
    }

    /// Tries to parse a primitive constant.
    pub fn primitive_constant<T, E>(&mut self) -> Result<T, Error>
    where
        T: FromStr<Err = E>,
        Error: From<E>,
    {
        Ok(T::from_str(
            self.constants.next().ok_or_else(|| Error::NotEnoughConstants)?,
        )?)
    }

    /// Assigns the next input to a cell.
    pub fn assign_next<F: PrimeField>(
        &mut self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let i = self.next()?;
        Ok(layouter.assign_region(
            || "ins",
            |mut region| {
                region.assign_advice_from_instance(
                    || "input",
                    i.try_col()?,
                    i.row(),
                    i.temp(),
                    i.temp_offset(),
                )
            },
        )?)
    }
}

impl<'i> Deref for ICtx<'i, '_> {
    type Target = IOCtx<'i, InputDescr>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for ICtx<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl std::fmt::Debug for ICtx<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ICtx")
            .field("inner", &self.inner)
            .field("constants", &"<iterator>")
            .finish()
    }
}

/// Context type for the [`StoreIntoCells`] trait.
#[derive(Debug)]
pub struct OCtx<'o> {
    inner: IOCtx<'o, OutputDescr>,
}

impl<'o> OCtx<'o> {
    /// Creates a new output context.
    pub fn new(input: impl Iterator<Item = OutputDescr> + 'o) -> Self {
        Self {
            inner: IOCtx::new(input),
        }
    }

    /// Sets the next output to zero.
    pub fn set_next_to_zero<F: Field>(
        &mut self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        self.next()?.set_to_zero(layouter)
    }

    /// Sets the next output to the given value.
    pub fn assign_next<F, V>(
        &mut self,
        value: impl Into<AssignedCell<V, F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error>
    where
        F: PrimeField,
    {
        self.next()?.assign(value, layouter)
    }
}

impl<'o> Deref for OCtx<'o> {
    type Target = IOCtx<'o, OutputDescr>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for OCtx<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

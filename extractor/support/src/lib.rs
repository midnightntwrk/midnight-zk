//! Support crate for integrating the extractor.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use halo2_llzk_frontend::ir::{stmt::IRStmt, CmpOp};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{AssignedCell, Cell, RegionIndex},
    plonk::Expression,
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::Num as _;

use crate::error::Error;

pub mod cells;
pub mod circuit;
pub mod error;
pub mod fields;
pub mod macros;

pub mod ir {
    //! Re-export of IR types from the frontend.
    pub use halo2_llzk_frontend::ir::*;
}

/// Parses a value of F from the given string.
pub fn parse_field<F: PrimeField>(s: &str) -> Result<F, Error> {
    if s.is_empty() {
        return Err(Error::FieldParsingError);
    }
    let ten = F::from(10);
    s.chars()
        .map(|c| c.to_digit(10).ok_or(Error::FieldParsingError))
        .map(|r| r.map(u64::from))
        .map(|r| r.map(F::from))
        .fold(Ok(F::ZERO), |acc, c| Ok(acc? * ten + c?))
}

fn modulus<F: PrimeField>() -> BigUint {
    BigUint::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

/// Converts a big unsigned integer into a prime field element.
pub fn big_to_fe<F: PrimeField>(e: BigUint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

/// Converts a prime field element into a big unsigned integer.
pub fn fe_to_big<F: PrimeField>(fe: F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}

/// Creates an [`Expression`] that queries the given cell relative to the beginning of the cell's
/// region.
pub fn cell_to_expr<F: PrimeField>(x: &AssignedCell<F, F>) -> Result<Expression<F>, Error> {
    cell_to_expr_inner(x.cell())
}

fn cell_to_expr_inner<F: PrimeField>(c: Cell) -> Result<Expression<F>, Error> {
    Ok(c.column.query_cell::<F>(Rotation(c.row_offset.try_into()?)))
}

/// Convenience method for creating a less-than constraint between a cell and a constant.
pub fn injectable_less_than<F: PrimeField>(
    cell: Cell,
    constant: F,
) -> Result<(RegionIndex, IRStmt<(usize, Expression<F>)>), Error> {
    let lhs = cell_to_expr_inner(cell)?;
    let rhs = Expression::Constant(constant);
    Ok((
        cell.region_index,
        IRStmt::constraint(CmpOp::Lt, (cell.row_offset, lhs), (cell.row_offset, rhs)),
    ))
}

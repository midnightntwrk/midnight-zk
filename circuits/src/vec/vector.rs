// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::ops::Range;

use ff::PrimeField;
use midnight_proofs::circuit::Value;

use crate::{
    field::AssignedNative,
    types::{AssignedByte, InnerValue},
    utils::util::fe_to_big,
};

/// A variable-length vector of elements of type T, with size bound M.
/// - `len` is the (potentially secret) effective length of the vector, its
///   value is guaranteed to be in the range `[0, M]`.
/// - `buffer` is the padded payload of this vector; it contains the effective
///   data of the vector as well as filler values, which are UNCONSTRAINED.
///
/// The effective payload in the data is aligned in A sized chunks. This
/// enables more efficient implementations of instructions like hashing
/// over this type. As a result of this alignment, the data may contain filler
/// values before and after the effective payload. The padding in front of
/// the payload will always be 0 mod A, so that the payload begins aligned in A
/// sized chunks. The padding at the end of the payload will be have a size in
/// [0, A) such that | front_pad | + | payload | + | back_pad | = M.
#[derive(Clone, Debug)]
pub struct AssignedVector<F: PrimeField, T: Vectorizable, const M: usize, const A: usize> {
    /// Padded payload of the vector.
    ///
    /// Made public for extraction.
    pub buffer: [T; M],

    /// Effective length of the vector.
    ///
    /// Made public for extraction.
    pub len: AssignedNative<F>,
}

/// Returns the range where the data should be placed in the buffer.
pub fn get_lims<const M: usize, const A: usize>(len: usize) -> Range<usize> {
    let final_pad_len = (A - (len % A)) % A;
    M - len - final_pad_len..M - final_pad_len
}

impl<F: PrimeField, const M: usize, T: Vectorizable, const A: usize> InnerValue
    for AssignedVector<F, T, M, A>
{
    type Element = Vec<T::Element>;

    fn value(&self) -> Value<Self::Element> {
        let data = Value::<Vec<T::Element>>::from_iter(self.buffer.iter().map(|v| v.value()));
        let idxs: Value<_> = self.len.value().map(|len| {
            let len: usize = fe_to_big(*len).try_into().unwrap();

            let end_pad = (A - (len % A)) % A;
            (M - len - end_pad, M - end_pad)
        });
        data.zip(idxs).map(|(data, idxs)| data[idxs.0..idxs.1].to_vec())
    }
}

/// Trait for the individual elements of an AssignedVector.
pub trait Vectorizable: InnerValue {
    /// Value to fill the space in the buffer that is not occupied with vector
    /// data.
    const FILLER: Self::Element;
}

impl<F: PrimeField> Vectorizable for AssignedNative<F> {
    const FILLER: F = F::ZERO;
}

impl<F: PrimeField> Vectorizable for AssignedByte<F> {
    const FILLER: u8 = 0u8;
}

#[cfg(feature = "extraction")]
pub mod extraction {
    //! Extraction specific logic related to the vector gadget.

    use extractor_support::{
        cell_to_expr,
        cells::{
            ctx::{ICtx, OCtx},
            load::LoadFromCells,
            store::StoreIntoCells,
            CellReprSize,
        },
        circuit::injected::InjectedIR,
        error::Error,
        ir::{expr::IRBexpr, stmt::IRStmt, CmpOp},
    };
    use ff::{Field, PrimeField};
    use midnight_proofs::{
        circuit::{Cell, Layouter},
        plonk::{Any, Column, ColumnType, Expression},
    };

    use crate::{field::AssignedNative, types::AssignedByte, vec::get_lims};

    use super::{AssignedVector, Vectorizable};

    impl<F: PrimeField, T: Vectorizable + CellReprSize, const M: usize, const A: usize> CellReprSize
        for AssignedVector<F, T, M, A>
    {
        const SIZE: usize = T::SIZE * M + AssignedNative::<F>::SIZE;
    }

    impl<
            F: PrimeField,
            C,
            T: Vectorizable + LoadFromCells<F, C>,
            const M: usize,
            const A: usize,
        > LoadFromCells<F, C> for AssignedVector<F, T, M, A>
    {
        fn load(
            ctx: &mut ICtx,
            chip: &C,
            layouter: &mut impl Layouter<F>,
            injected_ir: &mut InjectedIR<F>,
        ) -> Result<Self, Error> {
            let buffer = <[T; M]>::load(ctx, chip, layouter, injected_ir)?;
            let len = AssignedNative::load(ctx, chip, layouter, injected_ir)?;
            let lhs = cell_to_expr(&len)?;
            let rhs = Expression::Constant(F::from(M.try_into().unwrap()));
            let stmt = IRStmt::constraint(
                CmpOp::Le,
                (len.cell().row_offset, lhs),
                (len.cell().row_offset, rhs),
            );
            injected_ir.entry(len.cell().region_index).or_default().push(stmt);

            Ok(AssignedVector { buffer, len })
        }
    }

    fn emit_filler_constrain<F: PrimeField, const M: usize, const A: usize>(
        len_cell: Cell,
        len_expr: Expression<F>,
        buffer: &[(Cell, Expression<F>)],
        filler: F,
        injected_ir: &mut InjectedIR<F>,
    ) {
        let len_row = len_cell.row_offset;
        let len_idx = len_cell.region_index;

        let mut len_exprs = vec![];
        let mut size_exprs = vec![];
        for len in 0..=M {
            let lims = get_lims::<M, A>(len);
            let mut size_checks = vec![];
            for len in 0..M {
                if lims.contains(&len) {
                    continue;
                }
                let (elt_cell, elt) = &buffer[len];
                assert_eq!(elt_cell.region_index, len_idx);
                let elt_row = elt_cell.row_offset;
                size_checks.push(IRBexpr::Cmp(
                    CmpOp::Eq,
                    (elt_row, elt.clone()),
                    (elt_row, Expression::Constant(filler)),
                ))
            }
            if size_checks.is_empty() {
                continue;
            }
            size_exprs.push(IRBexpr::And(size_checks));

            let lenf = F::from(len as u64);
            len_exprs.push(IRBexpr::Cmp(
                CmpOp::Eq,
                (len_row, len_expr.clone()),
                (len_row, Expression::Constant(lenf)),
            ));
        }
        let expr = IRBexpr::Or(
            std::iter::zip(len_exprs, size_exprs)
                .map(|(len, size)| IRBexpr::Implies(Box::new(len), Box::new(size)))
                .collect(),
        );
        let stmt = IRStmt::assert(expr);
        injected_ir.entry(len_idx).or_default().push(stmt);
    }

    fn try_col<F, C: ColumnType, E>(c: &AssignedNative<F>) -> Result<Column<C>, Error>
    where
        Column<C>: TryFrom<Column<Any>, Error = E>,
        Error: From<E>,
        F: Field,
    {
        Ok(c.cell().column.try_into()?)
    }

    fn assign_to_same_region<F: Field, I: Into<AssignedNative<F>> + Clone>(
        len: &AssignedNative<F>,
        buffer: &[I],
        layouter: &mut impl Layouter<F>,
    ) -> Result<(AssignedNative<F>, Vec<AssignedNative<F>>), Error> {
        Ok(layouter.assign_region(
            || "filler constraint",
            |mut region| {
                let len = len.copy_advice(|| "len", &mut region, try_col(len)?, 0)?;
                let buffer: Vec<AssignedNative<F>> = buffer
                    .iter()
                    .cloned()
                    .map(|c| c.into())
                    .enumerate()
                    .map(|(n, c)| {
                        c.copy_advice(|| format!("buffer[{n}]"), &mut region, try_col(&c)?, n + 1)
                    })
                    .collect::<Result<_, _>>()?;
                Ok((len, buffer))
            },
        )?)
    }

    impl<F: PrimeField, C, const M: usize, const A: usize> StoreIntoCells<F, C>
        for AssignedVector<F, AssignedNative<F>, M, A>
    {
        fn store(
            self,
            ctx: &mut OCtx,
            chip: &C,
            layouter: &mut impl Layouter<F>,
            injected_ir: &mut InjectedIR<F>,
        ) -> Result<(), Error> {
            let (len, buffer) = assign_to_same_region(&self.len, &self.buffer, layouter)?;
            let buffer = buffer
                .into_iter()
                .map(|c| Ok((c.cell(), cell_to_expr(&c)?)))
                .collect::<Result<Vec<_>, Error>>()?;
            emit_filler_constrain::<_, M, A>(
                len.cell(),
                cell_to_expr(&len)?,
                &buffer,
                AssignedNative::FILLER,
                injected_ir,
            );

            self.buffer.store(ctx, chip, layouter, injected_ir)?;
            self.len.store(ctx, chip, layouter, injected_ir)?;

            Ok(())
        }
    }

    impl<F: PrimeField, C, const M: usize, const A: usize> StoreIntoCells<F, C>
        for AssignedVector<F, AssignedByte<F>, M, A>
    {
        fn store(
            self,
            ctx: &mut OCtx,
            chip: &C,
            layouter: &mut impl Layouter<F>,
            injected_ir: &mut InjectedIR<F>,
        ) -> Result<(), Error> {
            let (len, buffer) = assign_to_same_region(&self.len, &self.buffer, layouter)?;
            let buffer = buffer
                .into_iter()
                .map(|c| Ok((c.cell(), cell_to_expr(&c)?)))
                .collect::<Result<Vec<_>, Error>>()?;
            emit_filler_constrain::<F, M, A>(
                len.cell(),
                cell_to_expr(&len)?,
                &buffer,
                F::from(AssignedByte::<F>::FILLER as u64),
                injected_ir,
            );

            self.buffer.store(ctx, chip, layouter, injected_ir)?;
            self.len.store(ctx, chip, layouter, injected_ir)?;

            Ok(())
        }
    }
}

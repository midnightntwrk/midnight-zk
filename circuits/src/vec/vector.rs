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
    pub(crate) buffer: [T; M],

    /// Effective length of the vector.
    pub(crate) len: AssignedNative<F>,
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

    use std::ops::Range;

    use extractor_support::{
        cell_to_expr,
        cells::{
            ctx::{ICtx, LayoutAdaptor, OCtx},
            load::LoadFromCells,
            store::StoreIntoCells,
            CellReprSize,
        },
        ir::{expr::IRBexpr, stmt::IRStmt},
    };
    use ff::{Field, PrimeField};
    use midnight_proofs::{
        circuit::Cell,
        plonk::{Any, Column, ColumnType, Error, Expression},
        ExtractionSupport,
    };

    use super::{AssignedVector, Vectorizable};
    use crate::{
        field::AssignedNative,
        types::AssignedByte,
        utils::extraction::{IRExt as _, IR},
        vec::get_lims,
    };

    impl<F: PrimeField, T: Vectorizable + CellReprSize, const M: usize, const A: usize> CellReprSize
        for AssignedVector<F, T, M, A>
    {
        const SIZE: usize = T::SIZE * M + AssignedNative::<F>::SIZE;
    }

    impl<
            F: PrimeField,
            C,
            L,
            T: Vectorizable + LoadFromCells<F, C, ExtractionSupport, L>,
            const M: usize,
            const A: usize,
        > LoadFromCells<F, C, ExtractionSupport, L> for AssignedVector<F, T, M, A>
    {
        fn load(
            ctx: &mut ICtx<F, ExtractionSupport>,
            chip: &C,
            layouter: &mut impl LayoutAdaptor<F, ExtractionSupport, Adaptee = L>,
            injected_ir: &mut IR<F>,
        ) -> Result<Self, Error> {
            let buffer = ctx.load(chip, layouter, injected_ir)?;
            let len = ctx.load(chip, layouter, injected_ir)?;
            let v = AssignedVector { buffer, len };
            injected_ir.inject_in_cell(
                v.len.cell(),
                IRStmt::le(
                    cell_to_expr!(&v.len, F)?,
                    Expression::from(u64::try_from(M).unwrap()),
                ),
            );

            Ok(v)
        }
    }

    /// Creates IR checking that each cell in the vector that is padding is
    /// equal to the filler.
    ///
    /// I.e. for a vector of size 5 where indices 0, 1, and 4 are padding then
    /// emits the expressions: `(= buffer[0] 0), (= buffer[1] 0), (=
    /// buffer[4] 0)`
    fn emit_size_checks<F: PrimeField>(
        buffer: &[(Cell, Expression<F>)],
        lims: &Range<usize>,
        m: usize,
        filler: F,
    ) -> Vec<IRBexpr<(usize, Expression<F>)>> {
        buffer
            .iter()
            .enumerate()
            .take(m)
            .filter_map(|(len, (elt_cell, elt))| {
                if lims.contains(&len) {
                    return None;
                }
                Some(
                    IRBexpr::eq(elt.clone(), Expression::Constant(filler))
                        .with(elt_cell.row_offset),
                )
            })
            .collect::<Vec<_>>()
    }

    /// Creates IR checking that for a given length of the vector, the padding
    /// cells have the proper values.
    ///
    /// The checks on each padding value are emitted with [`emit_size_checks`].
    /// This function emits the list of checks for each possible length and
    /// creates an assertion with the following structure:
    ///
    /// ```text
    /// (len = 0 -> (pad_0 = 0 /\ pad_1 = 0 /\ ... /\ pad_M = 0)) \/
    /// (len = 1 -> (pad_0 = 0 /\ pad_1 = 0 /\ ... /\ pad_M = 0)) \/
    /// ...                                                       \/
    /// (len = M -> (pad_0 = 0 /\ pad_1 = 0 /\ ... /\ pad_M = 0))
    /// ```
    ///
    /// Where `len` is the cell storing the secret length of the vector and
    /// `pad_n` is the n-th padded cell according to [`emit_size_checks`]
    /// and the limits computed by [`get_lims`].
    fn emit_filler_constrain<F: PrimeField, const M: usize, const A: usize>(
        len_cell: Cell,
        len_expr: Expression<F>,
        buffer: &[(Cell, Expression<F>)],
        filler: F,
        injected_ir: &mut IR<F>,
    ) {
        let expr = IRBexpr::Or(
            (0..=M)
                .filter_map(|len| {
                    let lims = get_lims::<M, A>(len);
                    let size_checks = emit_size_checks(buffer, &lims, M, filler);

                    if size_checks.is_empty() {
                        return None;
                    }
                    Some(IRBexpr::implies(
                        IRBexpr::eq(len_expr.clone(), Expression::from(len as u64))
                            .with(len_cell.row_offset),
                        IRBexpr::And(size_checks),
                    ))
                })
                .collect(),
        );
        injected_ir.inject(len_cell.region_index, IRStmt::assert(expr));
    }

    fn try_col<F, C: ColumnType, E>(
        c: &AssignedNative<F>,
    ) -> Result<Column<C>, extractor_support::error::Error>
    where
        Column<C>: TryFrom<Column<Any>, Error = E>,
        extractor_support::error::Error: From<E>,
        F: Field,
    {
        Ok(c.cell().column.try_into()?)
    }

    /// Puts all the injected IR into the same region since that's a requirement
    /// of the frontend.
    fn assign_to_same_region<F: Field, I: Into<AssignedNative<F>> + Clone>(
        len: &AssignedNative<F>,
        buffer: &[I],
        layouter: &mut impl LayoutAdaptor<F, ExtractionSupport>,
    ) -> Result<(AssignedNative<F>, Vec<AssignedNative<F>>), Error> {
        layouter.region(
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
        )
    }

    impl<F: PrimeField, C, L, const M: usize, const A: usize>
        StoreIntoCells<F, C, ExtractionSupport, L> for AssignedVector<F, AssignedNative<F>, M, A>
    {
        fn store(
            self,
            ctx: &mut OCtx<F, ExtractionSupport>,
            chip: &C,
            layouter: &mut impl LayoutAdaptor<F, ExtractionSupport, Adaptee = L>,
            injected_ir: &mut IR<F>,
        ) -> Result<(), Error> {
            let (len, buffer) = assign_to_same_region(&self.len, &self.buffer, layouter)?;
            let buffer = buffer
                .into_iter()
                .map(|c| Ok((c.cell(), cell_to_expr!(&c, F)?)))
                .collect::<Result<Vec<_>, Error>>()?;
            emit_filler_constrain::<_, M, A>(
                len.cell(),
                cell_to_expr!(&len, F)?,
                &buffer,
                AssignedNative::FILLER,
                injected_ir,
            );

            self.buffer.store(ctx, chip, layouter, injected_ir)?;
            self.len.store(ctx, chip, layouter, injected_ir)?;

            Ok(())
        }
    }

    impl<F: PrimeField, C, L, const M: usize, const A: usize>
        StoreIntoCells<F, C, ExtractionSupport, L> for AssignedVector<F, AssignedByte<F>, M, A>
    {
        fn store(
            self,
            ctx: &mut OCtx<F, ExtractionSupport>,
            chip: &C,
            layouter: &mut impl LayoutAdaptor<F, ExtractionSupport, Adaptee = L>,
            injected_ir: &mut IR<F>,
        ) -> Result<(), Error> {
            let (len, buffer) = assign_to_same_region(&self.len, &self.buffer, layouter)?;
            let buffer = buffer
                .into_iter()
                .map(|c| Ok((c.cell(), cell_to_expr!(&c, F)?)))
                .collect::<Result<Vec<_>, Error>>()?;
            emit_filler_constrain::<F, M, A>(
                len.cell(),
                cell_to_expr!(&len, F)?,
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

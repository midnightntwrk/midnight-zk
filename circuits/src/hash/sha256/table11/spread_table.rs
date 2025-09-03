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

use std::{convert::TryInto, fmt::Debug};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Cell, Region, Value},
    plonk::{Advice, Column, Error},
};

use crate::hash::sha256::{
    util::{lebs2ip, spread_bits},
    AssignedBits,
};

/// An input word into a lookup, containing (dense, spread)
#[derive(Copy, Clone, Debug)]
pub(super) struct SpreadWord<const DENSE: usize, const SPREAD: usize> {
    pub dense: [bool; DENSE],
    pub spread: [bool; SPREAD],
}

impl<const DENSE: usize, const SPREAD: usize> SpreadWord<DENSE, SPREAD> {
    pub(super) fn new(dense: [bool; DENSE]) -> Self {
        assert!(DENSE <= 16);
        SpreadWord {
            dense,
            spread: spread_bits(dense),
        }
    }

    pub(super) fn try_new<T: TryInto<[bool; DENSE]> + std::fmt::Debug>(dense: T) -> Self
    where
        <T as TryInto<[bool; DENSE]>>::Error: std::fmt::Debug,
    {
        assert!(DENSE <= 16);
        let dense: [bool; DENSE] = dense.try_into().unwrap();
        SpreadWord {
            dense,
            spread: spread_bits(dense),
        }
    }
}

/// A variable stored in advice columns corresponding to a row of
/// [SpreadTableConfig](super::decomposition::SpreadTableConfig).
#[derive(Clone, Debug)]
pub(super) struct SpreadVar<const DENSE: usize, const SPREAD: usize, F: PrimeField> {
    pub dense: AssignedBits<DENSE, F>,
    pub spread: AssignedBits<SPREAD, F>,
}

pub(crate) trait PostponedSpreadVar: Debug {
    /// Function that gets the bit length of Self
    fn bit_length(&self) -> usize;

    /// Helper function to implement clone
    fn clone_box(&self) -> Box<dyn PostponedSpreadVar>;

    /// Dense form of a word
    fn dense(&self) -> Value<u64>;

    /// Spread form of a word
    fn spread(&self) -> Value<u64>;

    /// Gives the cell of the assigned dense word
    fn assigned_dense_cell(&self) -> Cell;

    /// Gives the cell of the assigned dense word
    fn assigned_spread_cell(&self) -> Cell;
}

impl<const DENSE: usize, const SPREAD: usize, F: PrimeField> PostponedSpreadVar
    for SpreadVar<DENSE, SPREAD, F>
{
    fn bit_length(&self) -> usize {
        DENSE
    }

    fn dense(&self) -> Value<u64> {
        let value = self.dense.value();
        value.map(|v| lebs2ip(v))
    }

    fn spread(&self) -> Value<u64> {
        let value = self.spread.value();
        value.map(|v| lebs2ip(v))
    }

    fn assigned_dense_cell(&self) -> Cell {
        self.dense.cell()
    }

    fn assigned_spread_cell(&self) -> Cell {
        self.spread.cell()
    }

    fn clone_box(&self) -> Box<dyn PostponedSpreadVar> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn PostponedSpreadVar> {
    fn clone(&self) -> Box<dyn PostponedSpreadVar> {
        self.clone_box()
    }
}

impl<const DENSE: usize, const SPREAD: usize, F: PrimeField> SpreadVar<DENSE, SPREAD, F> {
    pub(super) fn with_lookup(
        region: &mut Region<'_, F>,
        cols: &SpreadInputs,
        row: usize,
        word: Value<SpreadWord<DENSE, SPREAD>>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<Self, Error> {
        let dense_val = word.map(|word| word.dense);
        let spread_val = word.map(|word| word.spread);

        let dense =
            AssignedBits::<DENSE, F>::assign_bits(region, || "dense", cols.dense, row, dense_val)?;

        let spread = AssignedBits::<SPREAD, F>::assign_bits(
            region,
            || "spread",
            cols.spread,
            row,
            spread_val,
        )?;

        let spread_var = SpreadVar { dense, spread };

        // we postpone the check of the validity of dense/spread
        postponed.push(Box::new(spread_var.clone()));

        Ok(spread_var)
    }

    pub(super) fn without_lookup_fixed(
        region: &mut Region<'_, F>,
        dense_col: Column<Advice>,
        dense_row: usize,
        spread_col: Column<Advice>,
        spread_row: usize,
        word: SpreadWord<DENSE, SPREAD>,
    ) -> Result<Self, Error> {
        let dense_val = word.dense;
        let spread_val = word.spread;

        let dense = AssignedBits::<DENSE, F>::assign_bits_fixed(
            region,
            || "dense",
            dense_col,
            dense_row,
            dense_val,
        )?;

        let spread = AssignedBits::<SPREAD, F>::assign_bits_fixed(
            region,
            || "spread",
            spread_col,
            spread_row,
            spread_val,
        )?;

        Ok(SpreadVar { dense, spread })
    }

    pub(super) fn without_lookup(
        region: &mut Region<'_, F>,
        dense_col: Column<Advice>,
        dense_row: usize,
        spread_col: Column<Advice>,
        spread_row: usize,
        word: Value<SpreadWord<DENSE, SPREAD>>,
    ) -> Result<Self, Error> {
        let dense_val = word.map(|word| word.dense);
        let spread_val = word.map(|word| word.spread);

        let dense = AssignedBits::<DENSE, F>::assign_bits(
            region,
            || "dense",
            dense_col,
            dense_row,
            dense_val,
        )?;

        let spread = AssignedBits::<SPREAD, F>::assign_bits(
            region,
            || "spread",
            spread_col,
            spread_row,
            spread_val,
        )?;

        Ok(SpreadVar { dense, spread })
    }
}

#[derive(Clone, Debug)]
pub(super) struct SpreadInputs {
    pub(super) dense: Column<Advice>,
    pub(super) spread: Column<Advice>,
}

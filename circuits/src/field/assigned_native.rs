// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

//! Native field elements assigned in the circuit.
//!
//! An [AssignedNative] may be created without a cell ([AssignedNative::free]):
//! it is then assigned to the first cell it is copied to (or to the cell of an
//! assigned element it is constrained to be equal to), and stays there. An
//! element that is never used in any constraint is never assigned to a cell;
//! as it is unconstrained, it does not need to be in the circuit.

use std::{
    cell::OnceCell,
    hash::{Hash, Hasher},
    rc::Rc,
};

use ff::Field;
use midnight_proofs::{
    circuit::{AssignedCell, Cell, Region, Value},
    plonk::{Advice, Column, Error},
};

/// A native field element assigned in the circuit.
///
/// Its cell is set at most once, and shared by all its clones.
#[derive(Clone, Debug)]
pub struct AssignedNative<F: Field> {
    value: Value<F>,
    cell: Rc<OnceCell<AssignedCell<F, F>>>,
}

impl<F: Field> From<AssignedCell<F, F>> for AssignedNative<F> {
    fn from(assigned: AssignedCell<F, F>) -> Self {
        AssignedNative {
            value: assigned.value().copied(),
            cell: Rc::new(OnceCell::from(assigned)),
        }
    }
}

/// # Panics
///
/// If the element is not assigned to a cell.
impl<F: Field> From<&AssignedNative<F>> for AssignedCell<F, F> {
    fn from(assigned: &AssignedNative<F>) -> Self {
        let mut cell = assigned.cell.get().expect("AssignedNative is not assigned").clone();
        // The cell may have been assigned when the layouter only measured its
        // region, without its value.
        assigned
            .value
            .map(|v| cell.update_value(v).expect("AssignedNative value mismatch"));
        cell
    }
}

/// Two elements are equal iff one is a clone of the other.
impl<F: Field> PartialEq for AssignedNative<F> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.cell, &other.cell)
    }
}

impl<F: Field> Eq for AssignedNative<F> {}

/// Hashes the identity of the shared cell, which does not change when the
/// element is assigned to a cell, so elements can be keys of hash maps.
impl<F: Field> Hash for AssignedNative<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.cell).hash(state)
    }
}

impl<F: Field> AssignedNative<F> {
    /// An element with the given value that is not assigned to a cell yet.
    pub(crate) fn free(value: Value<F>) -> Self {
        AssignedNative {
            value,
            cell: Rc::new(OnceCell::new()),
        }
    }

    /// The value of the element.
    pub fn value(&self) -> Value<&F> {
        self.value.as_ref()
    }

    /// Whether the element is assigned to a cell.
    pub fn is_assigned(&self) -> bool {
        self.cell.get().is_some()
    }

    /// The cell where the element is assigned.
    ///
    /// # Panics
    ///
    /// If the element is not assigned to a cell (see [Self::is_assigned]).
    pub fn cell(&self) -> Cell {
        self.cell.get().expect("AssignedNative is not assigned").cell()
    }

    /// Copies the element to the given advice cell, constraining them to be
    /// equal, and returns the copy. If the element is not assigned to a cell,
    /// it is assigned to this one instead (and returned).
    ///
    /// Returns an error if either cell is in a column where equality has not
    /// been enabled.
    pub fn copy_advice<A, AR>(
        &self,
        annotation: A,
        region: &mut Region<'_, F>,
        column: Column<Advice>,
        offset: usize,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        let copy = region.assign_advice(annotation, column, offset, || self.value)?;
        match self.cell.get() {
            // The layouter may run a region twice: copying the element to its own cell
            // is just assigning it.
            Some(cell) if cell.cell() == copy.cell() => Ok(self.clone()),
            Some(cell) => {
                region.constrain_equal(copy.cell(), cell.cell())?;
                Ok(copy.into())
            }
            None => {
                let _ = self.cell.set(copy);
                Ok(self.clone())
            }
        }
    }

    /// Constrains the element to be equal to `other`. If one of them is not
    /// assigned to a cell, it is assigned to the cell of the other one, without
    /// any constraint.
    ///
    /// Returns an error if neither element is assigned to a cell, or if one
    /// is not and the values are known and differ.
    pub fn constrain_equal(&self, region: &mut Region<'_, F>, other: &Self) -> Result<(), Error> {
        match (self.cell.get(), other.cell.get()) {
            // The layouter may run a region twice: the second time, an element
            // assigned to the cell of the other one by the first run is found here.
            (Some(x), Some(y)) if x.cell() == y.cell() => Ok(()),
            (Some(x), Some(y)) => region.constrain_equal(x.cell(), y.cell()),
            (None, None) => Err(Error::Synthesis(
                "cannot constrain two unused AssignedNative to be equal".into(),
            )),
            (x, y) => {
                (self.value.zip(other.value)).error_if_known_and(|(x, y)| x != y)?;
                let (free, cell) = if x.is_none() { (self, y) } else { (other, x) };
                let _ = free.cell.set(cell.unwrap().clone());
                Ok(())
            }
        }
    }
}

/// Assignment of advice cells as [AssignedNative] elements.
pub(crate) trait AssignNative<F: Field> {
    /// Assigns an advice cell like [Region::assign_advice], returning it as an
    /// [AssignedNative].
    fn assign_native<'v, A, AR, V>(
        &'v mut self,
        annotation: A,
        column: Column<Advice>,
        offset: usize,
        to: V,
    ) -> Result<AssignedNative<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
        V: FnMut() -> Value<F> + 'v;
}

impl<F: Field> AssignNative<F> for Region<'_, F> {
    fn assign_native<'v, A, AR, V>(
        &'v mut self,
        annotation: A,
        column: Column<Advice>,
        offset: usize,
        to: V,
    ) -> Result<AssignedNative<F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
        V: FnMut() -> Value<F> + 'v,
    {
        self.assign_advice(annotation, column, offset, to).map(AssignedNative::from)
    }
}

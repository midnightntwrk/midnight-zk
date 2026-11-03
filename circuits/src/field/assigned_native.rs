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

impl<F: Field> From<&AssignedNative<F>> for AssignedCell<F, F> {
    fn from(assigned: &AssignedNative<F>) -> Self {
        assigned
            .cell
            .get()
            .expect("AssignedNative is always assigned to a cell")
            .clone()
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
    /// The value of the element.
    pub fn value(&self) -> Value<&F> {
        self.value.as_ref()
    }

    /// The cell where the element is assigned.
    pub fn cell(&self) -> Cell {
        self.cell.get().expect("AssignedNative is always assigned to a cell").cell()
    }

    /// Copies the element to the given advice cell, constraining them to be
    /// equal, and returns the copy.
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
        region.constrain_equal(copy.cell(), self.cell())?;
        Ok(copy.into())
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

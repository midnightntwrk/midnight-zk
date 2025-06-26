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

//! A module for in-circuit partial MSMs and its off-circuit analog.
//! These MSM have a fixed-base part which is represented by the corresponding
//! scalars only.
//! (The bases are assumed to be fixed and globally known.)

use std::collections::{btree_map::Entry, BTreeMap};

use ff::Field;
use halo2curves::msm::msm_best;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    instructions::{AssignmentInstructions, EccInstructions, PublicInputInstructions},
    types::{InnerValue, Instantiable},
    verifier::{
        types::{AssignedPoint, AssignedScalar, CurveChip, ScalarChip, SelfEmulationCurve},
        utils::{
            add_bounded_scalars, assign_bounded_scalars, mul_bounded_scalars, AssignedBoundedScalar,
        },
    },
};

/// Type for off-circuit multi-scalar multiplications.
///
/// This structure represents the following computation:
/// `<scalars, bases> + <fixed_bases, fixed_base_scalars>`
///
/// Note that the `fixed_bases` are not part of this structure, they are
/// supposed to be globally known and will be provided when evaluating the MSM.
///
/// (`scalars` and `bases` are guaranteed to have the same length.)
#[derive(Clone, Debug)]
pub struct Msm<C: SelfEmulationCurve> {
    bases: Vec<C>,
    scalars: Vec<C::ScalarExt>,
    fixed_base_scalars: BTreeMap<String, C::ScalarExt>,
}

/// Type for in-circuit multi-scalar multiplications.
///
/// This is the in-circuit analog of `Msm<C>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignedMsm<C: SelfEmulationCurve> {
    bases: Vec<AssignedPoint<C>>,
    scalars: Vec<AssignedBoundedScalar<C>>,
    fixed_base_scalars: BTreeMap<String, AssignedBoundedScalar<C>>,
}

impl<C: SelfEmulationCurve> Msm<C> {
    /// Creates a new MSM from the given slice of bases, scalars and a BTreeMap
    /// of fixed_base_scalars.
    ///
    /// # Panics
    ///
    /// If `bases` and `scalars` do not have the same length.
    pub fn new(
        bases: &[C],
        scalars: &[C::ScalarExt],
        fixed_base_scalars: &BTreeMap<String, C::ScalarExt>,
    ) -> Self {
        assert_eq!(bases.len(), scalars.len());
        Msm {
            bases: bases.to_vec(),
            scalars: scalars.to_vec(),
            fixed_base_scalars: fixed_base_scalars.clone(),
        }
    }

    /// Creates a new MSM from the given base-scalar pairs, with an empty tree
    /// of fixed_base_scalars.
    ///
    /// # Panics
    ///
    /// If `bases` and `scalars` do not have the same length.
    pub fn from_terms(bases: &[C], scalars: &[C::ScalarExt]) -> Self {
        assert_eq!(bases.len(), scalars.len());
        Msm {
            bases: bases.to_vec(),
            scalars: scalars.to_vec(),
            fixed_base_scalars: BTreeMap::new(),
        }
    }

    /// Evaluates the variable part of the AssignedMsm (the scalar-base pairs)
    /// collapsing it to a single point (and a scalar of 1), leaving the
    /// fixed-base part intact.
    ///
    /// This function mutates self.
    pub fn collapse(&mut self) {
        let affine_bases: Vec<C::G1Affine> = self.bases.iter().map(|&b| b.into()).collect();
        let collapsed_base = msm_best(&self.scalars, &affine_bases);

        self.bases = vec![collapsed_base];
        self.scalars = vec![C::ScalarExt::ONE];
    }

    /// Evaluates the MSM with the provided fixed_bases.
    /// I.e. it computes `<scalars, bases> + <fixed_bases, fixed_base_scalars>`.
    ///
    /// # Panics
    /// If one of the keys in the `fixed_base_scalars` of the MSM does not
    /// appear in the tree of `fixed_bases`.
    ///
    /// Note that the converse is not a problem, i.e., the keys of
    /// `fixed_bases` can be a superset of the keys of `fixed_base_scalars`.
    pub fn eval(&self, fixed_bases: &BTreeMap<String, C>) -> C {
        let mut bases = self.bases.clone();
        let mut scalars = self.scalars.clone();

        for (key, scalar) in self.fixed_base_scalars.iter() {
            let base = fixed_bases.get(key).expect("Base not provided: {key}");
            bases.push(*base);
            scalars.push(*scalar);
        }

        let affine_bases: Vec<C::G1Affine> = bases.iter().map(|&b| b.into()).collect();
        msm_best(&scalars, &affine_bases)
    }

    /// Accumulates two MSMs with the given scalar r.
    /// The resulting MSM evaluates (on any `fixed_bases`) to
    /// `self.eval(fixed_bases) + r * other.eval(fixed_bases)`.
    pub fn accumulate_with_r(&self, other: &Self, r: C::ScalarExt) -> Self {
        let mut acc = self.clone();

        acc.bases.extend(other.bases.clone());
        acc.scalars.extend(other.scalars.iter().map(|s| *s * r));

        for (key, value) in other.fixed_base_scalars.clone() {
            let r_times_value = r * value;
            acc.fixed_base_scalars
                .entry(key)
                .and_modify(|e| *e += r_times_value)
                .or_insert(r_times_value);
        }

        acc
    }

    /// Given a set of fixed bases (a map indexed by the base name),
    /// removes the given fixed bases from `self.bases` and their corresponding
    /// scalar is moved to `self.fixed_bases_scalars` with the base name as
    /// key.
    ///
    /// The resulting MSM is equivalent to the original one.
    /// Note that this function mutates self.
    ///
    /// # Warning
    ///
    /// If some of the fixed bases are repeated (different name but same point),
    /// they are removed from `self.bases` in the order dictated by the map
    /// `fixed_bases`.
    ///
    /// # Panics
    ///
    /// If some of the base names exist as a key in `self.fixed_base_scalars`.
    ///
    /// If some of the provided fixed bases does not appear in `self.bases`
    /// with the exact required multiplicity.
    pub fn extract_fixed_bases(&mut self, fixed_bases: &BTreeMap<String, C>) {
        assert!(
            (fixed_bases.keys()).all(|name| !self.fixed_base_scalars.contains_key(name)),
            "fixed_bases should not contain keys (names) that appear in self.fixed_base_scalars"
        );

        let n = self.bases.len();

        for (name, fixed_base) in fixed_bases.iter() {
            let mut found = false;
            for i in 0..n {
                if i >= self.bases.len() {
                    break;
                }
                if &self.bases[i] == fixed_base {
                    found = true;
                    self.fixed_base_scalars
                        .insert(name.clone(), self.scalars[i]);
                    self.bases.remove(i);
                    self.scalars.remove(i);
                    break;
                }
            }
            if !found {
                panic!("{fixed_base:?} not found in self.bases (with the required multiplicity)");
            }
        }

        // Do another search to make sure that the fixed bases do not appear
        // anymore, thus they had the exact required multiplicity.
        for fixed_base in fixed_bases.values() {
            if self.bases.iter().any(|base| base == fixed_base) {
                panic!("{fixed_base:?} appears in self.bases more times than expected");
            }
        }
    }
}

impl<C: SelfEmulationCurve> InnerValue for AssignedMsm<C> {
    type Element = Msm<C>;

    fn value(&self) -> Value<Self::Element> {
        let bases: Value<Vec<C>> = Value::from_iter(self.bases.iter().map(|base| base.value()));

        let scalars: Value<Vec<C::ScalarExt>> =
            Value::from_iter(self.scalars.iter().map(|s| s.scalar.value().copied()));

        let fixed_based_scalars: Value<BTreeMap<String, C::ScalarExt>> = Value::from_iter(
            self.fixed_base_scalars
                .iter()
                .map(|(name, s)| s.scalar.value().map(|s| (name.clone(), *s))),
        );

        scalars
            .zip(bases)
            .zip(fixed_based_scalars)
            .map(|((scalars, bases), fixed_base_scalars)| Msm {
                bases,
                scalars,
                fixed_base_scalars,
            })
    }
}

impl<C: SelfEmulationCurve> Instantiable<C::ScalarExt> for AssignedMsm<C> {
    fn as_public_input(msm: &Msm<C>) -> Vec<C::ScalarExt> {
        [
            msm.bases
                .iter()
                .flat_map(AssignedPoint::<C>::as_public_input)
                .collect::<Vec<_>>(),
            msm.scalars.clone(),
            msm.fixed_base_scalars.values().copied().collect::<Vec<_>>(),
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>()
    }
}

impl<C: SelfEmulationCurve> AssignedMsm<C> {
    pub(crate) fn in_circuit_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        curve_chip: &CurveChip<C>,
    ) -> Result<Vec<AssignedScalar<C>>, Error> {
        Ok([
            self.bases
                .iter()
                .map(|base| curve_chip.as_public_input(layouter, base))
                .collect::<Result<Vec<_>, Error>>()?
                .into_iter()
                .flatten()
                .collect::<Vec<_>>(),
            self.scalars
                .iter()
                .map(|s| s.clone().scalar)
                .collect::<Vec<_>>(),
            self.fixed_base_scalars
                .values()
                .map(|s| s.clone().scalar)
                .collect::<Vec<_>>(),
        ]
        .into_iter()
        .flatten()
        .collect())
    }

    pub(crate) fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        curve_chip: &CurveChip<C>,
        scalar_chip: &ScalarChip<C>,
    ) -> Result<(), Error> {
        self.bases
            .iter()
            .try_for_each(|base| curve_chip.constrain_as_public_input(layouter, base))?;

        self.scalars
            .iter()
            .try_for_each(|s| scalar_chip.constrain_as_public_input(layouter, &s.clone().scalar))?;

        self.fixed_base_scalars
            .values()
            .try_for_each(|s| scalar_chip.constrain_as_public_input(layouter, &s.clone().scalar))
    }
}

impl<C: SelfEmulationCurve> AssignedMsm<C> {
    /// Witnesses an MSM computation of `len` bases/scalars and a `BTreeMap` of
    /// fixed_base_scalars indexed by the given `fixed_base_names`.
    pub fn assign(
        layouter: &mut impl Layouter<C::ScalarExt>,
        curve_chip: &CurveChip<C>,
        scalar_chip: &ScalarChip<C>,
        len: usize,
        fixed_base_names: &[String],
        msm_value: Value<Msm<C>>,
    ) -> Result<Self, Error> {
        let bases_val = msm_value
            .as_ref()
            .map(|msm| msm.bases.clone())
            .transpose_vec(len);

        let scalars_val = msm_value
            .as_ref()
            .map(|msm| msm.scalars.clone())
            .transpose_vec(len);

        let fixed_base_scalars_val = msm_value
            .as_ref()
            .map(|msm| {
                // We only use the keys inside the Value to iterate over it in the right order,
                // these are then discarded.
                msm.fixed_base_scalars
                    .iter()
                    .map(|s| *s.1)
                    .collect::<Vec<_>>()
            })
            .transpose_vec(fixed_base_names.len());

        // Sort the fixed_base_names to ensure consistency with the BTreeMap.
        let mut fixed_base_names = fixed_base_names.to_vec();
        fixed_base_names.sort();

        let bases = curve_chip.assign_many(layouter, &bases_val)?;
        let scalars = assign_bounded_scalars(layouter, scalar_chip, &scalars_val)?;
        let fixed_base_scalars: BTreeMap<String, AssignedBoundedScalar<C>> = {
            let scalars = assign_bounded_scalars(layouter, scalar_chip, &fixed_base_scalars_val)?;
            fixed_base_names.iter().cloned().zip(scalars).collect()
        };

        Ok(AssignedMsm {
            scalars,
            bases,
            fixed_base_scalars,
        })
    }

    /// An empty AssignedMsm with no fixed base scalars, that evaluates to the
    /// identity point.
    pub fn empty() -> Self {
        Self {
            scalars: vec![],
            bases: vec![],
            fixed_base_scalars: BTreeMap::new(),
        }
    }

    /// Creates a new MSM from the given base (with a scalar of 1).
    pub fn from_term(scalar: &AssignedBoundedScalar<C>, base: &AssignedPoint<C>) -> Self {
        Self {
            scalars: vec![scalar.clone()],
            bases: vec![base.clone()],
            fixed_base_scalars: BTreeMap::new(),
        }
    }

    /// Creates a new MSM from the given fixed base name (with a scalar of 1).
    pub fn from_fixed_term(scalar: &AssignedBoundedScalar<C>, base_name: &str) -> Self {
        Self {
            scalars: vec![],
            bases: vec![],
            fixed_base_scalars: [(base_name.to_string(), scalar.clone())]
                .into_iter()
                .collect(),
        }
    }

    /// Adds a `(scalar, base)` term to the AssignedMsm.
    pub fn add_term(&mut self, scalar: &AssignedBoundedScalar<C>, base: &AssignedPoint<C>) {
        self.scalars.push(scalar.clone());
        self.bases.push(base.clone());
    }

    /// Adds two AssignedMsm.
    pub fn add_msm(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        scalar_chip: &ScalarChip<C>,
        other: &Self,
    ) -> Result<(), Error> {
        self.scalars.extend(other.scalars.clone());
        self.bases.extend(other.bases.clone());

        for (key, value) in other.fixed_base_scalars.clone() {
            match self.fixed_base_scalars.entry(key) {
                Entry::Occupied(mut occ) => {
                    *occ.get_mut() = add_bounded_scalars(layouter, scalar_chip, occ.get(), &value)?;
                }
                Entry::Vacant(vac) => {
                    vac.insert(value);
                }
            }
        }

        Ok(())
    }

    /// Evaluates the variable part of the AssignedMsm (the scalar-base pairs)
    /// collapsing it to a single point (and a scalar of 1), leaving the
    /// fixed-base part intact.
    ///
    /// This function mutates self.
    pub fn collapse(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        curve_chip: &CurveChip<C>,
        scalar_chip: &ScalarChip<C>,
    ) -> Result<(), Error> {
        let scalars = (self.scalars.iter())
            .map(|s| (s.scalar.clone(), s.bound.bits() as usize))
            .collect::<Vec<_>>();

        let collapsed_base = curve_chip.msm_by_bounded_scalars(layouter, &scalars, &self.bases)?;

        self.bases = vec![collapsed_base];
        self.scalars = vec![AssignedBoundedScalar::one(layouter, scalar_chip)?];

        Ok(())
    }

    /// Scales all the scalars of the AssignedMsm by the given factor r.
    ///
    /// This function mutates self.
    pub fn scale(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        scalar_chip: &ScalarChip<C>,
        r: &AssignedBoundedScalar<C>,
    ) -> Result<(), Error> {
        self.scalars = (self.scalars.iter())
            .map(|s| mul_bounded_scalars(layouter, scalar_chip, s, r))
            .collect::<Result<Vec<_>, Error>>()?;

        for s in self.fixed_base_scalars.values_mut() {
            *s = mul_bounded_scalars(layouter, scalar_chip, s, r)?;
        }

        Ok(())
    }

    /// Accumulates two AssignedMSMs with the a given scalar r.
    /// The resulting AssignedMSMs evaluates (on `fixed_bases`) to
    /// `self.eval(fixed_bases) + r * other.eval(fixed_bases)`.
    pub fn accumulate_with_r(
        &self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        scalar_chip: &ScalarChip<C>,
        other: &Self,
        r: &AssignedBoundedScalar<C>,
    ) -> Result<Self, Error> {
        let mut other = other.clone();
        other.scale(layouter, scalar_chip, r)?;

        let mut acc = self.clone();
        acc.add_msm(layouter, scalar_chip, &other)?;

        Ok(acc)
    }
}

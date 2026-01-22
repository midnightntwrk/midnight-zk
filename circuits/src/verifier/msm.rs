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

use std::collections::BTreeMap;

use ff::Field;
use midnight_curves::msm::msm_best;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    field::AssignedNative,
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{InnerValue, Instantiable},
    verifier::{
        types::SelfEmulation,
        utils::{assign_bounded_scalars, mul_bounded_scalars, AssignedBoundedScalar},
    },
};

/// Represents a base point in an MSM, either variable or fixed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Base<S: SelfEmulation> {
    /// A variable base point.
    Variable(S::C),
    /// A fixed base point identified by name.
    Fixed(String),
}

/// Represents an assigned base point in an MSM, either variable or fixed.
#[derive(Clone, Debug)]
pub enum AssignedBase<S: SelfEmulation> {
    /// An assigned variable base point.
    Variable(S::AssignedPoint),
    /// A fixed base point identified by name.
    Fixed(String),
}

impl<S: SelfEmulation> PartialEq for AssignedBase<S> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AssignedBase::Variable(p), AssignedBase::Variable(q)) => p == q,
            (AssignedBase::Fixed(n), AssignedBase::Fixed(m)) => n == m,
            _ => false,
        }
    }
}

impl<S: SelfEmulation> Eq for AssignedBase<S> {}

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
pub struct Msm<S: SelfEmulation> {
    bases: Vec<Base<S>>,
    scalars: Vec<S::F>,
}

/// Type for in-circuit multi-scalar multiplications.
///
/// This is the in-circuit analog of `Msm<C>`.
#[derive(Clone, Debug)]
pub struct AssignedMsm<S: SelfEmulation> {
    bases: Vec<AssignedBase<S>>,
    scalars: Vec<AssignedBoundedScalar<S::F>>,
}

impl<S: SelfEmulation> PartialEq for AssignedMsm<S> {
    fn eq(&self, other: &Self) -> bool {
        self.bases == other.bases && self.scalars == other.scalars
    }
}

impl<S: SelfEmulation> Eq for AssignedMsm<S> {}

impl<S: SelfEmulation> Msm<S> {
    /// Creates a new MSM from the given slice of bases and scalars.
    ///
    /// # Panics
    ///
    /// If `|bases| != |scalars|`.
    pub fn new(bases: &[Base<S>], scalars: &[S::F]) -> Self {
        assert_eq!(bases.len(), scalars.len());
        Msm {
            bases: bases.to_vec(),
            scalars: scalars.to_vec(),
        }
    }

    /// The bases of this MSM.
    pub fn bases(&self) -> Vec<Base<S>> {
        self.bases.clone()
    }

    /// The (non-fixed-base) scalars of this MSM.
    pub fn scalars(&self) -> Vec<S::F> {
        self.scalars.clone()
    }

    /// Creates a new MSM from the given base-scalar pairs.
    /// All bases are treated as variable bases.
    ///
    /// # Panics
    ///
    /// If `|bases| != |scalars|`.
    pub fn from_terms(bases: &[S::C], scalars: &[S::F]) -> Self {
        assert_eq!(bases.len(), scalars.len());
        Msm {
            bases: bases.iter().map(|&b| Base::Variable(b)).collect(),
            scalars: scalars.to_vec(),
        }
    }

    /// Evaluates the variable part of the AssignedMsm (the scalar-base pairs)
    /// collapsing it to a single point (and a scalar of 1), leaving the
    /// fixed-base part intact.
    ///
    /// This function mutates self.
    pub fn collapse(&mut self) {
        let mut variable_bases = vec![];
        let mut variable_scalars = vec![];
        let mut fixed_bases = vec![];
        let mut fixed_scalars = vec![];

        for (base, scalar) in self.bases.iter().zip(self.scalars.iter()) {
            if let Base::Variable(b) = base {
                variable_bases.push(*b);
                variable_scalars.push(*scalar);
            } else {
                fixed_bases.push(base.clone());
                fixed_scalars.push(*scalar);
            }
        }
        let affine_bases: Vec<S::G1Affine> = variable_bases.iter().map(|&b| b.into()).collect();
        let collapsed_base = msm_best(&variable_scalars, &affine_bases);

        self.bases = fixed_bases;
        self.bases.push(Base::Variable(collapsed_base.into()));

        self.scalars = fixed_scalars;
        self.scalars.push(S::F::ONE);
    }

    /// Evaluates the MSM with the provided fixed_bases.
    /// I.e. it computes `<scalars, bases>` where fixed bases are looked up.
    ///
    /// # Panics
    ///
    /// If some fixed base name in the MSM does not appear in `fixed_bases`.
    ///
    /// Note that the converse is not a problem, i.e., the keys of `fixed_bases`
    /// can be a superset of the fixed base names in the MSM.
    pub fn eval(&self, fixed_bases: &BTreeMap<String, S::C>) -> S::C {
        let concrete_bases: Vec<S::C> = self
            .bases
            .iter()
            .map(|base| match base {
                Base::Variable(b) => *b,
                Base::Fixed(name) => *fixed_bases.get(name).expect("Base not provided"),
            })
            .collect();

        let affine_bases: Vec<S::G1Affine> = concrete_bases.iter().map(|&b| b.into()).collect();
        msm_best(&self.scalars, &affine_bases)
    }

    /// Accumulates two MSMs with the given scalar r.
    /// The resulting MSM evaluates (on any `fixed_bases`) to
    /// `self.eval(fixed_bases) + r * other.eval(fixed_bases)`.
    pub fn accumulate_with_r(&self, other: &Self, r: S::F) -> Self {
        let mut acc = self.clone();

        acc.bases.extend(other.bases.clone());
        acc.scalars.extend(other.scalars.iter().map(|s| *s * r));

        acc
    }

    /// TODO: This function will change significantly with the new Base enum
    /// approach. The function should convert Base::Variable entries to
    /// Base::Fixed entries rather than moving scalars between fields.
    pub fn extract_fixed_bases(&mut self, _fixed_bases: &BTreeMap<String, S::C>) {
        todo!()
    }
}

impl<S: SelfEmulation> InnerValue for AssignedMsm<S> {
    type Element = Msm<S>;

    fn value(&self) -> Value<Self::Element> {
        let bases: Value<Vec<Base<S>>> =
            Value::from_iter(self.bases.iter().map(|base| match base {
                AssignedBase::Variable(p) => p.value().map(Base::Variable),
                AssignedBase::Fixed(name) => Value::known(Base::Fixed(name.clone())),
            }));

        let scalars: Value<Vec<S::F>> =
            Value::from_iter(self.scalars.iter().map(|s| s.scalar.value().copied()));

        scalars.zip(bases).map(|(scalars, bases)| Msm { bases, scalars })
    }
}

impl<S: SelfEmulation> Instantiable<S::F> for AssignedMsm<S> {
    fn as_public_input(msm: &Msm<S>) -> Vec<S::F> {
        let variable_bases: Vec<S::F> = msm
            .bases
            .iter()
            .filter_map(|base| match base {
                Base::Variable(b) => Some(S::AssignedPoint::as_public_input(b)),
                Base::Fixed(_) => None,
            })
            .flatten()
            .collect();

        [variable_bases, msm.scalars.clone()].into_iter().flatten().collect()
    }
}

impl<S: SelfEmulation> AssignedMsm<S> {
    /// Converts the off-circuit MSM into two vectors of scalars. The first
    /// will be used as a normal instance, whereas the second will be plugged-in
    /// in as a committed instance.
    ///
    /// The committed instance part corresponds to all scalars of the MSM.
    pub fn as_public_input_with_committed_scalars(msm: &Msm<S>) -> (Vec<S::F>, Vec<S::F>) {
        let normal_instance: Vec<S::F> = msm
            .bases
            .iter()
            .filter_map(|base| match base {
                Base::Variable(b) => Some(S::AssignedPoint::as_public_input(b)),
                Base::Fixed(_) => None,
            })
            .flatten()
            .collect();

        let committed_instance = msm.scalars.clone();

        (normal_instance, committed_instance)
    }
}

impl<S: SelfEmulation> AssignedMsm<S> {
    pub(crate) fn in_circuit_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        let variable_bases: Vec<_> = self
            .bases
            .iter()
            .filter_map(|base| match base {
                AssignedBase::Variable(p) => Some(p),
                AssignedBase::Fixed(_) => None,
            })
            .map(|base| curve_chip.as_public_input(layouter, base))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect();

        let scalars: Vec<_> = self.scalars.iter().map(|s| s.clone().scalar).collect();

        Ok([variable_bases, scalars].concat())
    }

    pub(crate) fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
    ) -> Result<(), Error> {
        self.bases.iter().try_for_each(|base| match base {
            AssignedBase::Variable(p) => curve_chip.constrain_as_public_input(layouter, p),
            AssignedBase::Fixed(_) => Ok(()),
        })?;

        self.scalars
            .iter()
            .try_for_each(|s| scalar_chip.constrain_as_public_input(layouter, &s.clone().scalar))
    }

    pub(crate) fn constrain_as_public_input_with_committed_scalars(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
    ) -> Result<(), Error> {
        self.bases.iter().try_for_each(|base| match base {
            AssignedBase::Variable(p) => curve_chip.constrain_as_public_input(layouter, p),
            AssignedBase::Fixed(_) => Ok(()),
        })?;

        self.scalars.iter().try_for_each(|s| {
            let mut a = S::F::ZERO;
            s.scalar.clone().value().map(|v| a = *v);
            S::constrain_scalar_as_committed_public_input(layouter, scalar_chip, &s.scalar)
        })
    }
}

impl<S: SelfEmulation> AssignedMsm<S> {
    /// Witnesses an MSM computation.
    ///
    /// `base_names`: For each base, `None` means it's a variable base (will be
    /// assigned), `Some(name)` means it's a fixed base with the given name.
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        base_names: &[Option<String>],
        msm_value: Value<Msm<S>>,
    ) -> Result<Self, Error> {
        let len = base_names.len();
        let bases_val = msm_value.as_ref().map(|msm| msm.bases.clone()).transpose_vec(len);
        let scalars_val = msm_value.as_ref().map(|msm| msm.scalars.clone()).transpose_vec(len);

        let bases = base_names
            .iter()
            .zip(bases_val.iter())
            .map(|(base_name, base_val)| match base_name {
                None => {
                    let p_val = base_val.clone().map_with_result(|p| match p {
                        Base::Variable(p) => Ok(p),
                        Base::Fixed(_) => Err(Error::Synthesis(
                            "Expected variable base but found fixed base".into(),
                        )),
                    })?;
                    let assigned_point = curve_chip.assign(layouter, p_val)?;
                    Ok(AssignedBase::Variable(assigned_point))
                }
                Some(name) => Ok(AssignedBase::Fixed(name.clone())),
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let scalars = assign_bounded_scalars(layouter, scalar_chip, &scalars_val)?;

        Ok(AssignedMsm { scalars, bases })
    }

    /// An empty AssignedMsm that evaluates to the identity point.
    pub fn empty() -> Self {
        Self {
            scalars: vec![],
            bases: vec![],
        }
    }

    /// Creates a new MSM from the given variable base and scalar.
    pub fn from_term(scalar: &AssignedBoundedScalar<S::F>, base: &S::AssignedPoint) -> Self {
        Self {
            scalars: vec![scalar.clone()],
            bases: vec![AssignedBase::Variable(base.clone())],
        }
    }

    /// Creates a new MSM from the given fixed base name and scalar.
    pub fn from_fixed_term(scalar: &AssignedBoundedScalar<S::F>, base_name: &str) -> Self {
        Self {
            scalars: vec![scalar.clone()],
            bases: vec![AssignedBase::Fixed(base_name.to_string())],
        }
    }

    /// Adds a `(scalar, base)` term to the AssignedMsm.
    pub fn add_term(&mut self, scalar: &AssignedBoundedScalar<S::F>, base: &S::AssignedPoint) {
        self.scalars.push(scalar.clone());
        self.bases.push(AssignedBase::Variable(base.clone()));
    }

    /// Adds two AssignedMsm.
    pub fn add_msm(&mut self, other: &Self) {
        self.scalars.extend(other.scalars.clone());
        self.bases.extend(other.bases.clone());
    }

    /// Evaluates the variable part of the AssignedMsm (the scalar-base pairs)
    /// collapsing it to a single point (and a scalar of 1), leaving the
    /// fixed-base part intact.
    ///
    /// This function mutates self.
    pub fn collapse(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
    ) -> Result<(), Error> {
        let mut variable_bases = vec![];
        let mut variable_scalars = vec![];
        let mut fixed_bases = vec![];
        let mut fixed_scalars = vec![];

        for (base, scalar) in self.bases.iter().zip(self.scalars.iter()) {
            match base {
                AssignedBase::Variable(p) => {
                    variable_bases.push(p.clone());
                    variable_scalars.push((scalar.scalar.clone(), scalar.bound.bits() as usize));
                }
                AssignedBase::Fixed(_) => {
                    fixed_bases.push(base.clone());
                    fixed_scalars.push(scalar.clone());
                }
            }
        }

        let collapsed_base = S::msm(layouter, curve_chip, &variable_scalars, &variable_bases)?;

        self.bases = fixed_bases;
        self.bases.push(AssignedBase::Variable(collapsed_base));

        self.scalars = fixed_scalars;
        self.scalars.push(AssignedBoundedScalar::one(layouter, scalar_chip)?);

        Ok(())
    }

    /// Scales all the scalars of the AssignedMsm by the given factor r.
    ///
    /// This function mutates self.
    pub fn scale(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        r: &AssignedBoundedScalar<S::F>,
    ) -> Result<(), Error> {
        self.scalars = (self.scalars.iter())
            .map(|s| mul_bounded_scalars(layouter, scalar_chip, s, r))
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(())
    }

    /// Accumulates two AssignedMSMs with the given scalar r.
    /// The resulting AssignedMSM evaluates (on `fixed_bases`) to
    /// `self.eval(fixed_bases) + r * other.eval(fixed_bases)`.
    pub fn accumulate_with_r(
        &self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: &Self,
        r: &AssignedBoundedScalar<S::F>,
    ) -> Result<Self, Error> {
        let mut other = other.clone();
        other.scale(layouter, scalar_chip, r)?;

        let mut acc = self.clone();
        acc.add_msm(&other);

        Ok(acc)
    }
}

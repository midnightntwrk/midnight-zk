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

//! A module for in-circuit partial MSMs and its off-circuit analog.
//! These MSM have a fixed-base part which is represented by the corresponding
//! scalars only.
//! (The bases are assumed to be fixed and globally known.)

use std::collections::{btree_map::Entry, BTreeMap, HashSet};

use ff::Field;
use midnight_curves::msm::msm_best;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::PolynomialLabel,
};

use crate::{
    field::AssignedNative,
    instructions::PublicInputInstructions,
    types::{InnerValue, Instantiable},
    verifier::{
        types::SelfEmulation,
        utils::{
            add_bounded_scalars, assign_bounded_scalars, mul_bounded_scalars, AssignedBoundedScalar,
        },
    },
};

/// An off-circuit base in a multi-scalar multiplication.
///
/// `Variable` stores the concrete curve point inline.
/// `Fixed` indicates that the point is a globally-known constant (e.g. a
/// verifying-key commitment, an SRS element, or the negated generator `-G`)
/// identified by its `PolynomialLabel`; the actual value is not stored here
/// and must be supplied when the MSM is evaluated or resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Point<S: SelfEmulation> {
    /// A concrete curve point whose value is known at this stage.
    Variable(S::C),
    /// A globally-known constant point, identified by its label.
    Fixed,
}

/// The in-circuit analog of [`Point`].
///
/// `Variable` holds an explicitly-assigned circuit cell.
/// `Fixed` means the base is a known constant (e.g. a VK-committed point, an
/// SRS element, or the negated generator); no cell is allocated for it in the
/// layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignedPoint<S: SelfEmulation> {
    /// A circuit-assigned variable-base point.
    Variable(S::AssignedPoint),
    /// A globally-known constant point that lives outside the circuit witness.
    Fixed,
}

impl<S: SelfEmulation> Point<S> {
    /// Returns a reference to the inner curve point.
    ///
    /// # Panics
    ///
    /// If this is a `Fixed` point whose value has not yet been resolved.
    /// Call `resolve_fixed_bases` before accessing the point.
    pub fn get_point(&self) -> &S::C {
        match self {
            Self::Variable(p) => p,
            Self::Fixed => {
                panic!("attempted to read an unresolved Fixed base; call resolve_fixed_bases first")
            }
        }
    }
}

impl<S: SelfEmulation> InnerValue for AssignedPoint<S> {
    type Element = Point<S>;

    fn value(&self) -> Value<Self::Element> {
        match self {
            AssignedPoint::Variable(p) => p.value().map(|v| Point::Variable(v)),
            AssignedPoint::Fixed => Value::known(Point::Fixed),
        }
    }
}

impl<S: SelfEmulation> Instantiable<S::F> for AssignedPoint<S> {
    fn as_public_input(point: &Point<S>) -> Vec<S::F> {
        match point {
            Point::Variable(p) => S::AssignedPoint::as_public_input(p),
            Point::Fixed => vec![],
        }
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(fields: &[S::F]) -> Option<Point<S>> {
        match fields {
            [] => Some(Point::Fixed),
            fs => S::AssignedPoint::from_public_input(fs).map(Point::Variable),
        }
    }
}

impl<S: SelfEmulation> AssignedPoint<S> {
    pub(crate) fn in_circuit_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        match self {
            AssignedPoint::Variable(p) => curve_chip.as_public_input(layouter, p),
            AssignedPoint::Fixed => Ok(vec![]),
        }
    }

    pub(crate) fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
    ) -> Result<(), Error> {
        match self {
            AssignedPoint::Variable(p) => curve_chip.constrain_as_public_input(layouter, p),
            AssignedPoint::Fixed => Ok(()),
        }
    }
}

/// Off-circuit multi-scalar multiplication with mixed fixed and variable bases.
///
/// This is the off-circuit analog of [`AssignedMsm`] and a generalization of
/// `MSMKZG` that can refer to some bases as "fixed" (globally-known constants).
/// The triple `(scalars, bases, labels)` is flat and parallel:
/// `scalars[i]` multiplies `bases[i]`, which is identified by `labels[i]`.
///
/// A `Fixed` base is not stored inline; its actual curve point is supplied
/// later via `resolve_fixed_bases` or `eval`.
///
/// Invariant: `scalars.len() == bases.len() == labels.len()`.
#[derive(Clone, Debug)]
pub struct Msm<S: SelfEmulation> {
    scalars: Vec<S::F>,
    bases: Vec<Point<S>>,
    labels: Vec<PolynomialLabel>,
}

/// Type for in-circuit multi-scalar multiplications.
///
/// This is the in-circuit analog of `Msm<C>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignedMsm<S: SelfEmulation> {
    scalars: Vec<AssignedBoundedScalar<S::F>>,
    bases: Vec<AssignedPoint<S>>,
    labels: Vec<PolynomialLabel>,
}

impl<S: SelfEmulation> Msm<S> {
    /// Creates a new MSM from the given slice of bases, scalars and labels.
    ///
    /// # Panics
    ///
    /// If `bases`, `scalars` and `labels` do not all have the same length.
    pub fn new(bases: &[Point<S>], scalars: &[S::F], labels: &[PolynomialLabel]) -> Self {
        assert_eq!(bases.len(), scalars.len());
        assert_eq!(bases.len(), labels.len());
        Msm {
            bases: bases.to_vec(),
            scalars: scalars.to_vec(),
            labels: labels.to_vec(),
        }
    }

    /// Builds an `Msm` from a slice of `(label, scalar, base)` triples, as
    /// returned by [`midnight_proofs::poly::kzg::msm::DualMSM::split`].
    ///
    /// Each base is classified as `Fixed` if its label appears in
    /// `fixed_bases` (with a sanity-check that the point matches the expected
    /// value), or `Variable` otherwise.
    pub fn from_terms(
        terms: &[(&PolynomialLabel, &S::F, &S::C)],
        fixed_bases: &BTreeMap<PolynomialLabel, S::C>,
    ) -> Self {
        let mut bases = Vec::with_capacity(terms.len());
        let mut scalars = Vec::with_capacity(terms.len());
        let mut labels = Vec::with_capacity(terms.len());

        for (label, scalar, &base) in terms {
            scalars.push(**scalar);
            labels.push((*label).clone());
            match fixed_bases.get(*label) {
                Some(expected) => {
                    assert_eq!(base, *expected);
                    bases.push(Point::Fixed);
                }
                None => bases.push(Point::Variable(base)),
            }
        }
        Msm::new(&bases, &scalars, &labels)
    }

    /// The bases of this MSM.
    pub fn bases(&self) -> Vec<Point<S>> {
        self.bases.clone()
    }

    /// The scalars of this MSM.
    pub fn scalars(&self) -> Vec<S::F> {
        self.scalars.clone()
    }

    /// The labels of this MSM.
    pub fn labels(&self) -> Vec<PolynomialLabel> {
        self.labels.clone()
    }

    /// Collapses the variable-base part into a single `(collapsed-point, 1)`
    /// term, labeling the result with `label`.
    ///
    /// All `Variable` entries are accumulated into one curve point via MSM and
    /// stored with scalar `1` and the given `label`.
    /// `Fixed` entries are preserved: terms sharing the same label have their
    /// scalars summed. After the call the MSM has exactly one `Variable` entry
    /// (the collapsed result) plus one `Fixed` entry per distinct fixed label.
    ///
    /// This function mutates `self`.
    pub fn collapse(&mut self, label: PolynomialLabel) {
        // We allocate max capacity but we may not fill it.
        let n = self.bases.len();
        let mut variable_bases = Vec::<S::G1Affine>::with_capacity(n);
        let mut variable_scalars = Vec::<S::F>::with_capacity(n);

        let mut fixed_base_scalars = BTreeMap::<PolynomialLabel, S::F>::new();

        for i in 0..n {
            match self.bases[i] {
                Point::Variable(p) => {
                    variable_bases.push(p.into());
                    variable_scalars.push(self.scalars[i]);
                }
                Point::Fixed => {
                    fixed_base_scalars
                        .entry(self.labels[i].clone())
                        .and_modify(|s| *s += self.scalars[i])
                        .or_insert(self.scalars[i]);
                }
            }
        }

        let mut bases = vec![Point::Fixed; fixed_base_scalars.len()];
        let mut scalars: Vec<_> = fixed_base_scalars.values().copied().collect();
        let mut labels: Vec<_> = fixed_base_scalars.keys().cloned().collect();

        let collapsed_base = msm_best(&variable_scalars, &variable_bases);
        bases.push(Point::Variable(collapsed_base));
        scalars.push(S::F::ONE);
        labels.push(label);

        self.bases = bases;
        self.scalars = scalars;
        self.labels = labels;
    }

    /// Resolves all `Fixed` bases by looking up their curve points in the map.
    ///
    /// Each `Fixed` entry is replaced with `Variable(fixed_bases[label])`.
    /// After this call, no `Fixed` entries remain.
    ///
    /// # Panics
    ///
    /// If any `Fixed` label is absent from `fixed_bases`.
    pub fn resolve_fixed_bases(&mut self, fixed_bases: &BTreeMap<PolynomialLabel, S::C>) {
        for (i, base) in self.bases.iter_mut().enumerate() {
            match base {
                Point::Variable(..) => (),
                Point::Fixed => {
                    let l = &self.labels[i];
                    let p = fixed_bases.get(l).unwrap_or_else(|| panic!("Base not provided: {l}"));
                    *base = Point::Variable(*p)
                }
            }
        }
    }

    /// Fully evaluates the MSM to a single curve point.
    ///
    /// Equivalent to calling `resolve_fixed_bases(fixed_bases)` followed by
    /// `collapse()`. Returns `∑ scalars[i] * bases[i]`, with all fixed bases
    /// substituted from the map.
    ///
    /// # Panics
    ///
    /// If any `Fixed` label is absent from `fixed_bases`.
    pub fn eval(&self, fixed_bases: &BTreeMap<PolynomialLabel, S::C>) -> S::C {
        let mut msm = self.clone();
        msm.resolve_fixed_bases(fixed_bases);
        msm.collapse(PolynomialLabel::NoLabel);

        debug_assert_eq!(msm.scalars, vec![S::F::ONE]);
        debug_assert_eq!(msm.labels, vec![PolynomialLabel::NoLabel]);

        match msm.bases.as_slice() {
            [Point::Variable(p)] => *p,
            _ => unreachable!(),
        }
    }

    /// Accumulates two MSMs with the given scalar r.
    /// The resulting MSM evaluates (on any `fixed_bases`) to
    /// `self.eval(fixed_bases) + r * other.eval(fixed_bases)`.
    pub fn accumulate_with_r(&self, other: &Self, r: S::F) -> Self {
        let mut acc = self.clone();

        acc.bases.extend(other.bases.clone());
        acc.scalars.extend(other.scalars.iter().map(|s| *s * r));
        acc.labels.extend(other.labels.clone());

        acc
    }
}

impl<S: SelfEmulation> InnerValue for AssignedMsm<S> {
    type Element = Msm<S>;

    fn value(&self) -> Value<Self::Element> {
        let bases: Value<Vec<Point<S>>> =
            Value::from_iter(self.bases.iter().map(|base| base.value()));

        let scalars: Value<Vec<S::F>> =
            Value::from_iter(self.scalars.iter().map(|s| s.scalar.value().copied()));

        let labels = self.labels.clone();

        scalars.zip(bases).map(|(scalars, bases)| Msm {
            bases,
            scalars,
            labels,
        })
    }
}

impl<S: SelfEmulation> Instantiable<S::F> for AssignedMsm<S> {
    fn as_public_input(msm: &Msm<S>) -> Vec<S::F> {
        [
            msm.bases
                .iter()
                .flat_map(AssignedPoint::<S>::as_public_input)
                .collect::<Vec<_>>(),
            msm.scalars.clone(),
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>()
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[S::F]) -> Option<Msm<S>> {
        unimplemented!("not invertible: the flat encoding loses structural metadata.")
    }
}

impl<S: SelfEmulation> AssignedMsm<S> {
    /// Creates a new in-circuit MSM from parallel slices of scalars, bases,
    /// and labels.
    ///
    /// # Panics
    ///
    /// If `bases`, `scalars` and `labels` do not all have the same length.
    pub fn new(
        scalars: &[AssignedBoundedScalar<S::F>],
        bases: &[AssignedPoint<S>],
        labels: &[PolynomialLabel],
    ) -> Self {
        assert_eq!(bases.len(), scalars.len());
        assert_eq!(bases.len(), labels.len());
        Self {
            bases: bases.to_vec(),
            scalars: scalars.to_vec(),
            labels: labels.to_vec(),
        }
    }

    /// The bases of this assigned MSM.
    pub fn bases(&self) -> Vec<AssignedPoint<S>> {
        self.bases.clone()
    }

    /// The scalars of this assigned MSM.
    pub fn scalars(&self) -> Vec<AssignedBoundedScalar<S::F>> {
        self.scalars.clone()
    }

    /// The labels of this assigned MSM.
    pub fn labels(&self) -> Vec<PolynomialLabel> {
        self.labels.clone()
    }

    /// Creates a single-term MSM from the given scalar, base, and label.
    pub fn from_term(
        scalar: AssignedBoundedScalar<S::F>,
        base: AssignedPoint<S>,
        label: PolynomialLabel,
    ) -> Self {
        Self::new(&[scalar], &[base], &[label])
    }

    /// Creates a single fixed-base term MSM with the given scalar and label.
    pub fn from_fixed_term(scalar: AssignedBoundedScalar<S::F>, label: PolynomialLabel) -> Self {
        Self::from_term(scalar, AssignedPoint::Fixed, label)
    }
}

impl<S: SelfEmulation> AssignedMsm<S> {
    /// Converts the off-circuit MSM into two vectors of scalars. The first
    /// will be used as a normal instance, whereas the second will be plugged-in
    /// in as a committed instance.
    ///
    /// The committed instance part corresponds to the scalars of the MSM.
    pub fn as_public_input_with_committed_scalars(msm: &Msm<S>) -> (Vec<S::F>, Vec<S::F>) {
        let normal_instance =
            msm.bases.iter().flat_map(AssignedPoint::<S>::as_public_input).collect();

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
        Ok([
            self.bases
                .iter()
                .map(|base| base.in_circuit_as_public_input(layouter, curve_chip))
                .collect::<Result<Vec<_>, Error>>()?
                .concat(),
            self.scalars.iter().map(|s| s.clone().scalar).collect::<Vec<_>>(),
        ]
        .concat())
    }

    pub(crate) fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
    ) -> Result<(), Error> {
        self.bases
            .iter()
            .try_for_each(|base| base.constrain_as_public_input(layouter, curve_chip))?;

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
        self.bases
            .iter()
            .try_for_each(|base| base.constrain_as_public_input(layouter, curve_chip))?;

        self.scalars.iter().try_for_each(|s| {
            let mut a = S::F::ZERO;
            s.scalar.clone().value().map(|v| a = *v);
            S::constrain_scalar_as_committed_public_input(layouter, scalar_chip, &s.scalar)
        })
    }
}

impl<S: SelfEmulation> AssignedMsm<S> {
    /// Witnesses all scalar cells and variable-base point cells for this MSM.
    ///
    /// The `labels` slice determines the shape: entries whose label is in
    /// `fixed_base_labels` are represented as `AssignedPoint::Fixed` (no cell
    /// allocated for the point); all other entries are assigned as
    /// `AssignedPoint::Variable`.
    ///
    /// # Warning
    ///
    /// Variable-base points are not checked for subgroup membership.
    ///
    /// # Errors
    ///
    /// If `msm_value` is known and its label list differs from `labels`.
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        labels: &[PolynomialLabel],
        fixed_base_labels: &HashSet<PolynomialLabel>,
        msm_value: Value<Msm<S>>,
    ) -> Result<Self, Error> {
        let len = labels.len();
        assert!(fixed_base_labels.len() <= len);
        msm_value.error_if_known_and(|msm| msm.labels != labels)?;

        let scalars_val = msm_value.as_ref().map(|msm| msm.scalars.clone()).transpose_vec(len);
        let bases_val = msm_value.as_ref().map(|msm| msm.bases.clone()).transpose_vec(len);

        let scalars = assign_bounded_scalars(layouter, scalar_chip, &scalars_val)?;
        let mut bases = Vec::<AssignedPoint<S>>::with_capacity(len);

        for i in 0..len {
            if fixed_base_labels.contains(&labels[i]) {
                bases_val[i].error_if_known_and(|p| matches!(p, Point::Variable(..)))?;
                bases.push(AssignedPoint::Fixed);
            } else {
                bases_val[i].error_if_known_and(|p| matches!(p, Point::Fixed))?;
                let p_val = bases_val[i].clone().map(|p| match p {
                    Point::Variable(p) => p,
                    Point::Fixed => unreachable!(),
                });
                let p = S::assign_without_subgroup_check(layouter, curve_chip, p_val)?;
                bases.push(AssignedPoint::Variable(p));
            }
        }

        Ok(AssignedMsm {
            scalars,
            bases,
            labels: labels.to_vec(),
        })
    }

    /// An empty AssignedMsm with no fixed base scalars, that evaluates to the
    /// identity point.
    pub fn empty() -> Self {
        Self {
            scalars: vec![],
            bases: vec![],
            labels: vec![],
        }
    }

    /// Appends a `(scalar, base, label)` term to this MSM.
    pub fn add_term(
        &mut self,
        scalar: &AssignedBoundedScalar<S::F>,
        base: &AssignedPoint<S>,
        label: &PolynomialLabel,
    ) {
        self.scalars.push(scalar.clone());
        self.bases.push(base.clone());
        self.labels.push(label.clone());
    }

    /// Adds two AssignedMsm.
    pub fn add_msm(&mut self, other: &Self) -> Result<(), Error> {
        self.scalars.extend(other.scalars.clone());
        self.bases.extend(other.bases.clone());
        self.labels.extend(other.labels.clone());
        Ok(())
    }

    /// In-circuit analog of [`Msm::collapse`].
    ///
    /// Reduces the variable-base part to a single MSM point via the circuit's
    /// MSM chip, labeling the result with `label`. Fixed-base terms sharing the
    /// same label have their scalars added in-circuit. After the call, the MSM
    /// has one `Variable` entry (the collapsed result) and one `Fixed` entry
    /// per distinct fixed label.
    ///
    /// This function mutates `self`.
    pub fn collapse(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        label: PolynomialLabel,
    ) -> Result<(), Error> {
        // We allocate max capacity but we may not fill it.
        let n = self.bases.len();
        let mut variable_bases = Vec::with_capacity(n);
        let mut variable_scalars = Vec::with_capacity(n);

        let mut fixed_base_scalars =
            BTreeMap::<PolynomialLabel, AssignedBoundedScalar<S::F>>::new();

        for i in 0..n {
            match self.bases[i].clone() {
                AssignedPoint::Variable(p) => {
                    let s = self.scalars[i].clone();
                    variable_bases.push(p.clone());
                    variable_scalars.push((s.scalar, s.bound.bits() as usize));
                }
                AssignedPoint::Fixed => match fixed_base_scalars.entry(self.labels[i].clone()) {
                    Entry::Occupied(mut occ) => {
                        let s = add_bounded_scalars(
                            layouter,
                            scalar_chip,
                            occ.get(),
                            &self.scalars[i],
                        )?;
                        *occ.get_mut() = s;
                    }
                    Entry::Vacant(vac) => {
                        vac.insert(self.scalars[i].clone());
                    }
                },
            }
        }

        let mut bases = vec![AssignedPoint::Fixed; fixed_base_scalars.len()];
        let mut scalars: Vec<_> = fixed_base_scalars.values().cloned().collect();
        let mut labels: Vec<_> = fixed_base_scalars.keys().cloned().collect();

        let collapsed_base = S::msm(layouter, curve_chip, &variable_scalars, &variable_bases)?;
        bases.push(AssignedPoint::Variable(collapsed_base));
        scalars.push(AssignedBoundedScalar::one(layouter, scalar_chip)?);
        labels.push(label);

        self.bases = bases;
        self.scalars = scalars;
        self.labels = labels;

        Ok(())
    }

    /// Resolves all `Fixed` bases by substituting their assigned circuit
    /// points.
    ///
    /// Each `Fixed` entry is replaced with `Variable(fixed_bases[label])`.
    /// After this call, no `Fixed` entries remain.
    ///
    /// This is the in-circuit analog of [Msm::resolve_fixed_bases].
    ///
    /// # Panics
    ///
    /// If any `Fixed` label is absent from `fixed_bases`.
    pub fn resolve_fixed_bases(
        &mut self,
        fixed_bases: &BTreeMap<PolynomialLabel, S::AssignedPoint>,
    ) {
        for (i, base) in self.bases.iter_mut().enumerate() {
            match base {
                AssignedPoint::Variable(..) => (),
                AssignedPoint::Fixed => {
                    let l = &self.labels[i];
                    let p = fixed_bases.get(l).unwrap_or_else(|| panic!("Base not provided: {l}"));
                    *base = AssignedPoint::Variable(p.clone())
                }
            }
        }
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

    /// Accumulates two AssignedMSMs with the a given scalar r.
    /// The resulting AssignedMSMs evaluates (on `fixed_bases`) to
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
        acc.add_msm(&other)?;

        Ok(acc)
    }
}

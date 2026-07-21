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

//! Module for in-circuit accumulators (and their off-circuit counterpart).
//!
//! An accumulator is a pair of points (lhs, rhs), represented with
//! respective MSMs that is supposed to satisfy:
//!
//!   e(lhs, \[τ\]₂) = e(rhs, \[1\]₂)
//!
//! where τ is the corresponding SRS toxic waste.
//!
//! This property is preserved by the `accumulate` function, which combines two
//! accumulators into one; the resulting accumulator satisfies the property iff
//! both inputs do. We thus call this property the accumulator "invariant".
//!
//! Note that implication <= holds unconditionally, whereas implication => holds
//! "computationally".

use std::collections::{BTreeMap, HashSet};

use ff::Field;
use group::Group;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{
        kzg::{
            msm::{DualMSM, MSMKZG},
            params::ParamsVerifierKZG,
        },
        PolynomialLabel,
    },
};
use num_bigint::BigUint;
use num_traits::One;

#[cfg(not(feature = "truncated-challenges"))]
use crate::verifier::utils::powers;
#[cfg(feature = "truncated-challenges")]
use crate::verifier::utils::{truncate_off_circuit, truncated_powers};
use crate::{
    instructions::{hash::HashCPU, HashInstructions, PublicInputInstructions},
    types::{AssignedBit, InnerValue, Instantiable},
    verifier::{
        msm::{AssignedMsm, Msm, Point},
        utils::AssignedBoundedScalar,
        SelfEmulation,
    },
};

/// Type for off-circuit accumulators.
///
/// Note that the points are represented with MSMs which may have
/// a fixed-base scalars part. In order to evaluate the accumulator, one may
/// thus need to provide the corresponding fixed bases.
#[derive(Clone, Debug)]
pub struct Accumulator<S: SelfEmulation> {
    lhs: Msm<S>,
    rhs: Msm<S>,
}

/// Type for in-circuit accumulators (in-circuit analog of `Accumulator`).
#[derive(Clone, Debug)]
pub struct AssignedAccumulator<C: SelfEmulation> {
    pub(crate) lhs: AssignedMsm<C>,
    pub(crate) rhs: AssignedMsm<C>,
}

impl<S: SelfEmulation> Accumulator<S> {
    /// Converts an off-circuit [`DualMSM`] produced by the KZG verifier into an
    /// [`Accumulator`].
    ///
    /// For each term in the dual MSM, the label is looked up in `fixed_bases`:
    /// * if found, the term is recorded as `Point::Fixed` and the expected base
    ///   value is asserted to match (sanity check);
    /// * otherwise, the term is recorded as `Point::Variable` with the base
    ///   stored inline.
    pub fn from_dual_msm(
        dual_msm: DualMSM<S::Engine>,
        fixed_bases: &BTreeMap<PolynomialLabel, S::C>,
    ) -> Self {
        let (lhs, rhs) = dual_msm.split();
        Accumulator {
            lhs: Msm::from_terms(&lhs, fixed_bases),
            rhs: Msm::from_terms(&rhs, fixed_bases),
        }
    }

    /// Checks whether the accumulator, when evaluated with the provided
    /// fixed-bases, satisfies the pairing invariant w.r.t. the SRS verifier
    /// parameters.
    pub fn check(
        &self,
        params: &ParamsVerifierKZG<S::Engine>,
        fixed_bases: &BTreeMap<PolynomialLabel, S::C>,
    ) -> bool {
        let lhs = MSMKZG::<S::Engine>::from_base(&self.lhs.eval(fixed_bases));
        let rhs = MSMKZG::<S::Engine>::from_base(&self.rhs.eval(fixed_bases));
        DualMSM::new(lhs, rhs).check(params)
    }

    /// Returns a trivial accumulator that satisfies the pairing invariant.
    ///
    /// Both sides evaluate to the identity point for any `fixed_bases` map:
    /// * LHS: a single `Variable(identity)` with scalar `1`, label `NoLabel`.
    /// * RHS: one `Fixed` entry per label in `fixed_base_labels` with scalar
    ///   `0` (contributing nothing), plus one `Variable(identity)` with scalar
    ///   `1` and label `NoLabel`.
    pub fn trivial(fixed_base_labels: &[PolynomialLabel]) -> Self {
        let n = fixed_base_labels.len();
        let id = S::C::identity();

        Accumulator {
            lhs: Msm::new(
                &[Point::Variable(id)],
                &[S::F::ONE],
                &[PolynomialLabel::NoLabel],
            ),
            rhs: Msm::new(
                &[vec![Point::Fixed; n], vec![Point::Variable(id)]].concat(),
                &[vec![S::F::ZERO; n], vec![S::F::ONE]].concat(),
                &[fixed_base_labels, &[PolynomialLabel::NoLabel]].concat(),
            ),
        }
    }

    /// An accumulator a given lhs and rhs terms respectively.
    pub fn new(lhs: Msm<S>, rhs: Msm<S>) -> Self {
        Accumulator { lhs, rhs }
    }

    /// The left-hand side of this accumulator.
    pub fn lhs(&self) -> Msm<S> {
        self.lhs.clone()
    }

    /// The right-hand side of this accumulator.
    pub fn rhs(&self) -> Msm<S> {
        self.rhs.clone()
    }

    /// Given the actual fixed bases, resolves the fixed-base part of the
    /// internal MSMs by pairing each named scalar with its base and moving
    /// them to regular variable-base entries.
    ///
    /// After this call, `fixed_base_scalars` of each internal MSM becomes
    /// empty.
    ///
    /// # Panics
    ///
    /// If some of the keys in `fixed_base_scalars` from the internal MSMs do
    /// not appear in the provided `fixed_bases` map.
    pub fn resolve_fixed_bases(&mut self, fixed_bases: &BTreeMap<PolynomialLabel, S::C>) {
        self.lhs.resolve_fixed_bases(fixed_bases);
        self.rhs.resolve_fixed_bases(fixed_bases);
    }

    /// Evaluates the variable part of the Accumulator collapsing each
    /// side to a single point (and a scalar of 1), leaving the fixed-base part
    /// of both sides intact.
    ///
    /// This function mutates self.
    pub fn collapse(&mut self) {
        self.lhs.collapse(PolynomialLabel::NoLabel);
        self.rhs.collapse(PolynomialLabel::NoLabel);
    }

    /// Accumulates several accumulators together. The resulting acc will
    /// satisfy the invariant iff all the accumulators individually do.
    pub fn accumulate(accs: &[Self]) -> Self {
        let hash_input =
            accs.iter().flat_map(AssignedAccumulator::as_public_input).collect::<Vec<_>>();

        let r = <S::SpongeChip as HashCPU<S::F, S::F>>::hash(&hash_input);
        let rs = (0..accs.len()).map(|i| r.pow([i as u64]));
        #[cfg(feature = "truncated-challenges")]
        let rs = rs.map(truncate_off_circuit).collect::<Vec<_>>();

        let mut acc = accs[0].clone();
        for (other, ri) in accs.iter().zip(rs).skip(1) {
            acc.lhs = acc.lhs.accumulate_with_r(&other.lhs, ri);
            acc.rhs = acc.rhs.accumulate_with_r(&other.rhs, ri);
        }

        acc
    }
}

impl<S: SelfEmulation> InnerValue for AssignedAccumulator<S> {
    type Element = Accumulator<S>;

    fn value(&self) -> Value<Accumulator<S>> {
        (self.lhs.value())
            .zip(self.rhs.value())
            .map(|(lhs, rhs)| Accumulator { lhs, rhs })
    }
}

impl<S: SelfEmulation> Instantiable<S::F> for AssignedAccumulator<S> {
    fn as_public_input(acc: &Accumulator<S>) -> Vec<S::F> {
        [
            AssignedMsm::as_public_input(&acc.lhs),
            AssignedMsm::as_public_input(&acc.rhs),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[S::F]) -> Option<Accumulator<S>> {
        unimplemented!("Size of inner MSMs cannot be known from public input format.")
    }
}

impl<S: SelfEmulation> AssignedAccumulator<S> {
    /// Converts the off-circuit accumulator into two vectors of scalars. The
    /// first will be used as a normal instance, whereas the second will be
    /// plugged-in in as a committed instance.
    ///
    /// The committed instance part corresponds to the MSM (fixed and non-fixed)
    /// scalars of the accumulator RHS.
    pub fn as_public_input_with_committed_scalars(acc: &Accumulator<S>) -> (Vec<S::F>, Vec<S::F>) {
        let (rhs_normal_pi, rhs_committed_pi) =
            AssignedMsm::as_public_input_with_committed_scalars(&acc.rhs);

        let normal_instance = [AssignedMsm::as_public_input(&acc.lhs), rhs_normal_pi]
            .into_iter()
            .flatten()
            .collect();

        (normal_instance, rhs_committed_pi)
    }
}

impl<S: SelfEmulation> AssignedAccumulator<S> {
    /// Witnesses both sides of a KZG accumulator in the circuit.
    ///
    /// Each side is shaped by its `labels` slice (one entry per scalar/base
    /// pair) and its `fixed_base_labels` set (entries whose label appears
    /// there become `AssignedPoint::Fixed`; the rest are assigned as
    /// variable-base points).
    ///
    /// # Errors
    ///
    /// If the known accumulator value's label list does not match the supplied
    /// `lhs_labels` / `rhs_labels`.
    #[allow(clippy::too_many_arguments)]
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        lhs_labels: &[PolynomialLabel],
        rhs_labels: &[PolynomialLabel],
        lhs_fixed_base_labels: &HashSet<PolynomialLabel>,
        rhs_fixed_base_labels: &HashSet<PolynomialLabel>,
        acc_val: Value<Accumulator<S>>,
    ) -> Result<Self, Error> {
        let (acc_lhs_val, acc_rhs_val) = acc_val.map(|acc| (acc.lhs, acc.rhs)).unzip();
        Ok(AssignedAccumulator::new(
            AssignedMsm::<S>::assign(
                layouter,
                curve_chip,
                scalar_chip,
                lhs_labels,
                lhs_fixed_base_labels,
                acc_lhs_val,
            )?,
            AssignedMsm::<S>::assign(
                layouter,
                curve_chip,
                scalar_chip,
                rhs_labels,
                rhs_fixed_base_labels,
                acc_rhs_val,
            )?,
        ))
    }

    /// An `AssignedAccumulator` a given lhs and rhs terms respectively.
    pub fn new(lhs: AssignedMsm<S>, rhs: AssignedMsm<S>) -> Self {
        Self { lhs, rhs }
    }

    /// Scales the given acc by the given assigned bit.
    ///
    /// This function mutates self.
    pub fn scale_by_bit(
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        cond: &AssignedBit<S::F>,
        acc: &mut Self,
    ) -> Result<(), Error> {
        let cond_as_bounded = AssignedBoundedScalar {
            scalar: cond.clone().into(),
            bound: BigUint::one(),
        };
        acc.lhs.scale(layouter, scalar_chip, &cond_as_bounded)?;
        acc.rhs.scale(layouter, scalar_chip, &cond_as_bounded)
    }

    /// Evaluates the variable part of the AssignedAccumulator collapsing each
    /// side to a single point (and a scalar of 1), leaving the fixed-base part
    /// of both sides intact.
    ///
    /// Calls to this function will probably be the bottleneck of any recursive
    /// circuit, but it allows one to condense a carrying computation into a
    /// single point, enabling powerful predicates such as
    /// incrementally-verifiable computation (IVC).
    ///
    /// Alternatively, one may choose not to collapse an accumulator, fully
    /// restrict it with public inputs and evaluate it off-circuit.
    ///
    /// This function mutates self.
    pub fn collapse(
        &mut self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
    ) -> Result<(), Error> {
        self.lhs.collapse(layouter, curve_chip, scalar_chip, PolynomialLabel::NoLabel)?;
        self.rhs.collapse(layouter, curve_chip, scalar_chip, PolynomialLabel::NoLabel)
    }

    /// Resolves all `Fixed` bases in both internal MSMs by substituting their
    /// assigned circuit points from `fixed_bases`.
    ///
    /// After this call, `lhs` and `rhs` contain no `Fixed` entries; every base
    /// has been materialized into an `AssignedPoint::Variable` circuit cell.
    ///
    /// # Panics
    ///
    /// If any `Fixed` label in either MSM is absent from `fixed_bases`.
    pub fn resolve_fixed_bases(
        &mut self,
        fixed_bases: &BTreeMap<PolynomialLabel, S::AssignedPoint>,
    ) {
        self.lhs.resolve_fixed_bases(fixed_bases);
        self.rhs.resolve_fixed_bases(fixed_bases);
    }

    /// Accumulates several accumulators together. The resulting acc will
    /// satisfy the invariant iff all the accumulators individually do.
    pub fn accumulate(
        layouter: &mut impl Layouter<S::F>,
        acc_pi_chip: &impl PublicInputInstructions<S::F, AssignedAccumulator<S>>,
        scalar_chip: &S::ScalarChip,
        sponge_chip: &S::SpongeChip,
        accs: &[Self],
    ) -> Result<Self, Error> {
        let hash_input = accs
            .iter()
            .map(|acc| acc_pi_chip.as_public_input(layouter, acc))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let r = sponge_chip.hash(layouter, &hash_input)?;
        #[cfg(feature = "truncated-challenges")]
        let rs = truncated_powers::<S::F>(layouter, scalar_chip, &r, accs.len())?;
        #[cfg(not(feature = "truncated-challenges"))]
        let rs = powers::<S::F>(layouter, scalar_chip, &r, accs.len())?
            .iter()
            .map(|ri| AssignedBoundedScalar::new(ri, None))
            .collect::<Vec<_>>();

        let mut acc = accs[0].clone();
        for (other, ri) in accs.iter().zip(rs).skip(1) {
            acc.lhs = acc.lhs.accumulate_with_r(layouter, scalar_chip, &other.lhs, &ri)?;
            acc.rhs = acc.rhs.accumulate_with_r(layouter, scalar_chip, &other.rhs, &ri)?;
        }

        Ok(acc)
    }
}

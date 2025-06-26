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

use std::collections::BTreeMap;

use group::prime::PrimeCurveAffine;
use halo2curves::pairing::Engine;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::msm::DualMSM,
};
use num_bigint::BigUint;
use num_traits::One;

use crate::{
    instructions::{hash::HashCPU, HashInstructions, PublicInputInstructions},
    types::{AssignedBit, InnerValue, Instantiable},
    verifier::{
        msm::{AssignedMsm, Msm},
        types::{CurveChip, ScalarChip, SpongeChip},
        utils::{truncate, truncate_off_circuit, AssignedBoundedScalar},
        SelfEmulationCurve,
    },
};

/// Type for off-circuit accumulators.
///
/// Note that the points are represented with MSMs which may have
/// a fixed-base scalars part. In order to evaluate the accumulator, one may
/// thus need to provide the corresponding fixed bases.
#[derive(Clone, Debug)]
pub struct Accumulator<C: SelfEmulationCurve> {
    lhs: Msm<C>,
    rhs: Msm<C>,
}

/// Type for in-circuit accumulators (in-circuit analog of `Accumulator`).
#[derive(Clone, Debug)]
pub struct AssignedAccumulator<C: SelfEmulationCurve> {
    pub(crate) lhs: AssignedMsm<C>,
    pub(crate) rhs: AssignedMsm<C>,
}

impl<C: SelfEmulationCurve> From<DualMSM<C::Engine>> for Accumulator<C> {
    fn from(dual_msm: DualMSM<C::Engine>) -> Self {
        let (lhs, rhs) = dual_msm.split();

        let lhs: (Vec<C>, Vec<C::ScalarField>) = lhs.into_iter().map(|(s, b)| (*b, *s)).unzip();
        let rhs: (Vec<C>, Vec<C::ScalarField>) = rhs.into_iter().map(|(s, b)| (*b, *s)).unzip();

        Accumulator {
            lhs: Msm::from_terms(&lhs.0, &lhs.1),
            rhs: Msm::from_terms(&rhs.0, &rhs.1),
        }
    }
}

impl<C: SelfEmulationCurve> Accumulator<C> {
    /// Checks whether the accumulator, when evaluated with the provided
    /// fixed-bases, satisfies the invariant w.r.t. the given \[τ\]₂.
    pub fn check(&self, tau_in_g2: &C::G2Affine, fixed_bases: &BTreeMap<String, C>) -> bool {
        // TODO: Share the Miller-loop?
        let lhs = self.lhs.eval(fixed_bases).into();
        let rhs = self.rhs.eval(fixed_bases).into();
        C::Engine::pairing(&lhs, tau_in_g2) == C::Engine::pairing(&rhs, &C::G2Affine::generator())
    }

    /// An accumulator a given lhs and rhs terms respectively.
    pub fn new(lhs: Msm<C>, rhs: Msm<C>) -> Self {
        Accumulator { lhs, rhs }
    }

    /// Evaluates the variable part of the Accumulator collapsing each
    /// side to a single point (and a scalar of 1), leaving the fixed-base part
    /// of both sides intact.
    ///
    /// This function mutates self.
    pub fn collapse(&mut self) {
        self.lhs.collapse();
        self.rhs.collapse();
    }

    /// Accumulates `self` with `other`.
    /// The resulting acc will satisfy the invariant iff `self` and `other` do.
    pub fn accumulate(&self, other: &Self) -> Self {
        let hash_input = vec![
            AssignedAccumulator::as_public_input(self),
            AssignedAccumulator::as_public_input(other),
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

        let r = <SpongeChip<C> as HashCPU<C::ScalarField, C::ScalarField>>::hash(&hash_input);
        let r = truncate_off_circuit(r);

        Self {
            lhs: self.lhs.accumulate_with_r(&other.lhs, r),
            rhs: self.rhs.accumulate_with_r(&other.rhs, r),
        }
    }

    /// Given a set of fixed bases (a map indexed by the base name),
    /// removes the given fixed bases from `self.rhs.bases` and their
    /// corresponding scalar is moved to `self.rhs.fixed_base_scalars` with the
    /// base name as key.
    ///
    /// The resulting Accumulator is equivalent to the original one.
    /// Note that this function mutates self.
    ///
    /// Also, note that the lhs is not affected.
    ///
    /// # Warning
    ///
    /// If some of the fixed bases are repeated (different name but same point),
    /// they are removed from `self.rhs.bases` in the order dictated by the map
    /// `fixed_bases`.
    ///
    /// # Panics
    ///    
    /// If some of the base names exist as a key in
    /// `self.rhs.fixed_base_scalars`.
    ///
    /// If some of the provided fixed bases does not appear in `self.rhs.bases`
    /// with the exact required multiplicity.
    pub fn extract_fixed_bases(&mut self, fixed_bases: &BTreeMap<String, C>) {
        self.rhs.extract_fixed_bases(fixed_bases);
    }
}

impl<C: SelfEmulationCurve> InnerValue for AssignedAccumulator<C> {
    type Element = Accumulator<C>;

    fn value(&self) -> Value<Accumulator<C>> {
        (self.lhs.value())
            .zip(self.rhs.value())
            .map(|(lhs, rhs)| Accumulator { lhs, rhs })
    }
}

impl<C: SelfEmulationCurve> Instantiable<C::ScalarField> for AssignedAccumulator<C> {
    fn as_public_input(acc: &Accumulator<C>) -> Vec<C::ScalarField> {
        [
            AssignedMsm::as_public_input(&acc.lhs),
            AssignedMsm::as_public_input(&acc.rhs),
        ]
        .into_iter()
        .flatten()
        .collect()
    }
}

impl<C: SelfEmulationCurve> AssignedAccumulator<C> {
    /// Witnesses an accumulator of `lhs_len` bases/scalars and a `BTreeMap` of
    /// fixed_base_scalars indexed by the given `lhs_fixed_base_names`.
    ///
    /// Similar arguments determine the size and shape of the accumulator
    /// right-hand side.
    #[allow(clippy::too_many_arguments)]
    pub fn assign(
        layouter: &mut impl Layouter<C::ScalarField>,
        curve_chip: &CurveChip<C>,
        scalar_chip: &ScalarChip<C>,
        lhs_len: usize,
        rhs_len: usize,
        lhs_fixed_base_names: &[String],
        rhs_fixed_base_names: &[String],
        acc_val: Value<Accumulator<C>>,
    ) -> Result<Self, Error> {
        let (acc_lhs_val, acc_rhs_val) = acc_val.map(|acc| (acc.lhs, acc.rhs)).unzip();
        Ok(AssignedAccumulator::new(
            AssignedMsm::<C>::assign(
                layouter,
                curve_chip,
                scalar_chip,
                lhs_len,
                lhs_fixed_base_names,
                acc_lhs_val,
            )?,
            AssignedMsm::<C>::assign(
                layouter,
                curve_chip,
                scalar_chip,
                rhs_len,
                rhs_fixed_base_names,
                acc_rhs_val,
            )?,
        ))
    }

    /// An `AssignedAccumulator` a given lhs and rhs terms respectively.
    pub fn new(lhs: AssignedMsm<C>, rhs: AssignedMsm<C>) -> Self {
        Self { lhs, rhs }
    }

    /// Scales the given acc by the given assigned bit.
    ///
    /// This function mutates self.
    pub fn scale_by_bit(
        layouter: &mut impl Layouter<C::ScalarField>,
        scalar_chip: &ScalarChip<C>,
        cond: &AssignedBit<C::ScalarField>,
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
        layouter: &mut impl Layouter<C::ScalarField>,
        curve_chip: &CurveChip<C>,
        scalar_chip: &ScalarChip<C>,
    ) -> Result<(), Error> {
        self.lhs.collapse(layouter, curve_chip, scalar_chip)?;
        self.rhs.collapse(layouter, curve_chip, scalar_chip)
    }

    /// Accumulates `self` with `other`.
    /// The resulting acc will satisfy the invariant iff `self` and `other` do.
    pub fn accumulate(
        &self,
        layouter: &mut impl Layouter<C::ScalarField>,
        acc_pi_chip: &impl PublicInputInstructions<C::ScalarField, AssignedAccumulator<C>>,
        scalar_chip: &ScalarChip<C>,
        sponge_chip: &SpongeChip<C>,
        other: &Self,
    ) -> Result<Self, Error> {
        let hash_input = vec![
            acc_pi_chip.as_public_input(layouter, self)?,
            acc_pi_chip.as_public_input(layouter, other)?,
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

        let r = sponge_chip.hash(layouter, &hash_input)?;
        let r = truncate(layouter, scalar_chip, &r)?;

        Ok(AssignedAccumulator::new(
            self.lhs
                .accumulate_with_r(layouter, scalar_chip, &other.lhs, &r)?,
            self.rhs
                .accumulate_with_r(layouter, scalar_chip, &other.rhs, &r)?,
        ))
    }
}

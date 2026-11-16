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

use std::collections::BTreeMap;

use ff::Field;
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{
        PolynomialLabel,
        kzg::{
            msm::{DualMSM, MSMKZG},
            params::ParamsVerifierKZG,
        },
    },
};
use num_bigint::BigUint;
use num_traits::One;

use crate::{
    field::AssignedNative,
    instructions::{HashInstructions, hash::HashCPU},
    types::{AssignedBit, InnerValue, Instantiable},
    verifier::{
        ScalarChip,
        kzg::InCircuitKZGEngine,
        msm::{AssignedMsm, Msm, Point},
        types::{AssignedG1, CurveChip},
        utils::{AssignedBoundedScalar, truncate_off_circuit, truncated_powers},
    },
};

/// Type for off-circuit accumulators.
///
/// Note that the points are represented with MSMs which may have
/// a fixed-base scalars part. In order to evaluate the accumulator, one may
/// thus need to provide the corresponding fixed bases.
#[derive(Clone, Debug)]
pub struct Accumulator<E: MultiMillerLoop> {
    lhs: Msm<E>,
    rhs: Msm<E>,
}

/// Type for in-circuit accumulators (in-circuit analog of `Accumulator`).
#[derive(Clone, Debug)]
pub struct AssignedAccumulator<E: InCircuitKZGEngine> {
    pub(crate) lhs: AssignedMsm<E>,
    pub(crate) rhs: AssignedMsm<E>,
}

impl<E: InCircuitKZGEngine> Accumulator<E> {
    /// Converts an off-circuit [`DualMSM`] produced by the KZG verifier into an
    /// [`Accumulator`].
    ///
    /// For each term in the dual MSM, the label is looked up in `fixed_bases`:
    /// * if found, the term is recorded as `Point::Fixed` and the expected base
    ///   value is asserted to match (sanity check);
    /// * otherwise, the term is recorded as `Point::Variable` with the base
    ///   stored inline.
    pub fn from_dual_msm(
        dual_msm: DualMSM<E>,
        fixed_bases: &BTreeMap<PolynomialLabel, E::G1>,
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
        params: &ParamsVerifierKZG<E>,
        fixed_bases: &BTreeMap<PolynomialLabel, E::G1>,
    ) -> bool {
        let lhs = MSMKZG::<E>::from_base(&self.lhs.eval(fixed_bases));
        let rhs = MSMKZG::<E>::from_base(&self.rhs.eval(fixed_bases));
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
        let id = E::G1::identity();

        Accumulator {
            lhs: Msm::new(
                &[Point::Variable(id)],
                &[E::Fr::ONE],
                &[PolynomialLabel::NoLabel],
            ),
            rhs: Msm::new(
                &[vec![Point::Fixed; n], vec![Point::Variable(id)]].concat(),
                &[vec![E::Fr::ZERO; n], vec![E::Fr::ONE]].concat(),
                &[fixed_base_labels, &[PolynomialLabel::NoLabel]].concat(),
            ),
        }
    }

    /// An accumulator a given lhs and rhs terms respectively.
    pub fn new(lhs: Msm<E>, rhs: Msm<E>) -> Self {
        Accumulator { lhs, rhs }
    }

    /// The left-hand side of this accumulator.
    pub fn lhs(&self) -> Msm<E> {
        self.lhs.clone()
    }

    /// The right-hand side of this accumulator.
    pub fn rhs(&self) -> Msm<E> {
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
    pub fn resolve_fixed_bases(&mut self, fixed_bases: &BTreeMap<PolynomialLabel, E::G1>) {
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
    ///
    /// The accumulation randomness is derived with `H`, which must match the
    /// hash used by the in-circuit [`AssignedAccumulator::accumulate`].
    pub fn accumulate<H: HashCPU<E::Fr, E::Fr>>(accs: &[Self]) -> Self {
        let hash_input =
            accs.iter().flat_map(AssignedAccumulator::as_public_input).collect::<Vec<_>>();

        let r = H::hash(&hash_input);
        let rs = (0..accs.len()).map(|i| r.pow([i as u64]));
        let rs = rs.map(truncate_off_circuit).collect::<Vec<_>>();

        let mut acc = accs[0].clone();
        for (other, ri) in accs.iter().zip(rs).skip(1) {
            acc.lhs = acc.lhs.accumulate_with_r(&other.lhs, ri);
            acc.rhs = acc.rhs.accumulate_with_r(&other.rhs, ri);
        }

        acc
    }
}

impl<E: InCircuitKZGEngine> InnerValue for AssignedAccumulator<E> {
    type Element = Accumulator<E>;

    fn value(&self) -> Value<Accumulator<E>> {
        (self.lhs.value())
            .zip(self.rhs.value())
            .map(|(lhs, rhs)| Accumulator { lhs, rhs })
    }
}

impl<E: InCircuitKZGEngine> Instantiable<E::Fr> for AssignedAccumulator<E> {
    fn as_public_input(acc: &Accumulator<E>) -> Vec<E::Fr> {
        [
            AssignedMsm::as_public_input(&acc.lhs),
            AssignedMsm::as_public_input(&acc.rhs),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    /// Always returns `None`: the encoding is not invertible, since the size of
    /// the inner MSMs cannot be known from the public input format.
    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[E::Fr]) -> Option<Accumulator<E>> {
        None
    }
}

impl<E: InCircuitKZGEngine> AssignedAccumulator<E> {
    /// Converts the off-circuit accumulator into two vectors of scalars. The
    /// first will be used as a normal instance, whereas the second will be
    /// plugged-in in as a committed instance.
    ///
    /// The committed instance part corresponds to the MSM (fixed and non-fixed)
    /// scalars of the accumulator RHS.
    pub fn as_public_input_with_committed_scalars(
        acc: &Accumulator<E>,
    ) -> (Vec<E::Fr>, Vec<E::Fr>) {
        let (rhs_normal_pi, rhs_committed_pi) =
            AssignedMsm::as_public_input_with_committed_scalars(&acc.rhs);

        let normal_instance = [AssignedMsm::as_public_input(&acc.lhs), rhs_normal_pi]
            .into_iter()
            .flatten()
            .collect();

        (normal_instance, rhs_committed_pi)
    }
}

impl<E: InCircuitKZGEngine> AssignedAccumulator<E> {
    /// An `AssignedAccumulator` a given lhs and rhs terms respectively.
    pub fn new(lhs: AssignedMsm<E>, rhs: AssignedMsm<E>) -> Self {
        Self { lhs, rhs }
    }

    /// Witnesses the "collapsed" form of a KZG accumulator.
    ///
    /// The expected shape is, as [`AssignedMsm::assign_collapsed`] assigns:
    /// * LHS: exactly one `Variable` entry labeled `NoLabel`.
    /// * RHS: one `Fixed` entry per label in `fixed_base_labels` plus one
    ///   `Variable` entry labeled `NoLabel`.
    ///
    /// This shape matches the invariant maintained by the KZG multiopen
    /// accumulation after `collapse()` has been called off-circuit.
    ///
    /// # Errors
    ///
    /// If the expected shape is not satisfied.
    pub fn assign_collapsed(
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
        fixed_base_labels: &[PolynomialLabel],
        value: Value<Accumulator<E>>,
    ) -> Result<Self, Error> {
        let (lhs, rhs) = value.map(|acc| (acc.lhs, acc.rhs)).unzip();
        Ok(Self::new(
            AssignedMsm::assign_collapsed(layouter, curve_chip, scalar_chip, &[], lhs)?,
            AssignedMsm::assign_collapsed(
                layouter,
                curve_chip,
                scalar_chip,
                fixed_base_labels,
                rhs,
            )?,
        ))
    }

    /// The in-circuit counterpart of [`Instantiable::as_public_input`].
    pub fn in_circuit_as_public_input(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
    ) -> Result<Vec<AssignedNative<E::Fr>>, Error> {
        Ok([
            self.lhs.in_circuit_as_public_input(layouter, curve_chip)?,
            self.rhs.in_circuit_as_public_input(layouter, curve_chip)?,
        ]
        .concat())
    }

    /// Constrains this accumulator as a public input.
    pub fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
    ) -> Result<(), Error> {
        self.lhs.constrain_as_public_input(layouter, curve_chip, scalar_chip)?;
        self.rhs.constrain_as_public_input(layouter, curve_chip, scalar_chip)
    }

    /// Constrains this accumulator as a public input. The (fixed and
    /// non-fixed) scalars of its RHS are constrained in committed form (as a
    /// committed instance), whereas the rest of the accumulator is constrained
    /// as a normal instance.
    ///
    /// See [AssignedAccumulator::as_public_input_with_committed_scalars] for
    /// the off-circuit analog of this function.
    pub fn constrain_as_public_input_with_committed_scalars(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
    ) -> Result<(), Error> {
        self.lhs.constrain_as_public_input(layouter, curve_chip, scalar_chip)?;
        self.rhs
            .constrain_as_public_input_with_committed_scalars(layouter, curve_chip, scalar_chip)
    }

    /// Scales the given acc by the given assigned bit.
    ///
    /// This function mutates self.
    pub fn scale_by_bit(
        layouter: &mut impl Layouter<E::Fr>,
        scalar_chip: &ScalarChip<E::Fr>,
        cond: &AssignedBit<E::Fr>,
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
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
    ) -> Result<(), Error> {
        self.lhs.collapse(layouter, curve_chip, scalar_chip, PolynomialLabel::NoLabel)?;
        self.rhs.collapse(layouter, curve_chip, scalar_chip, PolynomialLabel::NoLabel)
    }

    /// Whether both sides are collapsed and fixed-base-resolved; see
    /// [`AssignedMsm::is_collapsed`].
    pub fn is_collapsed(&self) -> bool {
        self.lhs.is_collapsed() && self.rhs.is_collapsed()
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
    pub fn resolve_fixed_bases(&mut self, fixed_bases: &BTreeMap<PolynomialLabel, AssignedG1<E>>) {
        self.lhs.resolve_fixed_bases(fixed_bases);
        self.rhs.resolve_fixed_bases(fixed_bases);
    }

    /// Accumulates several accumulators together. The resulting acc will
    /// satisfy the invariant iff all the accumulators individually do.
    pub fn accumulate(
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
        hash_chip: &impl HashInstructions<E::Fr, AssignedNative<E::Fr>, AssignedNative<E::Fr>>,
        accs: &[Self],
    ) -> Result<Self, Error> {
        let hash_input = accs
            .iter()
            .map(|acc| acc.in_circuit_as_public_input(layouter, curve_chip))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let r = hash_chip.hash(layouter, &hash_input)?;
        let rs = truncated_powers::<E::Fr>(layouter, scalar_chip, &r, accs.len())?;

        let mut acc = accs[0].clone();
        for (other, ri) in accs.iter().zip(rs).skip(1) {
            acc.lhs = acc.lhs.accumulate_with_r(layouter, scalar_chip, &other.lhs, &ri)?;
            acc.rhs = acc.rhs.accumulate_with_r(layouter, scalar_chip, &other.rhs, &ri)?;
        }

        Ok(acc)
    }
}

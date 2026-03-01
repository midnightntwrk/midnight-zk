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
use group::prime::PrimeCurveAffine;
use midnight_curves::pairing::Engine;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{kzg::msm::DualMSM, CommitmentLabel},
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
        fixed_commitment_name,
        msm::{AssignedMsm, Msm},
        perm_commitment_name,
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
    /// Converts the off-circuit dual MSM into an `Accumulator<S>` by separating
    /// the fixed-base scalars aside in a BTreeMap indexed by the base name with
    /// a custom prefix.
    ///
    /// This function also takes a map of fixed bases indexed by their name,
    /// which is used to perform a sanity check on the fixed-base scalars of the
    /// dual MSM.
    pub fn from_dual_msm(
        dual_msm: DualMSM<S::Engine>,
        prefix: &str,
        fixed_bases: &BTreeMap<String, S::C>,
    ) -> Self {
        let (lhs, rhs) = dual_msm.split();

        let process_msm = |msm: Vec<(&CommitmentLabel, &S::F, &S::C)>| {
            let mut bases = Vec::with_capacity(msm.len());
            let mut scalars = Vec::with_capacity(msm.len());
            let mut fixed_base_scalars = BTreeMap::new();
            for (label, scalar, base) in msm {
                match label {
                    CommitmentLabel::Fixed(i) => {
                        let name = fixed_commitment_name(prefix, *i);
                        assert_eq!(fixed_bases.get(&name), Some(base));
                        fixed_base_scalars.insert(name, *scalar);
                    }
                    CommitmentLabel::Permutation(i) => {
                        let name = perm_commitment_name(prefix, *i);
                        assert_eq!(fixed_bases.get(&name), Some(base));
                        fixed_base_scalars.insert(name, *scalar);
                    }
                    CommitmentLabel::Custom(s) if s == "-G" => {
                        assert_eq!(fixed_bases.get(s), Some(base));
                        fixed_base_scalars.insert("-G".into(), *scalar);
                    }
                    _ => {
                        bases.push(*base);
                        scalars.push(*scalar);
                    }
                }
            }
            (bases, scalars, fixed_base_scalars)
        };

        let (lhs_bases, lhs_scalars, lhs_fixed_base_scalars) = process_msm(lhs);
        let (rhs_bases, rhs_scalars, rhs_fixed_base_scalars) = process_msm(rhs);

        Accumulator {
            lhs: Msm::new(&lhs_bases, &lhs_scalars, &lhs_fixed_base_scalars),
            rhs: Msm::new(&rhs_bases, &rhs_scalars, &rhs_fixed_base_scalars),
        }
    }

    /// Checks whether the accumulator, when evaluated with the provided
    /// fixed-bases, satisfies the invariant w.r.t. the given \[τ\]₂.
    pub fn check(&self, tau_in_g2: &S::G2Affine, fixed_bases: &BTreeMap<String, S::C>) -> bool {
        // TODO: Share the Miller-loop?
        let lhs = self.lhs.eval(fixed_bases).into();
        let rhs = self.rhs.eval(fixed_bases).into();
        S::Engine::pairing(&lhs, tau_in_g2) == S::Engine::pairing(&rhs, &S::G2Affine::generator())
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

    /// Evaluates the variable part of the Accumulator collapsing each
    /// side to a single point (and a scalar of 1), leaving the fixed-base part
    /// of both sides intact.
    ///
    /// This function mutates self.
    pub fn collapse(&mut self) {
        self.lhs.collapse();
        self.rhs.collapse();
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
}

impl<S: SelfEmulation> AssignedAccumulator<S> {
    /// Converts the off-circuit accumulator into two vectors of scalars. The
    /// first will be used as a normal instance, whereas the second will be
    /// plugged-in in as a committed instance.
    ///
    /// The committed instance part corresponds to the MSM (fixed and non-fixed)
    /// scalars of the accumulator RHS.
    pub fn as_public_input_with_committed_scalars(acc: &Accumulator<S>) -> (Vec<S::F>, Vec<S::F>) {
        let (rhs_scalars, rhs_committed_scalars) =
            AssignedMsm::as_public_input_with_committed_scalars(&acc.rhs);

        let normal_instance = [AssignedMsm::as_public_input(&acc.lhs), rhs_scalars]
            .into_iter()
            .flatten()
            .collect();

        (normal_instance, rhs_committed_scalars)
    }
}

impl<S: SelfEmulation> AssignedAccumulator<S> {
    /// Witnesses an accumulator of `lhs_len` bases/scalars and a `BTreeMap` of
    /// fixed_base_scalars indexed by the given `lhs_fixed_base_names`.
    ///
    /// Similar arguments determine the size and shape of the accumulator
    /// right-hand side.
    #[allow(clippy::too_many_arguments)]
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        lhs_len: usize,
        rhs_len: usize,
        lhs_fixed_base_names: &[String],
        rhs_fixed_base_names: &[String],
        acc_val: Value<Accumulator<S>>,
    ) -> Result<Self, Error> {
        let (acc_lhs_val, acc_rhs_val) = acc_val.map(|acc| (acc.lhs, acc.rhs)).unzip();
        Ok(AssignedAccumulator::new(
            AssignedMsm::<S>::assign(
                layouter,
                curve_chip,
                scalar_chip,
                lhs_len,
                lhs_fixed_base_names,
                acc_lhs_val,
            )?,
            AssignedMsm::<S>::assign(
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
        self.lhs.collapse(layouter, curve_chip, scalar_chip)?;
        self.rhs.collapse(layouter, curve_chip, scalar_chip)
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

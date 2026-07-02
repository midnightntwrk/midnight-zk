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

//! In-circuit KZG-based PLONK verifier.

use std::collections::BTreeMap;

use group::Group;
use midnight_proofs::{
    circuit::Value,
    plonk::{self, ConstraintSystem},
    poly::{kzg::KZGCommitmentScheme, PolynomialLabel},
};

use crate::{
    field::AssignedNative,
    types::{InnerValue, Instantiable},
};

mod accumulator;
mod expressions;
mod kzg;
mod lookup;
mod msm;
mod permutation;
mod traces;
mod transcript_gadget;
mod trash;
mod types;
mod utils;
mod verifier_gadget;

pub use accumulator::{Accumulator, AssignedAccumulator};
pub use kzg::AssignedKZGCommitment;
pub use msm::{AssignedMsm, AssignedPoint, Msm, Point};
#[cfg(feature = "dev-curves")]
pub use types::BnEmulation;
pub use types::{BlstrsEmulation, SelfEmulation};
pub use verifier_gadget::VerifierGadget;

type VerifyingKey<S> =
    plonk::VerifyingKey<<S as SelfEmulation>::F, KZGCommitmentScheme<<S as SelfEmulation>::Engine>>;

/// Type for in-circuit Evaluation Domain.
///
/// This type carries only the information needed for the verifier, `k`
/// and `omega`, and values `omega^{-1}` and `n = 2^k`, computed in-circuit.
///
/// The only entry points are via the assignment functions of Verifying Keys.
#[derive(Clone, Debug)]
struct AssignedEvaluationDomain<S: SelfEmulation> {
    k: AssignedNative<S::F>,
    omega: AssignedNative<S::F>,
    omega_inv: AssignedNative<S::F>,
    n: AssignedNative<S::F>,
}

/// Type for in-circuit verifying keys.
///
/// This type carries off-circuit the information about the constraint system.
/// The in-circuit fields are the transcript representation, the fixed
/// commitments, permutation commitments, and the evaluation domain.
///
/// The only entry-point for this function is intended to be
/// [VerifierGadget::assign_vk_as_public_input]. This is possible because fixed
/// commitments are dealt with off-circuit, i.e., the resulting accumulator of
/// [VerifierGadget::prepare] contains the scalars of the
/// fixed-commitments, in the `fixed_base_scalars` field (of its RHS).
#[derive(Clone, Debug)]
pub struct AssignedVk<S: SelfEmulation> {
    domain: AssignedEvaluationDomain<S>,
    fixed_commitments: Vec<AssignedKZGCommitment<S>>,
    perm_commitments: Vec<AssignedKZGCommitment<S>>,
    cs: ConstraintSystem<S::F>,
    cs_degree: usize,
    transcript_repr: AssignedNative<S::F>,
}

impl<S: SelfEmulation> InnerValue for AssignedVk<S> {
    type Element = VerifyingKey<S>;

    fn value(&self) -> Value<VerifyingKey<S>> {
        unimplemented!(
            "It is not possible to get a full verifying key out of an
             AssignedVk, as the latter does not include fixed commitments."
        )
    }
}

impl<S: SelfEmulation> Instantiable<S::F> for AssignedVk<S> {
    fn as_public_input(vk: &VerifyingKey<S>) -> Vec<S::F> {
        let domain = vk.get_domain();
        [
            AssignedNative::<S::F>::as_public_input(&vk.transcript_repr()),
            AssignedNative::<S::F>::as_public_input(&S::F::from(domain.k() as u64)),
            AssignedNative::<S::F>::as_public_input(&domain.get_omega()),
        ]
        .concat()
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[S::F]) -> Option<VerifyingKey<S>> {
        unimplemented!("as_public_input encodes the VK as its transcript_repr() — not invertible")
    }
}

impl<S: SelfEmulation> AssignedVk<S> {
    /// The assigned `transcript_repr` cell of this verifying key.
    pub fn transcript_repr(&self) -> &AssignedNative<S::F> {
        &self.transcript_repr
    }

    /// The assigned `k` cell.
    pub fn k(&self) -> &AssignedNative<S::F> {
        &self.domain.k
    }

    /// The assigned `omega` cell.
    pub fn omega(&self) -> &AssignedNative<S::F> {
        &self.domain.omega
    }
}

/// Builds the map from [`PolynomialLabel`] to curve point for all
/// circuit-constant bases of a verifying key.
///
/// The map contains:
/// * `Fixed(i)`: the i-th fixed-column commitment,
/// * `PermutationFixed(i)`: the i-th permutation commitment,
/// * `Custom("-G")`: the negated designated generator used in the KZG opening
///   proof.
///
/// Pass this map to [`Accumulator::check`] or [`Msm::eval`].
pub fn fixed_bases<S: SelfEmulation>(vk: &VerifyingKey<S>) -> BTreeMap<PolynomialLabel, S::C> {
    let mut fixed_bases = BTreeMap::new();

    let fixed_commitments = vk.fixed_commitments();
    let perm_commitments = vk.permutation().commitments();

    for (i, com) in fixed_commitments.iter().enumerate() {
        fixed_bases.insert(PolynomialLabel::Fixed(i), *com.as_point());
    }

    for (i, com) in perm_commitments.iter().enumerate() {
        fixed_bases.insert(PolynomialLabel::PermutationFixed(i), *com.as_point());
    }

    fixed_bases.insert(PolynomialLabel::Custom("-G".into()), -S::C::generator());

    fixed_bases
}

/// Returns the ordered list of [`PolynomialLabel`]s for the fixed bases of a
/// circuit with the given number of fixed and permutation commitments.
///
/// The order matches [`fixed_bases`]: fixed columns first, then permutation
/// columns, then `Custom("-G")`. Call this before having an actual verifying
/// key (e.g. during setup) to size an accumulator correctly.
pub fn fixed_base_labels<S: SelfEmulation>(
    nb_fixed_commitments: usize,
    nb_perm_commitments: usize,
) -> Vec<PolynomialLabel> {
    let mut labels = Vec::with_capacity(nb_fixed_commitments + nb_perm_commitments + 1);

    for i in 0..nb_fixed_commitments {
        labels.push(PolynomialLabel::Fixed(i));
    }

    for i in 0..nb_perm_commitments {
        labels.push(PolynomialLabel::PermutationFixed(i));
    }

    // This term will be introduced by the KZG multiopen argument as a fixed base.
    // It corresponds to the negated designated generator. It is not proper of the
    // verifying key, but there is no harm in having it here (it needs to be
    // introduced at some point anyway and this is a good place).
    labels.push(PolynomialLabel::Custom("-G".into()));

    labels
}

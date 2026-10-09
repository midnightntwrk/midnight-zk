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
    plonk,
    plonk::ConstraintSystem,
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
};

use crate::{
    field::AssignedNative,
    types::{InnerValue, Instantiable},
};

mod absorbed_vk;
mod accumulator;
mod argument;
mod expressions;
mod fflonk;
mod kzg;
mod msm;
pub(crate) mod pcs;
mod traces;
mod transcript_gadget;
mod types;
mod utils;
mod verifier_gadget;

pub use accumulator::{Accumulator, AssignedAccumulator};
pub use fflonk::InCircuitFflonk;
pub use kzg::{AssignedKZGCommitment, AssignedKZGMultiCommitment, InCircuitKZG};
pub use msm::{AssignedMsm, AssignedPoint, Msm, Point};
pub use pcs::{
    CommitmentBases, InCircuitCounterpart, InCircuitHomomorphicCommitment, InCircuitPCS,
};
#[cfg(feature = "dev-curves")]
pub use types::BnEmulation;
pub use types::{BlstrsEmulation, SelfEmulation};
pub use verifier_gadget::VerifierGadget;

/// The off-circuit verifying key that a given in-circuit PCS accepts.
type VerifyingKey<S, PCS> =
    plonk::VerifyingKey<<S as SelfEmulation>::F, <PCS as InCircuitPCS<S>>::OffCircuit>;

/// Type for in-circuit Evaluation Domain.
///
/// This type carries only the information needed for the verifier, `k`
/// and `omega`, and values `omega^{-1}` and `n = 2^k`, computed in-circuit.
///
/// The only entry points are the assignment functions of Verifying Keys.
#[derive(Clone, Debug)]
struct AssignedEvaluationDomain<S: SelfEmulation> {
    k: AssignedNative<S::F>,
    omega: AssignedNative<S::F>,
    omega_inv: AssignedNative<S::F>,
    n: AssignedNative<S::F>,
}

/// Type for in-circuit verifying keys.
///
/// Only the transcript representation and the evaluation domain are assigned
/// in-circuit; the constraint system is kept off-circuit.
///
/// The fixed and permutation commitments are not assigned either: they are
/// placeholders (the `Fixed` variant of [AssignedKZGCommitment]) that only
/// carry their label. The verifier only uses them as MSM bases, so
/// [VerifierGadget::prepare] records their scalars in the accumulator, and
/// the decider supplies the actual points off-circuit, via
/// [Accumulator::resolve_fixed_bases]. They are still bound to the proof, as
/// `transcript_repr` commits to them.
///
/// The only entry points are [VerifierGadget::assign_vk_as_public_input] and
/// [VerifierGadget::assign_fixed_vk].
#[derive(Clone, Debug)]
pub struct AssignedVk<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    domain: AssignedEvaluationDomain<S>,
    phase0_commitment: PCS::AssignedCommitment,
    cs: ConstraintSystem<S::F>,
    cs_degree: usize,
    transcript_repr: AssignedNative<S::F>,
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> InnerValue for AssignedVk<S, PCS> {
    type Element = VerifyingKey<S, PCS>;

    fn value(&self) -> Value<VerifyingKey<S, PCS>> {
        unimplemented!(
            "It is not possible to get a full verifying key out of an
             AssignedVk, as the latter does not include fixed commitments."
        )
    }
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> Instantiable<S::F> for AssignedVk<S, PCS> {
    fn as_public_input(vk: &VerifyingKey<S, PCS>) -> Vec<S::F> {
        let domain = vk.get_domain();
        [
            AssignedNative::<S::F>::as_public_input(&vk.transcript_repr()),
            AssignedNative::<S::F>::as_public_input(&S::F::from(domain.k() as u64)),
            AssignedNative::<S::F>::as_public_input(&domain.get_omega()),
        ]
        .concat()
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[S::F]) -> Option<VerifyingKey<S, PCS>> {
        unimplemented!("as_public_input encodes the VK as its transcript_repr() — not invertible")
    }
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> AssignedVk<S, PCS> {
    /// The assigned `transcript_repr` of this verifying key.
    pub fn transcript_repr(&self) -> &AssignedNative<S::F> {
        &self.transcript_repr
    }

    /// The assigned `k`.
    pub fn k(&self) -> &AssignedNative<S::F> {
        &self.domain.k
    }

    /// The assigned `omega`.
    pub fn omega(&self) -> &AssignedNative<S::F> {
        &self.domain.omega
    }
}

/// Builds the map from [`PolynomialLabel`] to curve point for all
/// circuit-constant bases of a verifying key.
///
/// The map contains:
/// * the bases of the phase-0 commitment, under the labels it carries (e.g.
///   `Fixed(i)`, `PermutationFixed(i)`),
/// * `Custom("-G")`: the negated designated generator used in the KZG opening
///   proof.
///
/// Pass this map to [`Accumulator::check`] or [`Msm::eval`].
pub fn fixed_bases<S, CS>(vk: &plonk::VerifyingKey<S::F, CS>) -> BTreeMap<PolynomialLabel, S::C>
where
    S: SelfEmulation,
    CS: PolynomialCommitmentScheme<S::F>,
    CS::Commitment: CommitmentBases<S::C>,
{
    let mut fixed_bases: BTreeMap<_, _> = vk.phase0_commitment().bases().into_iter().collect();

    fixed_bases.insert(PolynomialLabel::Custom("-G".into()), -S::C::generator());

    fixed_bases
}

/// Returns the ordered list of [`PolynomialLabel`]s for the fixed bases of a
/// circuit with constraint system `cs`, committed with `CS`.
///
/// The order matches the keys of [`fixed_bases`]. Call this before having an
/// actual verifying key (e.g. during setup) to size an accumulator correctly.
pub fn fixed_base_labels<S, CS>(cs: &ConstraintSystem<S::F>) -> Vec<PolynomialLabel>
where
    S: SelfEmulation,
    CS: PolynomialCommitmentScheme<S::F>,
    CS::Commitment: CommitmentBases<S::C>,
{
    let mut labels: Vec<_> = (CS::commitment_to_zero(&cs.fixed_polys_labels()).bases())
        .into_iter()
        .map(|(label, _)| label)
        // This term will be introduced by the KZG multiopen argument as a fixed
        // base. It corresponds to the negated designated generator. It is not
        // proper of the verifying key, but there is no harm in having it here (it
        // needs to be introduced at some point anyway and this is a good place).
        .chain(std::iter::once(PolynomialLabel::Custom("-G".into())))
        .collect();
    labels.sort();

    labels
}

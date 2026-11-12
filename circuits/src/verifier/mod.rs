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
use midnight_curves::pairing::MultiMillerLoop;
use midnight_proofs::{
    circuit::Value,
    plonk,
    plonk::{ConstraintSystem, VerifyingKey},
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
};

use crate::{
    CircuitField,
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
pub use kzg::{AssignedKZGCommitment, AssignedKZGMultiCommitment, InCircuitKZGEngine};
pub use msm::{AssignedMsm, AssignedPoint, Msm, Point};
pub use pcs::{AssignedCommitment, CommitmentBases, InCircuitPCS};
pub use transcript_gadget::{InCircuitHashable, InCircuitTranscript, PoseidonTranscriptGadget};
pub use types::{AssignedG1, CurveChip, ScalarChip};
pub use verifier_gadget::{UnboundVk, VerifierGadget, vk_hash};

/// Type for in-circuit Evaluation Domain.
///
/// This type carries only the information needed for the verifier, `k`
/// and `omega`, and values `omega^{-1}` and `n = 2^k`, computed in-circuit.
///
/// The only entry points are the assignment functions of Verifying Keys.
#[derive(Clone, Debug)]
struct AssignedEvaluationDomain<F: CircuitField> {
    k: AssignedNative<F>,
    omega: AssignedNative<F>,
    omega_inv: AssignedNative<F>,
    n: AssignedNative<F>,
}

/// Type for in-circuit verifying keys.
///
/// The transcript representation and the evaluation domain are assigned
/// in-circuit (as are the commitments, for keys obtained from an [UnboundVk]);
/// the constraint system is kept off-circuit.
///
/// The fixed and permutation commitments are either:
///  - placeholders (the `Fixed` variant of [AssignedKZGCommitment]) that only
///    carry their label, for keys assigned with
///    [VerifierGadget::assign_vk_as_public_input] or
///    [VerifierGadget::assign_fixed_vk]. The verifier only uses them as MSM
///    bases, so [VerifierGadget::prepare] records their scalars in the
///    accumulator, and the decider supplies the actual points off-circuit, via
///    [Accumulator::resolve_fixed_bases]. They are still bound to the proof, as
///    `transcript_repr` commits to them.
///  - witnessed points, for keys obtained from an [UnboundVk]. They are bound
///    by the hash the key is bound to.
///
/// The only entry points are [VerifierGadget::assign_vk_as_public_input],
/// [VerifierGadget::assign_fixed_vk] and [VerifierGadget::bind_vk_to_hash].
///
/// This type does not guarantee that its values are consistent with each
/// other (e.g. that `omega` is a primitive `2^k`-th root of unity, or that they
/// match the key `transcript_repr` commits to). For keys obtained through
/// [VerifierGadget::bind_vk_to_hash] this is enforced by the hash constraint;
/// for the other entry points it is the caller's responsibility.
#[derive(Clone, Debug)]
pub struct AssignedVk<F: CircuitField, PCS: InCircuitPCS<F>> {
    domain: AssignedEvaluationDomain<F>,
    phase0_commitment: AssignedCommitment<F, PCS>,
    cs: ConstraintSystem<F>,
    cs_degree: usize,
    transcript_repr: AssignedNative<F>,
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> InnerValue for AssignedVk<F, PCS> {
    type Element = VerifyingKey<F, PCS>;

    fn value(&self) -> Value<VerifyingKey<F, PCS>> {
        unimplemented!(
            "It is not possible to get a full verifying key out of an
             AssignedVk, as the latter does not include fixed commitments."
        )
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> Instantiable<F> for AssignedVk<F, PCS> {
    fn as_public_input(vk: &VerifyingKey<F, PCS>) -> Vec<F> {
        let domain = vk.get_domain();
        [
            AssignedNative::<F>::as_public_input(&vk.transcript_repr()),
            AssignedNative::<F>::as_public_input(&F::from(domain.k() as u64)),
            AssignedNative::<F>::as_public_input(&domain.get_omega()),
        ]
        .concat()
    }

    /// Always returns `None`: [Self::as_public_input] encodes the verifying key
    /// as its `transcript_repr()`, which is not invertible.
    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[F]) -> Option<VerifyingKey<F, PCS>> {
        None
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> AssignedVk<F, PCS> {
    /// The assigned `transcript_repr` of this verifying key.
    pub fn transcript_repr(&self) -> &AssignedNative<F> {
        &self.transcript_repr
    }

    /// The assigned `k`.
    pub fn k(&self) -> &AssignedNative<F> {
        &self.domain.k
    }

    /// The assigned `omega`.
    pub fn omega(&self) -> &AssignedNative<F> {
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
pub fn fixed_bases<E, PCS>(vk: &plonk::VerifyingKey<E::Fr, PCS>) -> BTreeMap<PolynomialLabel, E::G1>
where
    E: MultiMillerLoop,
    PCS: PolynomialCommitmentScheme<E::Fr, Commitment: CommitmentBases<E::G1>>,
{
    let mut fixed_bases: BTreeMap<_, _> = vk.phase0_commitment().bases().into_iter().collect();

    fixed_bases.insert(PolynomialLabel::Custom("-G".into()), -E::G1::generator());

    fixed_bases
}

/// Returns the ordered list of [`PolynomialLabel`]s for the fixed bases of a
/// circuit with the given constraint system.
///
/// The labels are sorted, matching the key order of [`fixed_bases`]. Call this
/// before having an actual verifying key (e.g. during setup) to size an
/// accumulator correctly.
pub fn fixed_base_labels<F: CircuitField, PCS: InCircuitPCS<F>>(
    cs: &ConstraintSystem<F>,
) -> Vec<PolynomialLabel> {
    let mut labels = PCS::fixed_base_labels(&cs.fixed_polys_labels());

    // This term will be introduced by the KZG multiopen argument as a fixed base.
    // It corresponds to the negated designated generator. It is not proper of the
    // verifying key, but there is no harm in having it here (it needs to be
    // introduced at some point anyway and this is a good place).
    labels.push(PolynomialLabel::Custom("-G".into()));

    labels.sort();
    labels
}

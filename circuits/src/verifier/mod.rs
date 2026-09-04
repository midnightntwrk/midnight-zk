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
    pcs::PolynomialCommitmentScheme,
    plonk,
    plonk::ConstraintSystem,
    poly::{EvaluationDomain, PolynomialLabel},
};

use crate::{
    field::AssignedNative,
    types::{InnerValue, Instantiable},
};

mod accumulator;
mod expressions;
mod fflonk;
mod kzg;
mod lookup;
mod msm;
mod multi_open;
pub(crate) mod pcs;
mod permutation;
mod traces;
mod transcript_gadget;
mod trash;
mod types;
mod utils;
mod verifier_gadget;

pub use accumulator::{Accumulator, AssignedAccumulator};
pub use fflonk::{AssignedFflonkCommitment, InCircuitFflonk};
pub use kzg::{AssignedKZGCommitment, AssignedKZGMultiCommitment, InCircuitKZG};
pub use msm::{AssignedMsm, AssignedPoint, Msm, Point};
pub use pcs::{InCircuitHomomorphicCommitment, InCircuitPCS};
#[cfg(feature = "dev-curves")]
pub use types::BnEmulation;
pub use types::{BlstrsEmulation, SelfEmulation};
pub use verifier_gadget::VerifierGadget;

/// The in-circuit gadget that verifies proofs of the off-circuit scheme `Self`.
///
/// Exists so that a single definition — [`midnight_proofs::MidnightPCS`] —
/// fixes both halves of the protocol. Without it the two would be named
/// independently and could silently drift apart.
pub trait InCircuitCounterpart<S: SelfEmulation>: PolynomialCommitmentScheme<S::F> {
    /// The gadget verifying this scheme's proofs.
    type InCircuit: InCircuitPCS<S, OffCircuit = Self>;
}

impl<S: SelfEmulation> InCircuitCounterpart<S>
    for midnight_proofs::pcs::kzg::KZGCommitmentScheme<S::Engine>
{
    type InCircuit = InCircuitKZG<S>;
}

impl<S: SelfEmulation> InCircuitCounterpart<S>
    for midnight_proofs::pcs::fflonk::FflonkScheme<S::Engine>
{
    type InCircuit = InCircuitFflonk<S>;
}

/// The in-circuit counterpart of [`midnight_proofs::MidnightPCS`]: the scheme
/// the verifier gadget is instantiated at throughout this workspace.
///
/// Derived from `MidnightPCS`, so switching the protocol's commitment scheme is
/// the single edit of that alias; this one follows.
pub type MidnightInCircuitPCS<S> =
    <midnight_proofs::MidnightPCS<<S as SelfEmulation>::Engine> as InCircuitCounterpart<S>>::InCircuit;

/// The in-circuit commitment type of [`MidnightInCircuitPCS`], the analog of
/// [`midnight_proofs::MidnightCommitment`].
pub type MidnightAssignedCommitment<S> =
    <MidnightInCircuitPCS<S> as InCircuitPCS<S>>::AssignedCommitment;

/// The off-circuit verifying key that a given in-circuit PCS accepts.
type VerifyingKey<S, PCS> =
    plonk::VerifyingKey<<S as SelfEmulation>::F, <PCS as InCircuitPCS<S>>::OffCircuit>;

/// Type for in-circuit verifying keys.
///
/// This type carries off-circuit a lot of the information about the vk.
/// The only in-circuit field is the `transcript_repr`.
///
/// The only entry-point for this function is intended to be
/// [VerifierGadget::assign_vk_as_public_input]. This is possible because fixed
/// commitments are dealt with off-circuit, i.e., the resulting accumulator of
/// [VerifierGadget::prepare] contains the scalars of the
/// fixed-commitments, in the `fixed_base_scalars` field (of its RHS).
#[derive(Clone, Debug)]
pub struct AssignedVk<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    domain: EvaluationDomain<S::F>,
    fixed_commitments: Vec<PCS::AssignedCommitment>,
    perm_commitments: Vec<PCS::AssignedCommitment>,
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
        AssignedNative::<S::F>::as_public_input(&vk.transcript_repr())
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(_fields: &[S::F]) -> Option<VerifyingKey<S, PCS>> {
        unimplemented!("as_public_input encodes the VK as its transcript_repr() — not invertible")
    }
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> AssignedVk<S, PCS> {
    /// The assigned `transcript_repr` cell of this verifying key.
    pub fn transcript_repr(&self) -> &AssignedNative<S::F> {
        &self.transcript_repr
    }
}

/// An off-circuit commitment to a single polynomial, as a verifying key holds
/// them.
///
/// Every commitment a verifying key carries is to one polynomial: the families
/// a scheme may bundle are all witnessed, never fixed.
pub trait SingletonCommitment<C> {
    /// The curve point of this commitment.
    ///
    /// # Panics
    ///
    /// If the commitment does not hold exactly one polynomial.
    fn point(&self) -> C;
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
pub fn fixed_bases<S: SelfEmulation, CS>(
    vk: &plonk::VerifyingKey<S::F, CS>,
) -> BTreeMap<PolynomialLabel, S::C>
where
    CS: PolynomialCommitmentScheme<S::F>,
    CS::Commitment: SingletonCommitment<S::C>,
{
    let mut fixed_bases = BTreeMap::new();

    let fixed_commitments = vk.fixed_commitments();
    let perm_commitments = vk.permutation().commitments();

    for (i, com) in fixed_commitments.iter().enumerate() {
        fixed_bases.insert(PolynomialLabel::Fixed(i), com.point());
    }

    for (i, com) in perm_commitments.iter().enumerate() {
        fixed_bases.insert(PolynomialLabel::PermutationFixed(i), com.point());
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

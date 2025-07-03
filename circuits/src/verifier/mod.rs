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

//! In-circuit KZG-based PLONK verifier.

use std::collections::BTreeMap;

use group::Group;
use midnight_proofs::{
    circuit::Value,
    plonk,
    plonk::ConstraintSystem,
    poly::{kzg::KZGCommitmentScheme, EvaluationDomain},
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
mod transcript_gadget;
mod types;
mod utils;
mod vanishing;
mod verifier_gadget;

pub use accumulator::{Accumulator, AssignedAccumulator};
pub use msm::Msm;
pub use types::{BlstrsEmulation, SelfEmulation};
pub use verifier_gadget::VerifierGadget;

type VerifyingKey<S> =
    plonk::VerifyingKey<<S as SelfEmulation>::F, KZGCommitmentScheme<<S as SelfEmulation>::Engine>>;

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
pub struct AssignedVk<S: SelfEmulation> {
    vk_name: String,
    domain: EvaluationDomain<S::F>,
    cs: ConstraintSystem<S::F>,
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
        AssignedNative::<S::F>::as_public_input(&vk.transcript_repr())
    }
}

/// Canonical name for the i-th verifying-key commitment.
// We prefix commitment names with `~` for two reasons:
// 1. It prevents collisions with other ad hoc names (e.g. for input
//    commitments).
// 2. It helps our very limited subroutine `extract_fixed_bases` for extracting
//    the fixed bases from a dual_msm (produced by halo2_proofs::prepare). If
//    two bases (with different names) are equal, this subroutine will extract
//    them from the dual_msm in alphabetical order on their name. This requires
//    that the committed instances have a name that goes before the one of any
//    fixed instance, since the halo2 queries for committed instances go first.
//    Prefixing with `~` will make sure that fixed and perm commitment names go
//    after any ad hoc commitment name the user may choose (if they do not use
//    this symbol).
fn commitment_name(prefix: String, nb_commitments: usize, i: usize) -> String {
    let nb_digits = utils::num_digits(nb_commitments - 1);
    format!("~{prefix}_{:0>nb_digits$}", i)
}

/// Canonical name for the i-th verifying-key fixed commitment.
fn fixed_commitment_name(prefix: &str, nb_fixed_commitments: usize, i: usize) -> String {
    commitment_name(String::from(prefix) + "_fixed_com", nb_fixed_commitments, i)
}

/// Canonical name for the i-th verifying-key permutation commitment.
fn perm_commitment_name(prefix: &str, nb_perm_commitments: usize, i: usize) -> String {
    commitment_name(String::from(prefix) + "_perm_com", nb_perm_commitments, i)
}

impl<S: SelfEmulation> AssignedVk<S> {
    /// Canonical name for the i-th fixed commitment of this AssignedVk.
    fn fixed_commitment_name(&self, i: usize) -> String {
        let nb_fixed_commitments = self.cs.num_fixed_columns() + self.cs.num_selectors();
        fixed_commitment_name(&self.vk_name, nb_fixed_commitments, i)
    }

    /// Canonical name for the i-th perm commitment of this AssignedVk.
    fn perm_commitment_name(&self, i: usize) -> String {
        let nb_perm_commitments = self.cs.permutation().columns.len();
        perm_commitment_name(&self.vk_name, nb_perm_commitments, i)
    }
}

/// Extracts the fixed bases from the verifying key, indexed by their
/// canonical name.
pub fn fixed_bases<S: SelfEmulation>(
    vk_name: &str,
    vk: &VerifyingKey<S>,
) -> BTreeMap<String, S::C> {
    let mut fixed_bases = BTreeMap::new();

    fixed_bases.insert(String::from("~G"), -S::C::generator());

    let fixed_commitments = vk.fixed_commitments();
    let perm_commitments = vk.permutation().commitments();

    for (i, com) in fixed_commitments.iter().enumerate() {
        fixed_bases.insert(
            fixed_commitment_name(vk_name, fixed_commitments.len(), i),
            *com,
        );
    }

    for (i, com) in perm_commitments.iter().enumerate() {
        fixed_bases.insert(
            perm_commitment_name(vk_name, perm_commitments.len(), i),
            *com,
        );
    }

    fixed_bases
}

/// The names of the fixed bases of a verifying key. This function is designed
/// to be called before having an actual verifying key. Only the number of fixed
/// and permutation commitments is necessary, not their actual values.
pub fn fixed_base_names<S: SelfEmulation>(
    vk_name: &str,
    nb_fixed_commitments: usize,
    nb_perm_commitments: usize,
) -> Vec<String> {
    let mut names = Vec::with_capacity(nb_fixed_commitments + nb_perm_commitments + 1);

    // This term will be introduced by the KZG multiopen argument as a fixed base.
    // It corresponds to the negated designated generator. It is not proper of the
    // verifying key, but there is no harm in having it here (it needs to be
    // introduced at some point anyway and this is a good place).
    names.push("~G".into());

    for i in 0..nb_fixed_commitments {
        names.push(fixed_commitment_name(vk_name, nb_fixed_commitments, i));
    }

    for i in 0..nb_perm_commitments {
        names.push(perm_commitment_name(vk_name, nb_perm_commitments, i));
    }

    names
}

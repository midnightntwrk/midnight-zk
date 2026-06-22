//! VK hashing utilities for multi-circuit proof aggregation.
//!
//! Because different inner circuits differ in their verifying keys (fixed and
//! permutation commitments), the aggregator must bind each accumulated proof to
//! the specific VK it was verified against. This is done by hashing the VK into
//! a single field element and including it in the claims hash chain.
//!
//! This module provides both the off-circuit ([`compute_vk_hash`]) and
//! in-circuit ([`assign_as_public_inputs_and_hash_vk`]) versions of this hash.

use std::collections::BTreeMap;

use group::Group;
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{hash::HashCPU, *},
    types::AssignedNative,
    verifier::{AssignedVk, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::EvaluationDomain,
    transcript::Hashable,
};
use midnight_zk_stdlib::{MidnightVK, ZkStdLib};

use crate::ivc::{C, F, S};

/// Result of [`assign_as_public_inputs_and_hash_vk`]: the assigned VK (whose
/// `transcript_repr` is added to the hash chain, enforcing that the inner proof
/// is verified against the same VK that was hashed), its VK hash, and a named
/// map of assigned base points for resolving fixed-base scalars.
pub type VkHashAndBases = (
    AssignedVk<S>,
    AssignedNative<F>,
    BTreeMap<String, <S as SelfEmulation>::AssignedPoint>,
);

/// Computes the VK hash off-circuit: `Poseidon(transcript_repr || bases)`.
///
/// Each curve point is serialized as its foreign-field limb representation
/// (via [`Hashable`]), so this is consistent with the in-circuit version
/// ([`assign_as_public_inputs_and_hash_vk`]).
pub fn compute_vk_hash(vk: &MidnightVK) -> F {
    let vk = vk.vk();
    let to_raw = Hashable::<PoseidonState<F>>::to_input;

    let vk_repr = vec![vk.transcript_repr()];
    let fixed_coms: Vec<F> = vk.fixed_commitments().iter().flat_map(to_raw).collect();
    let perm_coms: Vec<F> = vk.permutation().commitments().iter().flat_map(to_raw).collect();

    <PoseidonChip<F> as HashCPU<F, F>>::hash(&[vk_repr, fixed_coms, perm_coms].concat())
}

/// In-circuit counterpart of [`compute_vk_hash`].
///
/// Witnesses the VK commitment points (fixed and permutation), computes
/// `Poseidon(transcript_repr || bases)` in-circuit, and returns their hash
/// together with a named fixed-bases map (including `-G`).
pub fn assign_as_public_inputs_and_hash_vk(
    layouter: &mut impl Layouter<F>,
    std_lib: &ZkStdLib,
    domain: &EvaluationDomain<F>,
    cs: &ConstraintSystem<F>,
    vk: Value<&MidnightVK>,
) -> Result<VkHashAndBases, Error> {
    let curve_chip = std_lib.bls12_381();

    let nb_fixed = cs.num_fixed_columns() + cs.num_selectors();
    let nb_perm = cs.permutation().columns.len();

    // Witness the VK commitment points.
    let base_values: Vec<Value<C>> = (0..nb_fixed)
        .map(|i| vk.map(|vk| vk.vk().fixed_commitments()[i].clone().into_point()))
        .chain(
            (0..nb_perm)
                .map(|i| vk.map(|vk| vk.vk().permutation().commitments()[i].clone().into_point())),
        )
        .collect();

    let assigned_bases = base_values
        .into_iter()
        .map(|val| curve_chip.assign_without_subgroup_check(layouter, val))
        .collect::<Result<Vec<_>, _>>()?;

    // Assign the VK, witnessing its transcript_repr. The same repr cell is folded
    // into the hash below, binding the verified VK to the hashed one.
    let assigned_vk = std_lib.verifier().assign_vk_as_public_input(
        layouter,
        "inner_vk",
        domain,
        cs,
        vk.map(|vk| vk.vk().transcript_repr()),
    )?;

    // Compute the hash: Poseidon(transcript_repr || bases...).
    let mut input = vec![assigned_vk.transcript_repr().clone()];
    for base in &assigned_bases {
        input.extend(curve_chip.as_public_input(layouter, base)?);
    }
    let hash = std_lib.poseidon(layouter, &input)?;

    // Build the named fixed-bases map (including -G).
    let mut named_map: BTreeMap<String, _> = assigned_bases
        .iter()
        .enumerate()
        .map(|(i, base)| {
            let name = if i < nb_fixed {
                midnight_circuits::verifier::fixed_commitment_name("inner_vk", i)
            } else {
                midnight_circuits::verifier::perm_commitment_name("inner_vk", i - nb_fixed)
            };
            (name, base.clone())
        })
        .collect();

    let neg_g = curve_chip.assign_fixed(layouter, -C::generator())?;
    named_map.insert("-G".into(), neg_g);

    Ok((assigned_vk, hash, named_map))
}

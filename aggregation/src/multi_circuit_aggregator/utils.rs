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
    verifier::{AssignedVk, InCircuitKZG, SelfEmulation, fixed_bases},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::PolynomialLabel,
    transcript::Hashable,
};
use midnight_zk_stdlib::{MidnightVK, ZkStdLib};

use crate::ivc::{C, F, S};

/// Result of [`assign_as_public_inputs_and_hash_vk`]: the assigned VK (whose
/// `transcript_repr` is added to the hash chain, enforcing that the inner proof
/// is verified against the same VK that was hashed), its VK hash, and a named
/// map of assigned base points for resolving fixed-base scalars.
pub type VkHashAndBases = (
    AssignedVk<S, InCircuitKZG<S>>,
    AssignedNative<F>,
    BTreeMap<PolynomialLabel, <S as SelfEmulation>::AssignedPoint>,
);

/// The labels of the VK's fixed bases, in the order they are hashed: every
/// fixed column, then every fixed permutation polynomial.
fn hashed_base_labels(nb_fixed: usize, nb_perm: usize) -> Vec<PolynomialLabel> {
    (0..nb_fixed)
        .map(PolynomialLabel::Fixed)
        .chain((0..nb_perm).map(PolynomialLabel::PermutationFixed))
        .collect()
}

/// Computes the VK hash off-circuit:
/// `Poseidon(transcript_repr || k || omega || bases)`.
///
/// Each curve point is serialized as its foreign-field limb representation
/// (via [`Hashable`]), so this is consistent with the in-circuit version
/// ([`assign_as_public_inputs_and_hash_vk`]).
pub fn compute_vk_hash(vk: &MidnightVK) -> F {
    let vk = vk.vk();
    let to_raw = Hashable::<PoseidonState<F>>::to_input;

    let domain = vk.get_domain();
    let vk_as_public_inputs = vec![
        vk.transcript_repr(),
        F::from(domain.k() as u64),
        domain.get_omega(),
    ];
    let bases = fixed_bases::<S>(vk);
    let labels = hashed_base_labels(
        vk.cs().num_fixed_columns(),
        vk.cs().permutation().columns.len(),
    );
    let base_inputs: Vec<F> = labels.iter().flat_map(|label| to_raw(&bases[label])).collect();

    <PoseidonChip<F> as HashCPU<F, F>>::hash(&[vk_as_public_inputs, base_inputs].concat())
}

/// In-circuit counterpart of [`compute_vk_hash`].
///
/// Witnesses the VK commitment points (fixed and permutation), computes
/// `Poseidon(transcript_repr || k || omega || bases)` in-circuit, and returns
/// their hash together with a named fixed-bases map (including `-G`).
pub fn assign_as_public_inputs_and_hash_vk(
    layouter: &mut impl Layouter<F>,
    std_lib: &ZkStdLib,
    cs: &ConstraintSystem<F>,
    vk: Value<&MidnightVK>,
) -> Result<VkHashAndBases, Error> {
    let curve_chip = std_lib.bls12_381();

    let nb_fixed = cs.num_fixed_columns();
    let nb_perm = cs.permutation().columns.len();

    // Witness the VK commitment points.
    let labels = hashed_base_labels(nb_fixed, nb_perm);
    let bases = vk.map(|vk| fixed_bases::<S>(vk.vk()));
    let base_values: Vec<Value<C>> =
        labels.iter().map(|label| bases.as_ref().map(|bases| bases[label])).collect();

    let assigned_bases = base_values
        .into_iter()
        .map(|val| curve_chip.assign_without_subgroup_check(layouter, val))
        .collect::<Result<Vec<_>, _>>()?;

    // Assign the VK, witnessing its transcript_repr. The same repr cell is folded
    // into the hash below, binding the verified VK to the hashed one.
    let assigned_vk =
        std_lib
            .verifier()
            .assign_vk_as_public_input(layouter, vk.map(|vk| vk.vk()), cs)?;

    // Compute the hash: Poseidon(transcript_repr || k || omega || bases...).
    let mut input = vec![
        assigned_vk.transcript_repr().clone(),
        assigned_vk.k().clone(),
        assigned_vk.omega().clone(),
    ];
    for base in &assigned_bases {
        input.extend(curve_chip.as_public_input(layouter, base)?);
    }
    let hash = std_lib.poseidon(layouter, &input)?;

    // Build the named fixed-bases map (including -G).
    let mut labels_map: BTreeMap<PolynomialLabel, _> =
        labels.into_iter().zip(assigned_bases.iter().cloned()).collect();

    let neg_g = curve_chip.assign_fixed(layouter, -C::generator())?;
    labels_map.insert(PolynomialLabel::Custom("-G".into()), neg_g);

    Ok((assigned_vk, hash, labels_map))
}

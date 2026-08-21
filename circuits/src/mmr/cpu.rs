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

//! CPU (off-circuit) implementation of a Merkle Mountain Range (MMR).

use std::{array, marker::PhantomData};

use crate::{instructions::hash::HashCPU, CircuitField};

/// A Merkle Mountain Range of at most `SIZE` mountains, with a capacity of
/// `2^SIZE - 1` elements. See the [module documentation](crate::mmr) for the
/// structure.
///
/// Slot `i` of `mountains` holds the mountain of height `i`, or `None` when
/// bit `i` of `size` is unset.
#[derive(Clone, Debug)]
pub struct Mmr<F: CircuitField, H: HashCPU<F, F>, const SIZE: usize> {
    size: u64,
    mountains: [Option<Mountain<F, H>>; SIZE],
}

/// The succinct state of an [Mmr]: the number of appended elements and the
/// peak of each mountain. This is the (public) statement form consumed by
/// the in-circuit MMR operations. As everywhere in this module, `SIZE` must
/// be at most 64.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MmrState<F, const SIZE: usize> {
    /// Number of appended elements. Must be smaller than `2^SIZE`.
    pub size: u64,
    /// `peaks[i]` is the peak (root) of the mountain of height `i`, or
    /// `F::ZERO` if bit `i` of `size` is unset.
    pub peaks: [F; SIZE],
}

/// Witness for a prefix claim: `steps[i]` is the node of the big MMR that is
/// absorbed when climbing from height `i` to height `i + 1`, on the heights
/// where the small MMR does not provide a peak of its own. Unused entries
/// (including `steps[SIZE - 1]`, which can never be consumed) are `F::ZERO`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SummitPath<F, const SIZE: usize> {
    pub(crate) steps: [F; SIZE],
}

/// Witness for a membership claim: a Merkle authentication path from a leaf to
/// one of the MMR's peaks.
///
/// - `height` selects the mountain (equivalently, the peak `peaks[height]`)
///   that contains the leaf.
/// - `leaf_index` is the leaf's position within that mountain; its bit `l`
///   gives the left/right direction when climbing from level `l` to `l + 1`.
/// - `siblings[l]` is the sibling node absorbed at that climb.
///
/// Only the low `height` bits of `leaf_index` (which must be smaller than
/// `2^SIZE`) and the first `height` entries of `siblings` are meaningful; the
/// rest is padding, ignored by verification ([Mmr::prove_membership] emits it
/// as `F::ZERO`). The claim fixes no absolute position: `height` and
/// `leaf_index` are a hint supplied by the prover (see
/// [Mmr::verify_membership]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MembershipProof<F, const SIZE: usize> {
    pub(crate) height: usize,
    pub(crate) leaf_index: u64,
    pub(crate) siblings: [F; SIZE],
}

/// A *mountain*: a complete (perfect) binary Merkle tree of some height `h`,
/// stored as a flat vector of its `2^(h+1) - 1` nodes in *in-order* layout:
/// first the left subtree, then the peak, then the right subtree. Merging two
/// mountains is thus a concatenation. In this layout:
/// - leaf `j` sits at position `2j`,
/// - the `j`-th node (from the left) at height `l` sits at position `j *
///   2^(l+1) + 2^l - 1`,
/// - the peak (the tree's root) sits at the middle position, `nodes.len() / 2`.
///
/// ```text
/// height-2 mountain:     in-order positions of its nodes:
///         p                        3
///       /   \
///      *     *                 1       5
///     / \   / \
///    o   o o   o             0   2   4   6
/// ```
#[derive(Clone, Debug)]
pub(crate) struct Mountain<F: CircuitField, H: HashCPU<F, F>> {
    nodes: Vec<F>,
    _marker: PhantomData<H>,
}

impl<F: CircuitField, H: HashCPU<F, F>> Mountain<F, H> {
    /// A mountain of height 0 over the given element. Leaves are hashed with
    /// arity 1, which domain-separates them from internal nodes (arity 2).
    fn new(elem: F) -> Self {
        Mountain {
            nodes: vec![<H as HashCPU<F, F>>::hash(&[elem])],
            _marker: PhantomData,
        }
    }

    /// The height of the mountain.
    pub(crate) fn height(&self) -> usize {
        // The number of nodes is 2^(height + 1) - 1.
        ((self.nodes.len() + 1).trailing_zeros() - 1) as usize
    }

    /// The peak (root) of the mountain.
    pub(crate) fn peak(&self) -> F {
        self.nodes[self.nodes.len() / 2]
    }

    /// The `index`-th node (from the left) at the given height level.
    ///
    /// # Panics
    ///
    /// If `level > self.height()` or `index >= 2^(self.height() - level)`.
    pub(crate) fn node(&self, level: usize, index: u64) -> F {
        self.nodes[(index as usize) * (1 << (level + 1)) + (1 << level) - 1]
    }
}

/// Merges two mountains of equal height into a mountain of one more height,
/// with `left` becoming the left child (mountains merge with the older one
/// on the left).
///
/// # Panics
///
/// If the mountains have different heights.
fn merge_mountains<F: CircuitField, H: HashCPU<F, F>>(
    mut left: Mountain<F, H>,
    right: Mountain<F, H>,
) -> Mountain<F, H> {
    assert_eq!(
        left.height(),
        right.height(),
        "cannot merge mountains of different heights"
    );
    let peak = <H as HashCPU<F, F>>::hash(&[left.peak(), right.peak()]);
    // Thanks to the in-order layout, merging is a concatenation. We reuse
    // the left buffer to avoid a fresh allocation on every merge.
    left.nodes.reserve(right.nodes.len() + 1);
    left.nodes.push(peak);
    left.nodes.extend_from_slice(&right.nodes);
    left
}

impl<F, H, const SIZE: usize> Mmr<F, H, SIZE>
where
    F: CircuitField,
    H: HashCPU<F, F>,
{
    /// An empty MMR.
    ///
    /// # Panics
    ///
    /// If `SIZE > 64`.
    pub fn new() -> Self {
        assert!(SIZE <= 64, "MMR sizes are limited to 64 mountains");
        Mmr {
            size: 0,
            mountains: array::from_fn(|_| None),
        }
    }

    /// The maximum number of elements the MMR can hold: `2^SIZE - 1`.
    fn capacity() -> u64 {
        if SIZE >= 64 {
            u64::MAX
        } else {
            (1u64 << SIZE) - 1
        }
    }

    /// Appends an element to the MMR.
    ///
    /// The new element forms a mountain of height 0. While a mountain of the
    /// same height as the carried one exists, the two merge (like a binary
    /// increment of `size`).
    ///
    /// # Panics
    ///
    /// If the MMR is full, i.e. `size == 2^SIZE - 1`.
    pub fn append(&mut self, elem: F) {
        assert!(
            self.size < Self::capacity(),
            "MMR is full. No more mountains to climb."
        );
        let mut carried = Mountain::new(elem);
        for slot in self.mountains.iter_mut() {
            match slot.take() {
                Some(mountain) => carried = merge_mountains(mountain, carried),
                None => {
                    *slot = Some(carried);
                    self.size += 1;
                    return;
                }
            }
        }
        unreachable!("the capacity check guarantees an empty slot")
    }

    /// The number of elements appended so far.
    pub fn size(&self) -> u64 {
        self.size
    }

    /// The peak of each mountain; `None` iff bit `i` of `size` is unset.
    pub fn peaks(&self) -> [Option<F>; SIZE] {
        array::from_fn(|i| self.mountains[i].as_ref().map(|m| m.peak()))
    }

    /// The succinct state of the MMR, with absent peaks encoded as `F::ZERO`.
    pub fn state(&self) -> MmrState<F, SIZE> {
        MmrState {
            size: self.size,
            peaks: self.peaks().map(|peak| peak.unwrap_or(F::ZERO)),
        }
    }

    /// Produces the witness for the claim that the MMR of the first
    /// `small_size` elements of `self` is a prefix of `self`. The witness
    /// consists of the nodes of `self` that are absorbed while climbing from
    /// the lowest residual peak of the small MMR (see [Self::verify_prefix]).
    ///
    /// # Panics
    ///
    /// If `small_size > self.size()`.
    pub fn prove_prefix(&self, small_size: u64) -> SummitPath<F, SIZE> {
        assert!(
            small_size <= self.size,
            "a prefix cannot be longer than the MMR itself"
        );
        let mut steps = [F::ZERO; SIZE];
        let (a, b) = (small_size, self.size);

        // Case 1: Identical MMRs, all peaks match directly.
        if a == b {
            return SummitPath { steps };
        }

        // The residual mountains of the small MMR fold into the mountain of
        // `self` sitting at the highest bit where the sizes differ.
        let d = (a ^ b).ilog2() as usize;
        // Number of residual elements: they span the local leaf range
        // [0, a_res) of said mountain.
        let a_res = a & ((1u64 << d) - 1);

        // Case 2: All mountains in the small MMR are present identically (without
        // merge) in the large MMR.
        if a_res == 0 {
            // All the small mountains match one of `self` directly: no climb.
            return SummitPath { steps };
        }

        // Case 3: Some mountains in the small MMR are now a part of the d-th mountain
        // in the large MMR.
        let mountain = self.mountains[d].as_ref().expect("bit d of self.size is set");

        // The climb starts at the small MMR's lowest peak.
        let m = a_res.trailing_zeros() as usize;
        for (i, step) in steps.iter_mut().enumerate().take(d).skip(m) {
            // When the small MMR has a peak at height i (beyond the starting
            // one), it is absorbed instead of a witnessed node.
            let absorb_own_peak = i > m && (a >> i) & 1 == 1;
            if !absorb_own_peak {
                // The climbing node at height i is the block containing the
                // local leaf `a_res - 1`; absorb its right sibling (hence the
                // `+ 1`).
                let block = (a_res - 1) >> i;
                *step = mountain.node(i, block + 1);
            }
        }
        SummitPath { steps }
    }

    /// Verifies that the elements of the MMR with state `small` are a prefix
    /// of the elements of the MMR with state `big`, given a [SummitPath]
    /// witness (produced with [Self::prove_prefix] on the big MMR).
    ///
    /// This function is the off-circuit specification of the in-circuit
    /// check: it mirrors, gate by gate, the constraints of the MMR gadget.
    /// All its control flow is derived from the bits of the two sizes.
    pub fn verify_prefix(
        small: &MmrState<F, SIZE>,
        big: &MmrState<F, SIZE>,
        path: &SummitPath<F, SIZE>,
    ) -> bool {
        // States whose size exceeds SIZE bits are not representable
        // in-circuit and are rejected outright.
        if small.size > Self::capacity() || big.size > Self::capacity() {
            return false;
        }

        let a_bits: [bool; SIZE] = array::from_fn(|i| (small.size >> i) & 1 == 1);
        let b_bits: [bool; SIZE] = array::from_fn(|i| (big.size >> i) & 1 == 1);

        // agree[i]: the two sizes agree on all bits at positions >= i.
        let mut agree = vec![true; SIZE + 1];
        for i in (0..SIZE).rev() {
            agree[i] = agree[i + 1] && (a_bits[i] == b_bits[i]);
        }

        // started[i]: the small MMR has a peak at some height < i, i.e. the
        // climb is underway when reaching height i.
        let mut started = vec![false; SIZE + 1];
        for i in 0..SIZE {
            started[i + 1] = started[i] || a_bits[i];
        }

        let mut ok = true;
        // The climbing node; its initial value is irrelevant (it is never
        // consumed before being overwritten by a starting peak).
        let mut cur = F::ZERO;

        for i in 0..SIZE {
            // The sizes agree above height i and both MMRs have a mountain
            // here: their peaks must match directly.
            let direct_match = agree[i + 1] && a_bits[i] && b_bits[i];
            if direct_match {
                ok &= small.peaks[i] == big.peaks[i];
            }

            // Highest bit where the sizes differ (at most one height).
            let fin = agree[i + 1] && (a_bits[i] != b_bits[i]);

            // At said height, the small size must have the unset bit;
            // otherwise small > big and it cannot be a prefix.
            if fin && a_bits[i] {
                ok = false;
            }

            // The climb starts at the lowest peak of the small MMR.
            let is_start = a_bits[i] && !started[i];
            let input = if is_start { small.peaks[i] } else { cur };

            // If a climb took place, it must land exactly on big's peak at
            // the height of the first size disagreement.
            if fin && started[i] {
                ok &= input == big.peaks[i];
            }

            // Climb one level up: the node at height i is combined either
            // with small's own peak at this height (as left sibling) or with
            // a witnessed node of the big MMR (as right sibling). The top
            // height never climbs.
            if i < SIZE - 1 {
                let absorb_own_peak = a_bits[i] && started[i];
                let (left, right) = if absorb_own_peak {
                    (small.peaks[i], input)
                } else {
                    (input, path.steps[i])
                };
                let climbing = started[i + 1] && !agree[i + 1];
                cur = if climbing {
                    <H as HashCPU<F, F>>::hash(&[left, right])
                } else {
                    input
                };
            }
        }
        ok
    }

    /// Produces a membership proof for the element at append-position `pos`
    /// (`0` is the oldest element). The proof authenticates the leaf against
    /// the peak of the mountain that contains it.
    ///
    /// # Panics
    ///
    /// If `pos >= self.size()`.
    pub fn prove_membership(&self, pos: u64) -> MembershipProof<F, SIZE> {
        assert!(pos < self.size, "position out of range");

        // Locate the mountain holding `pos`: taller mountains hold the older
        // elements, so scan heights high-to-low, accumulating their leaf counts
        // until `pos` falls inside one.
        let mut offset = 0u64;
        let (mut height, mut leaf_index) = (0, 0);
        for h in (0..SIZE).rev() {
            if (self.size >> h) & 1 == 1 {
                let leaves = 1u64 << h;
                if pos < offset + leaves {
                    (height, leaf_index) = (h, pos - offset);
                    break;
                }
                offset += leaves;
            }
        }

        // The authentication path: the sibling of the climbing node at each
        // level, following the bits of `leaf_index`.
        let mountain = self.mountains[height].as_ref().expect("bit `height` of size is set");
        let mut siblings = [F::ZERO; SIZE];
        for (l, sibling) in siblings.iter_mut().enumerate().take(height) {
            *sibling = mountain.node(l, (leaf_index >> l) ^ 1);
        }

        MembershipProof {
            height,
            leaf_index,
            siblings,
        }
    }

    /// Verifies that `elem` is one of the elements committed to by `state`,
    /// given a [MembershipProof] (produced with [Self::prove_membership]).
    ///
    /// The element's position is not fixed by this check: `height` and
    /// `leaf_index` are supplied by the proof as a hint. This is the
    /// off-circuit specification of the in-circuit
    /// [assert_membership](crate::mmr::mmr_gadget::MmrGadget::assert_membership).
    pub fn verify_membership(
        state: &MmrState<F, SIZE>,
        elem: F,
        proof: &MembershipProof<F, SIZE>,
    ) -> bool {
        // Sizes and leaf indices exceeding SIZE bits are not representable
        // in-circuit.
        if state.size > Self::capacity() || proof.leaf_index > Self::capacity() {
            return false;
        }

        // The target mountain must exist.
        let h = proof.height;
        if h >= SIZE || (state.size >> h) & 1 == 0 {
            return false;
        }

        // Fold the (arity-1) leaf hash up to the peak, following the index bits:
        // a `0` bit places the running node on the left, a `1` on the right.
        let mut node = <H as HashCPU<F, F>>::hash(&[elem]);
        for l in 0..h {
            let sibling = proof.siblings[l];
            node = if (proof.leaf_index >> l) & 1 == 0 {
                <H as HashCPU<F, F>>::hash(&[node, sibling])
            } else {
                <H as HashCPU<F, F>>::hash(&[sibling, node])
            };
        }
        node == state.peaks[h]
    }
}

impl<F, H, const SIZE: usize> Default for Mmr<F, H, SIZE>
where
    F: CircuitField,
    H: HashCPU<F, F>,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::hash::poseidon::{constants::PoseidonField, PoseidonChip};

    /// Recomputes the root of a complete Merkle tree over the given leaves by
    /// direct recursion.
    fn subtree_root<F: CircuitField, H: HashCPU<F, F>>(leaves: &[F]) -> F {
        if leaves.len() == 1 {
            return <H as HashCPU<F, F>>::hash(&[leaves[0]]);
        }
        let half = leaves.len() / 2;
        let left = subtree_root::<F, H>(&leaves[..half]);
        let right = subtree_root::<F, H>(&leaves[half..]);
        <H as HashCPU<F, F>>::hash(&[left, right])
    }

    /// Recomputes the expected peaks of an MMR over the given leaves,
    /// independently of the [Mmr] logic: the mountain of height `i` exists
    /// iff bit `i` of the number of leaves is set, and taller mountains
    /// contain the older leaves.
    fn expected_peaks<F: CircuitField, H: HashCPU<F, F>, const SIZE: usize>(
        leaves: &[F],
    ) -> [Option<F>; SIZE] {
        let mut peaks = array::from_fn(|_| None);
        let mut offset = 0;
        for i in (0..SIZE).rev() {
            if (leaves.len() >> i) & 1 == 1 {
                peaks[i] = Some(subtree_root::<F, H>(&leaves[offset..offset + (1 << i)]));
                offset += 1 << i;
            }
        }
        peaks
    }

    fn test_append<F: CircuitField, H: HashCPU<F, F>>() {
        const SIZE: usize = 7;
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let leaves: Vec<F> = (0..64).map(|_| F::random(&mut rng)).collect();

        let mut mmr = Mmr::<F, H, SIZE>::new();
        assert_eq!(mmr.size(), 0);
        assert_eq!(mmr.peaks(), array::from_fn(|_| None));

        for n in 1..=leaves.len() {
            mmr.append(leaves[n - 1]);
            assert_eq!(mmr.size(), n as u64);
            assert_eq!(mmr.peaks(), expected_peaks::<F, H, SIZE>(&leaves[..n]));

            // The state encodes absent peaks as zero.
            let state = mmr.state();
            assert_eq!(state.size, n as u64);
            for (state_peak, peak) in state.peaks.iter().zip(mmr.peaks()) {
                assert_eq!(*state_peak, peak.unwrap_or(F::ZERO));
            }
        }
    }

    fn test_node_layout<F: CircuitField, H: HashCPU<F, F>>() {
        // A single mountain of height 3 (8 leaves).
        let leaves: [F; 8] = array::from_fn(|i| F::from(i as u64));
        let mut mmr = Mmr::<F, H, 4>::new();
        leaves.iter().for_each(|leaf| mmr.append(*leaf));

        let mountain = mmr.mountains[3].as_ref().unwrap();
        assert_eq!(mountain.height(), 3);

        // Level 0 holds the (arity-1) hashed leaves, in order.
        for (j, leaf) in leaves.iter().enumerate() {
            assert_eq!(
                mountain.node(0, j as u64),
                <H as HashCPU<F, F>>::hash(&[*leaf])
            );
        }
        // Inner nodes hash their two children; the peak is the top node.
        for level in 1..=3 {
            for j in 0..(8 >> level) as u64 {
                let expected = <H as HashCPU<F, F>>::hash(&[
                    mountain.node(level - 1, 2 * j),
                    mountain.node(level - 1, 2 * j + 1),
                ]);
                assert_eq!(mountain.node(level, j), expected);
            }
        }
        assert_eq!(mountain.peak(), mountain.node(3, 0));
    }

    /// The step indices of a [SummitPath] that are actually consumed when
    /// verifying that `a` is a prefix of `b` (mirrors [Mmr::prove_prefix]).
    fn used_steps<const SIZE: usize>(a: u64, b: u64) -> [bool; SIZE] {
        let mut used = [false; SIZE];
        if a == b {
            return used;
        }
        let d = (a ^ b).ilog2() as usize;
        let a_res = a & ((1u64 << d) - 1);
        if a_res == 0 {
            return used;
        }
        let m = a_res.trailing_zeros() as usize;
        for (i, used_i) in used.iter_mut().enumerate().take(d).skip(m) {
            *used_i = i == m || (a >> i) & 1 == 0;
        }
        used
    }

    fn test_prefix<F: CircuitField, H: HashCPU<F, F>>() {
        const SIZE: usize = 5;
        const MAX: usize = 24;
        type M<F, H> = Mmr<F, H, SIZE>;

        // All prefix MMRs over the leaves 0, 1, 2, ..., plus variants with
        // shifted content (leaves 1, 2, 3, ...) for mismatch tests.
        let mut mmrs: Vec<M<F, H>> = vec![Mmr::new()];
        let mut shifted_mmrs: Vec<M<F, H>> = vec![Mmr::new()];
        for n in 0..MAX {
            let mut next = mmrs[n].clone();
            next.append(F::from(n as u64));
            mmrs.push(next);

            let mut shifted = shifted_mmrs[n].clone();
            shifted.append(F::from(n as u64 + 1));
            shifted_mmrs.push(shifted);
        }

        for b in 0..=MAX {
            let big = &mmrs[b];
            for a in 0..=b {
                let small = &mmrs[a];
                let path = big.prove_prefix(a as u64);
                assert!(
                    M::<F, H>::verify_prefix(&small.state(), &big.state(), &path),
                    "honest prefix rejected: a = {a}, b = {b}"
                );

                // A small MMR with different content must be rejected.
                if a > 0 {
                    assert!(
                        !M::<F, H>::verify_prefix(&shifted_mmrs[a].state(), &big.state(), &path),
                        "content mismatch accepted: a = {a}, b = {b}"
                    );
                }

                // Tampering with a consumed step must be rejected, while the
                // padding entries must remain free.
                let used = used_steps::<SIZE>(a as u64, b as u64);
                for (i, step_used) in used.iter().enumerate() {
                    let mut tampered = path;
                    tampered.steps[i] += F::ONE;
                    let accepted =
                        M::<F, H>::verify_prefix(&small.state(), &big.state(), &tampered);
                    assert_eq!(
                        accepted, !step_used,
                        "tampered steps[{i}] misbehaved: a = {a}, b = {b}"
                    );
                }
            }

            // A longer MMR is never a prefix of a shorter one, regardless of
            // the witness.
            for (a, longer) in mmrs.iter().enumerate().skip(b + 1) {
                let path = SummitPath {
                    steps: [F::ZERO; SIZE],
                };
                assert!(
                    !M::<F, H>::verify_prefix(&longer.state(), &big.state(), &path),
                    "a > b accepted: a = {a}, b = {b}"
                );
            }
        }
    }

    fn test_membership<F: CircuitField, H: HashCPU<F, F>>() {
        const SIZE: usize = 6;
        let mut rng = ChaCha8Rng::seed_from_u64(0xfeedbeef);
        let n = 45usize;
        // n = 45 = 0b101101, so the height-1 mountain is absent.
        assert_eq!(
            n as u64 & 0b10,
            0,
            "test assumes the height-1 mountain is absent"
        );
        let leaves: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();

        let mut mmr = Mmr::<F, H, SIZE>::new();
        leaves.iter().for_each(|leaf| mmr.append(*leaf));
        let state = mmr.state();

        for (pos, &leaf) in leaves.iter().enumerate() {
            let proof = mmr.prove_membership(pos as u64);
            assert!(
                Mmr::<F, H, SIZE>::verify_membership(&state, leaf, &proof),
                "honest membership rejected at pos {pos}"
            );

            // A wrong element is rejected against an honest path.
            assert!(
                !Mmr::<F, H, SIZE>::verify_membership(&state, leaf + F::ONE, &proof),
                "wrong element accepted at pos {pos}"
            );

            // Tampering with any consumed sibling is rejected.
            for l in 0..proof.height {
                let mut tampered = proof;
                tampered.siblings[l] += F::ONE;
                assert!(
                    !Mmr::<F, H, SIZE>::verify_membership(&state, leaf, &tampered),
                    "tampered sibling[{l}] accepted at pos {pos}"
                );
            }

            // Flipping a consumed direction bit points at the wrong subtree.
            if proof.height > 0 {
                let mut tampered = proof;
                tampered.leaf_index ^= 1;
                assert!(
                    !Mmr::<F, H, SIZE>::verify_membership(&state, leaf, &tampered),
                    "flipped direction bit accepted at pos {pos}"
                );
            }
        }

        // An element that is not in the MMR is rejected.
        let outsider = F::random(&mut rng);
        let proof = mmr.prove_membership(0);
        assert!(
            !Mmr::<F, H, SIZE>::verify_membership(&state, outsider, &proof),
            "non-member accepted"
        );

        // A height pointing at an absent mountain is rejected.
        let mut absent = mmr.prove_membership(0);
        absent.height = 1;
        assert!(
            !Mmr::<F, H, SIZE>::verify_membership(&state, leaves[0], &absent),
            "membership against an absent mountain accepted"
        );
    }

    fn run_poseidon_tests<F: PoseidonField>() {
        test_append::<F, PoseidonChip<F>>();
        test_node_layout::<F, PoseidonChip<F>>();
        test_prefix::<F, PoseidonChip<F>>();
        test_membership::<F, PoseidonChip<F>>();
    }

    #[test]
    fn test_mmr_poseidon() {
        run_poseidon_tests::<midnight_curves::Fq>();
    }

    #[test]
    #[should_panic(expected = "MMR is full")]
    fn test_append_on_full_mmr_panics() {
        type F = midnight_curves::Fq;
        let mut mmr = Mmr::<F, PoseidonChip<F>, 3>::new();
        for i in 0..8 {
            mmr.append(F::from(i));
        }
    }
}

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

//! In-circuit operations over Merkle Mountain Ranges.
//!
//! The gadget is *stateless*: it operates over explicit [AssignedMmr] values
//! (assigned [MmrState]s), which makes relational statements over several
//! MMRs, such as [MmrGadget::assert_prefix], possible.
//!
//! The in-circuit statements are relative to the MMR states as commitments:
//! the provenance of a well-formed state (i.e. one whose peaks are the roots
//! of the mountains of an actual sequence of elements) must come from
//! off-circuit appends or from a trusted public input.

use std::marker::PhantomData;

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    midnight_proofs::plonk::{Advice, Column, ConstraintSystem, Fixed, Instance},
};

use crate::{
    CircuitField,
    instructions::{HashInstructions, NativeInstructions},
    mmr::cpu::{MembershipProof, MmrState, SummitPath},
    types::{AssignedBit, AssignedNative, InnerValue, Instantiable},
};

/// An assigned Merkle Mountain Range state (see [MmrState]).
///
/// The following invariants are enforced at construction:
/// - `size` equals `sum_i size_bits[i] * 2^i` (in particular, the size is
///   range-checked to be smaller than `2^CAPACITY`),
/// - `peaks[i]` is zero whenever `size_bits[i]` is zero (canonical encoding of
///   absent mountains).
#[derive(Clone, Debug)]
pub struct AssignedMmr<F: CircuitField, const CAPACITY: usize> {
    pub(crate) size: AssignedNative<F>,
    pub(crate) size_bits: [AssignedBit<F>; CAPACITY],
    pub(crate) peaks: [AssignedNative<F>; CAPACITY],
}

impl<F: CircuitField, const CAPACITY: usize> AssignedMmr<F, CAPACITY> {
    /// MMR state in its public input representation: size
    /// followed by the peaks as CAPACITY+1 field elements. Agrees with
    /// [Instantiable::as_public_input].
    pub fn as_public_input(&self) -> Vec<AssignedNative<F>> {
        let mut cells = vec![self.size.clone()];
        cells.extend(self.peaks.iter().cloned());
        cells
    }
}

impl<F: CircuitField, const CAPACITY: usize> InnerValue for AssignedMmr<F, CAPACITY> {
    type Element = MmrState<F, CAPACITY>;

    fn value(&self) -> Value<MmrState<F, CAPACITY>> {
        let size = self.size.value().copied();
        let peaks = self.peaks.value();
        size.zip(peaks).map(|(size, peaks)| MmrState {
            size: u64::try_from(size.to_biguint()).expect("MMR size fits in u64"),
            peaks,
        })
    }
}

impl<F: CircuitField, const CAPACITY: usize> Instantiable<F> for AssignedMmr<F, CAPACITY> {
    fn as_public_input(element: &MmrState<F, CAPACITY>) -> Vec<F> {
        let mut public_input = vec![F::from(element.size)];
        public_input.extend(element.peaks);
        public_input
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(fields: &[F]) -> Option<MmrState<F, CAPACITY>> {
        if fields.len() != CAPACITY + 1 {
            return None;
        }
        let size = u64::try_from(fields[0].to_biguint()).ok()?;
        if CAPACITY < 64 && size >= (1u64 << CAPACITY) {
            return None;
        }
        let peaks: [F; CAPACITY] = fields[1..].try_into().ok()?;
        // Absent peaks must be encoded as zero.
        for (i, peak) in peaks.iter().enumerate() {
            if (size >> i) & 1 == 0 && *peak != F::ZERO {
                return None;
            }
        }
        Some(MmrState { size, peaks })
    }
}

/// An assigned [SummitPath]: the witness of a prefix claim.
#[derive(Clone, Debug)]
pub struct AssignedSummitPath<F: CircuitField, const CAPACITY: usize> {
    pub(crate) steps: [AssignedNative<F>; CAPACITY],
}

impl<F: CircuitField, const CAPACITY: usize> InnerValue for AssignedSummitPath<F, CAPACITY> {
    type Element = SummitPath<F, CAPACITY>;

    fn value(&self) -> Value<SummitPath<F, CAPACITY>> {
        self.steps.value().map(|steps| SummitPath { steps })
    }
}

/// An assigned [MembershipProof]: the witness of a membership claim.
#[derive(Clone, Debug)]
pub struct AssignedMembershipProof<F: CircuitField, const CAPACITY: usize> {
    pub(crate) height: AssignedNative<F>,
    pub(crate) index_bits: [AssignedBit<F>; CAPACITY],
    pub(crate) siblings: [AssignedNative<F>; CAPACITY],
}

impl<F: CircuitField, const CAPACITY: usize> InnerValue for AssignedMembershipProof<F, CAPACITY> {
    type Element = MembershipProof<F, CAPACITY>;

    fn value(&self) -> Value<MembershipProof<F, CAPACITY>> {
        let height = self
            .height
            .value()
            .map(|h| u64::try_from(h.to_biguint()).expect("MMR height fits in u64") as usize);
        let index_bits = self.index_bits.value();
        let siblings = self.siblings.value();
        (height.zip(index_bits).zip(siblings)).map(|((height, index_bits), siblings)| {
            let leaf_index =
                (index_bits.iter().enumerate()).fold(
                    0u64,
                    |acc, (l, bit)| if *bit { acc | (1 << l) } else { acc },
                );
            MembershipProof {
                height,
                leaf_index,
                siblings,
            }
        })
    }
}

/// How a check reports each of its conditions.
enum CheckMode<F: CircuitField> {
    /// Constrain each condition on the spot; the circuit becomes
    /// unsatisfiable if one fails.
    Assert,
    /// Constrain nothing; accumulate one indicator per possible failure,
    /// folded by `finish` into the returned bit. More expensive than `Assert`.
    CollectFailures(Vec<AssignedBit<F>>),
}

/// Stateless gadget for in-circuit MMR operations.
/// Keeps no internal state: all operands are explicit [AssignedMmr] values.
#[derive(Clone, Debug)]
pub struct MmrGadget<F, N, H>
where
    F: CircuitField,
    N: NativeInstructions<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    native_gadget: N,
    hash_chip: H,
    _marker: PhantomData<F>,
}

impl<F, N, H> MmrGadget<F, N, H>
where
    F: CircuitField,
    N: NativeInstructions<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    /// Creates an MMR gadget.
    pub fn new(native_gadget: &N, hash_chip: &H) -> Self {
        Self {
            native_gadget: native_gadget.clone(),
            hash_chip: hash_chip.clone(),
            _marker: PhantomData,
        }
    }

    /// Assigns an MMR state as a private input, enforcing the [AssignedMmr]
    /// invariants: the assigned size is range-checked to `CAPACITY` bits and the
    /// peaks at absent slots are (re)set to zero.
    pub fn assign<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        state: Value<MmrState<F, CAPACITY>>,
    ) -> Result<AssignedMmr<F, CAPACITY>, Error> {
        let size = self.native_gadget.assign(layouter, state.map(|s| F::from(s.size)))?;
        let peaks = state.map(|s| s.peaks).transpose_array();
        let peaks = self.native_gadget.assign_many(layouter, &peaks)?;
        self.enforce_state_invariants(layouter, size, peaks)
    }

    /// Assigns a fixed (constant) MMR state.
    pub fn assign_fixed<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        state: MmrState<F, CAPACITY>,
    ) -> Result<AssignedMmr<F, CAPACITY>, Error> {
        let size = self.native_gadget.assign_fixed(layouter, F::from(state.size))?;
        let peaks = self.native_gadget.assign_many_fixed(layouter, &state.peaks)?;
        self.enforce_state_invariants(layouter, size, peaks)
    }

    /// Constrains the given MMR state as a public input, in the order of
    /// [AssignedMmr::as_public_input]: the size followed by the peaks.
    pub fn constrain_as_public_input<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        mmr: &AssignedMmr<F, CAPACITY>,
    ) -> Result<(), Error> {
        self.native_gadget.constrain_as_public_input(layouter, &mmr.size)?;
        (mmr.peaks.iter())
            .try_for_each(|peak| self.native_gadget.constrain_as_public_input(layouter, peak))
    }

    /// Assigns a [SummitPath] as a private input.
    ///
    /// The path is not constrained in any way: its steps get verified when
    /// consumed by [Self::assert_prefix].
    pub fn assign_summit_path<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        path: Value<SummitPath<F, CAPACITY>>,
    ) -> Result<AssignedSummitPath<F, CAPACITY>, Error> {
        let steps = path.map(|p| p.steps).transpose_array();
        let steps = self.native_gadget.assign_many(layouter, &steps)?;
        Ok(AssignedSummitPath {
            steps: steps.try_into().unwrap(),
        })
    }

    /// Checks if the elements of the MMR with state `small` are a prefix
    /// of the elements of the MMR with state `big`, given a summit path
    /// witness (produced off-circuit with
    /// [Mmr::prove_prefix](crate::mmr::cpu::Mmr::prove_prefix) on the big
    /// MMR), and returns the result as a bit.
    /// [Self::assert_prefix] is the asserting form which may be cheaper
    /// than a call to this method plus an assertion on the resulting bit.
    ///
    /// This is the in-circuit counterpart of
    /// [Mmr::is_prefix](crate::mmr::cpu::Mmr::is_prefix).
    pub fn is_prefix<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        small: &AssignedMmr<F, CAPACITY>,
        big: &AssignedMmr<F, CAPACITY>,
        path: &AssignedSummitPath<F, CAPACITY>,
    ) -> Result<AssignedBit<F>, Error> {
        let mut mode = CheckMode::CollectFailures(vec![]);
        self.prefix_check(layouter, small, big, path, &mut mode)?;
        Ok(self.finish(layouter, mode)?.expect("collecting failures"))
    }

    /// Asserts that the elements of the MMR with state `small` are a prefix of
    /// the elements of the MMR with state `big`: [Self::is_prefix]'s
    /// result, asserted.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If `small` is not a prefix of `big` (in particular, whenever
    /// `small.size > big.size`), or if the summit path steps are incorrect.
    pub fn assert_prefix<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        small: &AssignedMmr<F, CAPACITY>,
        big: &AssignedMmr<F, CAPACITY>,
        path: &AssignedSummitPath<F, CAPACITY>,
    ) -> Result<(), Error> {
        self.prefix_check(layouter, small, big, path, &mut CheckMode::Assert)
    }

    /// Main function implementing the bulk of what `is_prefix` and
    /// `assert_prefix` do. The body is made modular by using `record_*`
    /// functions that behave differently depending on `mode` (either by
    /// asserting a constraint or collecting a boolean in the mutable `mode`
    /// accumulator).
    fn prefix_check<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        small: &AssignedMmr<F, CAPACITY>,
        big: &AssignedMmr<F, CAPACITY>,
        path: &AssignedSummitPath<F, CAPACITY>,
        mode: &mut CheckMode<F>,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;
        let a_bits = &small.size_bits;
        let b_bits = &big.size_bits;

        // agree[i]: the two sizes agree on all bits at positions >= i
        // (computed top-down; agree[CAPACITY] is trivially true).
        let mut agree: Vec<AssignedBit<F>> = Vec::with_capacity(CAPACITY + 1);
        agree.push(ng.assign_fixed(layouter, true)?);
        for i in (0..CAPACITY).rev() {
            let bits_equal = ng.is_equal(layouter, &a_bits[i], &b_bits[i])?;
            let and = ng.and(layouter, &[agree.last().unwrap().clone(), bits_equal])?;
            agree.push(and);
        }
        agree.reverse();

        // started[i]: the small MMR has a peak at some height < i, i.e. the
        // climb is underway when reaching height i.
        let mut started: Vec<AssignedBit<F>> = Vec::with_capacity(CAPACITY + 1);
        started.push(ng.assign_fixed(layouter, false)?);
        for a_bit in a_bits.iter() {
            let or = ng.or(layouter, &[started.last().unwrap().clone(), a_bit.clone()])?;
            started.push(or);
        }

        // The climbing node; its initial value is irrelevant (it is never
        // consumed before being overwritten by a starting peak).
        let mut cur: AssignedNative<F> = ng.assign_fixed(layouter, F::ZERO)?;

        for i in 0..CAPACITY {
            // The sizes agree from height i up: the peaks must match. When
            // neither MMR has a mountain here both peaks are the canonical
            // zero, so the check is vacuous rather than wrong.
            self.record_eq(layouter, mode, &agree[i], &small.peaks[i], &big.peaks[i])?;

            // fin: highest bit where the sizes differ (at most one height),
            // i.e. the single step where the agree chain drops.
            let fin = ng.xor(layouter, &[agree[i + 1].clone(), agree[i].clone()])?;

            // At said height, the small size must have the unset bit;
            // otherwise small > big and it cannot be a prefix.
            let violation = ng.and(layouter, &[fin.clone(), a_bits[i].clone()])?;
            self.record_false(layouter, mode, &violation)?;

            // The climb starts at the lowest peak of the small MMR: the
            // single step where the started chain rises.
            let is_start = ng.xor(layouter, &[started[i + 1].clone(), started[i].clone()])?;
            let input = ng.select(layouter, &is_start, &small.peaks[i], &cur)?;

            // If a climb took place, it must land exactly on big's peak at
            // the height of the first size disagreement.
            let must_land = ng.and(layouter, &[fin, started[i].clone()])?;
            self.record_eq(layouter, mode, &must_land, &input, &big.peaks[i])?;

            // Climb one level up: the node at height i is combined either
            // with small's own peak at this height (as left sibling) or with
            // a witnessed node of the big MMR (as right sibling). The top
            // height never climbs.
            if i < CAPACITY - 1 {
                let absorb_own_peak = ng.and(layouter, &[a_bits[i].clone(), started[i].clone()])?;
                let left = ng.select(layouter, &absorb_own_peak, &small.peaks[i], &input)?;
                let right = ng.select(layouter, &absorb_own_peak, &input, &path.steps[i])?;
                // Hashed unconditionally: outside a climb the result is
                // never read, as the landing check is only ever reached
                // through an unbroken chain of climbing steps.
                cur = self.hash_chip.hash(layouter, &[left, right])?;
            }
        }

        Ok(())
    }

    /// Assigns a [MembershipProof] as a private input.
    ///
    /// The proof is not constrained here; its fields are verified when consumed
    /// by [Self::assert_membership]. Only the low `CAPACITY` bits of the leaf
    /// index are assigned; a larger index is not representable.
    pub fn assign_membership_proof<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        proof: Value<MembershipProof<F, CAPACITY>>,
    ) -> Result<AssignedMembershipProof<F, CAPACITY>, Error> {
        let height =
            self.native_gadget.assign(layouter, proof.map(|p| F::from(p.height as u64)))?;
        let index_bits = proof
            .map(|p| std::array::from_fn::<bool, CAPACITY, _>(|l| (p.leaf_index >> l) & 1 == 1))
            .transpose_array();
        let index_bits: Vec<AssignedBit<F>> =
            self.native_gadget.assign_many(layouter, &index_bits)?;
        let siblings = proof.map(|p| p.siblings).transpose_array();
        let siblings = self.native_gadget.assign_many(layouter, &siblings)?;
        Ok(AssignedMembershipProof {
            height,
            index_bits: index_bits.try_into().unwrap(),
            siblings: siblings.try_into().unwrap(),
        })
    }

    /// Checks that `elem` is one of the elements committed to by `mmr`,
    /// given a membership proof (produced off-circuit with
    /// [Mmr::prove_membership](crate::mmr::cpu::Mmr::prove_membership)), and
    /// returns the result as a bit.
    /// [Self::assert_membership] is the asserting form, which may be cheaper
    /// than calling this method and constraining the result.
    ///
    /// The element's position is not fixed: `height` and `leaf_index` are
    /// supplied by the proof as a hint. This is the in-circuit counterpart of
    /// [Mmr::is_member](crate::mmr::cpu::Mmr::is_member).
    ///
    /// The check has no unsatisfiable case: every failure (wrong element,
    /// wrong siblings, a height pointing at an absent mountain, a wrong leaf
    /// index) returns `0`.
    pub fn is_member<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        mmr: &AssignedMmr<F, CAPACITY>,
        elem: &AssignedNative<F>,
        proof: &AssignedMembershipProof<F, CAPACITY>,
    ) -> Result<AssignedBit<F>, Error> {
        let mut mode = CheckMode::CollectFailures(vec![]);
        self.member_check(layouter, mmr, elem, proof, &mut mode)?;
        Ok(self.finish(layouter, mode)?.expect("collecting failures"))
    }

    /// Asserts that `elem` is one of the elements committed to by `mmr`.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If `elem` is not a member of `mmr`, or if the proof is malformed.
    pub fn assert_membership<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        mmr: &AssignedMmr<F, CAPACITY>,
        elem: &AssignedNative<F>,
        proof: &AssignedMembershipProof<F, CAPACITY>,
    ) -> Result<(), Error> {
        self.member_check(layouter, mmr, elem, proof, &mut CheckMode::Assert)
    }

    /// Main function implementing the bulk of what `is_member` and
    /// `assert_membership` do. The body is made modular by using `record_*`
    /// functions that behave differently depending on `mode` (either by
    /// asserting a constraint or collecting a boolean in the mutable `mode`
    /// accumulator).
    fn member_check<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        mmr: &AssignedMmr<F, CAPACITY>,
        elem: &AssignedNative<F>,
        proof: &AssignedMembershipProof<F, CAPACITY>,
        mode: &mut CheckMode<F>,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;

        // Bit `l` of the leaf index is the left/right direction of the climb
        // from level `l` to `l + 1`.
        let index_bits = &proof.index_bits;

        // `node` is the root of the height-`l` subtree over the leaf. It starts
        // as the arity-1 leaf hash, which is the peak of a height-0 mountain.
        let mut node = self.hash_chip.hash(layouter, std::slice::from_ref(elem))?;

        // Set once the climb reaches the claimed height at a present mountain,
        // ensuring that `height` selects an existing slot in `[0, CAPACITY)`.
        let mut matched: AssignedBit<F> = ng.assign_fixed(layouter, false)?;

        for (l, (peak, size_bit)) in mmr.peaks.iter().zip(mmr.size_bits.iter()).enumerate() {
            let is_height = ng.is_equal_to_fixed(layouter, &proof.height, F::from(l as u64))?;
            self.record_eq(layouter, mode, &is_height, &node, peak)?;

            let matches_here = ng.and(layouter, &[is_height, size_bit.clone()])?;
            matched = ng.or(layouter, &[matched, matches_here])?;

            // Climb one level (the top height never climbs).
            if l < CAPACITY - 1 {
                let dir = &index_bits[l];
                let left = ng.select(layouter, dir, &proof.siblings[l], &node)?;
                let right = ng.select(layouter, dir, &node, &proof.siblings[l])?;
                node = self.hash_chip.hash(layouter, &[left, right])?;
            }
        }

        // The climb must also have matched a present mountain.
        self.record_eq_fixed(layouter, mode, &matched.0, F::ONE)
    }

    /// Records `cond => x == y`.
    fn record_eq(
        &self,
        layouter: &mut impl Layouter<F>,
        mode: &mut CheckMode<F>,
        cond: &AssignedBit<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;
        match mode {
            CheckMode::Assert => ng.cond_assert_equal(layouter, cond, x, y),
            CheckMode::CollectFailures(failures) => {
                let equal = ng.is_equal(layouter, x, y)?;
                // `cond AND NOT equal` (written as an `add_and_mul` to save one row).
                failures.push(AssignedBit(ng.add_and_mul(
                    layouter,
                    (F::ONE, &cond.0),
                    (F::ZERO, &equal.0),
                    (F::ZERO, &cond.0),
                    F::ZERO,
                    -F::ONE,
                )?));
                Ok(())
            }
        }
    }

    /// Records that `bit` must be false.
    fn record_false(
        &self,
        layouter: &mut impl Layouter<F>,
        mode: &mut CheckMode<F>,
        bit: &AssignedBit<F>,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;
        match mode {
            CheckMode::Assert => ng.assert_equal_to_fixed(layouter, bit, false),
            CheckMode::CollectFailures(failures) => {
                failures.push(bit.clone());
                Ok(())
            }
        }
    }

    /// Records that `x` must equal the constant `c`.
    fn record_eq_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        mode: &mut CheckMode<F>,
        x: &AssignedNative<F>,
        c: F,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;
        match mode {
            CheckMode::Assert => ng.assert_equal_to_fixed(layouter, x, c),
            CheckMode::CollectFailures(failures) => {
                let equal = ng.is_equal_to_fixed(layouter, x, c)?;
                failures.push(ng.not(layouter, &equal)?);
                Ok(())
            }
        }
    }

    /// Closes a verdict: `None` in asserting mode, otherwise the bit stating
    /// that no failure was recorded.
    fn finish(
        &self,
        layouter: &mut impl Layouter<F>,
        mode: CheckMode<F>,
    ) -> Result<Option<AssignedBit<F>>, Error> {
        match mode {
            CheckMode::Assert => Ok(None),
            CheckMode::CollectFailures(failures) => {
                // At most 3 terms per height, so the sum cannot wrap around
                // the field.
                let terms: Vec<(F, AssignedNative<F>)> =
                    failures.into_iter().map(|f| (F::ONE, f.0)).collect();
                let total = self.native_gadget.linear_combination(layouter, &terms, F::ZERO)?;
                self.native_gadget.is_zero(layouter, &total).map(Some)
            }
        }
    }

    /// Enforces the [AssignedMmr] invariants over an assigned size and
    /// assigned peaks: the size is linked to its `CAPACITY`-bit decomposition
    /// (hence range-checked) and the peaks at absent slots are set to zero.
    fn enforce_state_invariants<const CAPACITY: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        size: AssignedNative<F>,
        peaks: Vec<AssignedNative<F>>,
    ) -> Result<AssignedMmr<F, CAPACITY>, Error> {
        let size_bits: [AssignedBit<F>; CAPACITY] = self
            .native_gadget
            .assigned_to_le_bits(layouter, &size, Some(CAPACITY), true)?
            .try_into()
            .unwrap();

        let zero = self.native_gadget.assign_fixed(layouter, F::ZERO)?;
        let peaks: Vec<AssignedNative<F>> = size_bits
            .iter()
            .zip(peaks.iter())
            .map(|(bit, peak)| self.native_gadget.select(layouter, bit, peak, &zero))
            .collect::<Result<_, _>>()?;

        Ok(AssignedMmr {
            size,
            size_bits,
            peaks: peaks.try_into().unwrap(),
        })
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, N, H> FromScratch<F> for MmrGadget<F, N, H>
where
    F: CircuitField,
    N: NativeInstructions<F> + FromScratch<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
{
    type Config = (<N as FromScratch<F>>::Config, <H as FromScratch<F>>::Config);

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            native_gadget: N::new_from_scratch(&config.0),
            hash_chip: H::new_from_scratch(&config.1),
            _marker: PhantomData,
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        advice_columns: &mut Vec<Column<Advice>>,
        fixed_columns: &mut Vec<Column<Fixed>>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        (
            N::configure_from_scratch(meta, advice_columns, fixed_columns, instance_columns),
            H::configure_from_scratch(meta, advice_columns, fixed_columns, instance_columns),
        )
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)?;
        self.hash_chip.load_from_scratch(layouter)
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::Circuit,
    };

    use super::*;
    use crate::{
        field::{NativeChip, NativeGadget, decomposition::chip::P2RDecompositionChip},
        hash::poseidon::PoseidonChip,
        instructions::hash::HashCPU,
        mmr::cpu::Mmr,
        utils::circuit_modeling::{circuit_to_json, cost_measure_end, cost_measure_start},
    };

    const CAPACITY: usize = 5;
    type Ng<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    #[derive(Clone, Debug)]
    enum MmrTests {
        Assign,
        Prefix,
        Membership,
    }

    struct TestCircuit<F, N, H>
    where
        F: CircuitField,
        N: NativeInstructions<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
    {
        small: Value<MmrState<F, CAPACITY>>,
        big: Value<MmrState<F, CAPACITY>>,
        path: Value<SummitPath<F, CAPACITY>>,
        elem: Value<F>,
        membership: Value<MembershipProof<F, CAPACITY>>,
        mode: MmrTests,
        // None uses the asserting forms; Some(b) the verifying forms.
        verdict: Option<bool>,
        _marker: PhantomData<(N, H)>,
    }

    impl<F, N, H> Circuit<F> for TestCircuit<F, N, H>
    where
        F: CircuitField,
        N: NativeInstructions<F> + FromScratch<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        type Config = <MmrGadget<F, N, H> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                small: Value::unknown(),
                big: Value::unknown(),
                path: Value::unknown(),
                elem: Value::unknown(),
                membership: Value::unknown(),
                mode: self.mode.clone(),
                verdict: self.verdict,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            MmrGadget::<F, N, H>::configure_from_scratch(
                meta,
                &mut vec![],
                &mut vec![],
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = N::new_from_scratch(&config.0);
            let hash_chip = H::new_from_scratch(&config.1);
            let mmr_gadget = MmrGadget::<F, N, H>::new(&native_gadget, &hash_chip);

            match self.mode {
                MmrTests::Assign => {
                    let mmr = mmr_gadget.assign(&mut layouter, self.small)?;
                    mmr_gadget.constrain_as_public_input(&mut layouter, &mmr)?;

                    let cells = mmr.as_public_input();
                    assert_eq!(cells.len(), CAPACITY + 1);
                    self.small.map(|state| {
                        let expected =
                            <AssignedMmr<F, CAPACITY> as Instantiable<F>>::as_public_input(&state);
                        cells.iter().zip(expected).for_each(|(cell, expected)| {
                            cell.value().map(|v| assert_eq!(*v, expected));
                        });
                    });
                }
                MmrTests::Prefix => {
                    let small = mmr_gadget.assign(&mut layouter, self.small)?;
                    let big = mmr_gadget.assign(&mut layouter, self.big)?;
                    mmr_gadget.constrain_as_public_input(&mut layouter, &small)?;
                    mmr_gadget.constrain_as_public_input(&mut layouter, &big)?;

                    let path = mmr_gadget.assign_summit_path(&mut layouter, self.path)?;

                    cost_measure_start(&mut layouter);
                    match self.verdict {
                        None => mmr_gadget.assert_prefix(&mut layouter, &small, &big, &path)?,
                        Some(expected) => {
                            let ok = mmr_gadget.is_prefix(&mut layouter, &small, &big, &path)?;
                            native_gadget.assert_equal_to_fixed(&mut layouter, &ok, expected)?;
                        }
                    }
                    cost_measure_end(&mut layouter);
                }
                MmrTests::Membership => {
                    let mmr = mmr_gadget.assign(&mut layouter, self.small)?;
                    let elem = native_gadget.assign(&mut layouter, self.elem)?;
                    let proof =
                        mmr_gadget.assign_membership_proof(&mut layouter, self.membership)?;

                    cost_measure_start(&mut layouter);
                    match self.verdict {
                        None => mmr_gadget.assert_membership(&mut layouter, &mmr, &elem, &proof)?,
                        Some(expected) => {
                            let ok = mmr_gadget.is_member(&mut layouter, &mmr, &elem, &proof)?;
                            native_gadget.assert_equal_to_fixed(&mut layouter, &ok, expected)?;
                        }
                    }
                    cost_measure_end(&mut layouter);
                }
            }

            mmr_gadget.load_from_scratch(&mut layouter)
        }
    }

    /// Builds the MMRs over the leaves `first, first + 1, ...` of all sizes
    /// up to `max_size`.
    fn all_mmrs<F, H>(first: u64, max_size: u64) -> Vec<Mmr<F, H, CAPACITY>>
    where
        F: CircuitField,
        H: HashCPU<F, F>,
    {
        let mut mmrs = vec![Mmr::new()];
        for n in 0..max_size {
            let mut next = mmrs[n as usize].clone();
            next.append(F::from(first + n));
            mmrs.push(next);
        }
        mmrs
    }

    fn test_mmr_gadget<F, N, H>(cost_model: bool)
    where
        F: CircuitField + ff::FromUniformBytes<64> + Ord,
        N: NativeInstructions<F> + FromScratch<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        let mmrs = all_mmrs::<F, H>(0, 24);
        // Same sizes, different content: the leaves are shifted by one.
        let shifted_mmrs = all_mmrs::<F, H>(1, 4);

        let empty_path = SummitPath {
            steps: [F::ZERO; CAPACITY],
        };

        // (small, big, path, expect_ok, description).
        let prefix_cases = [
            // Only direct peak matches, no climb (8 = 0b1000, 11 = 0b1011).
            (
                &mmrs[8],
                &mmrs[11],
                mmrs[11].prove_prefix(8),
                true,
                "(8, 11)",
            ),
            // Identical MMRs.
            (
                &mmrs[11],
                &mmrs[11],
                mmrs[11].prove_prefix(11),
                true,
                "(11, 11)",
            ),
            // Climb absorbing both witnessed steps and own peaks.
            (
                &mmrs[3],
                &mmrs[11],
                mmrs[11].prove_prefix(3),
                true,
                "(3, 11)",
            ),
            // Full climb along the left spine of a single mountain.
            (&mmrs[7], &mmrs[8], mmrs[8].prove_prefix(7), true, "(7, 8)"),
            // The empty MMR is a prefix of any MMR.
            (
                &mmrs[0],
                &mmrs[11],
                mmrs[11].prove_prefix(0),
                true,
                "(0, 11)",
            ),
            // Direct match at the top slot (bit CAPACITY - 1) plus a climb.
            (
                &mmrs[20],
                &mmrs[24],
                mmrs[24].prove_prefix(20),
                true,
                "(20, 24)",
            ),
            // Tampered (consumed) witness step.
            (
                &mmrs[3],
                &mmrs[11],
                {
                    let mut path = mmrs[11].prove_prefix(3);
                    path.steps[0] += F::ONE;
                    path
                },
                false,
                "(3, 11) with a tampered step",
            ),
            // A longer MMR is not a prefix of a shorter one.
            (&mmrs[11], &mmrs[3], empty_path, false, "(11, 3)"),
            // Same sizes, different content.
            (
                &shifted_mmrs[3],
                &mmrs[11],
                mmrs[11].prove_prefix(3),
                false,
                "(3, 11) with mismatching content",
            ),
            // Different content, detected at the climb landing.
            (
                &shifted_mmrs[1],
                &mmrs[2],
                mmrs[2].prove_prefix(1),
                false,
                "(1, 2) with mismatching content",
            ),
        ];

        for (small, big, path, expect_ok, description) in prefix_cases.into_iter() {
            // Each case runs through the asserting form (accepted exactly on
            // the true cases) and through the verifying form twice: asserting
            // the true verdict must satisfy the circuit, asserting its
            // negation must not — which is what shows the returned bit is
            // constrained rather than merely witnessed.
            for verdict in [None, Some(expect_ok), Some(!expect_ok)] {
                let circuit = TestCircuit::<F, N, H> {
                    small: Value::known(small.state()),
                    big: Value::known(big.state()),
                    path: Value::known(path),
                    elem: Value::unknown(),
                    membership: Value::unknown(),
                    mode: MmrTests::Prefix,
                    verdict,
                    _marker: PhantomData,
                };

                let pi = [
                    <AssignedMmr<F, CAPACITY> as Instantiable<F>>::as_public_input(&small.state()),
                    <AssignedMmr<F, CAPACITY> as Instantiable<F>>::as_public_input(&big.state()),
                ]
                .concat();

                let accepts = match verdict {
                    None => expect_ok,
                    Some(expected) => expected == expect_ok,
                };
                let prover = MockProver::run(&circuit, vec![vec![], pi]).unwrap();
                if accepts {
                    assert!(
                        prover.verify().is_ok(),
                        "prefix case {description} (verdict {verdict:?}) rejected"
                    );
                } else {
                    assert!(
                        prover.verify().is_err(),
                        "prefix case {description} (verdict {verdict:?}) accepted"
                    );
                }

                if cost_model && verdict.is_none() && description == "(3, 11)" {
                    circuit_to_json::<F>("MMR gadget", "Prefix", circuit);
                }
            }
        }

        // Assignment and public-input encoding: the honest state passes and
        // any tampered public input is rejected. In particular, tampering
        // with the (zero) entry of an absent slot must fail: the assignment
        // canonicalizes absent peaks to zero.
        let state = mmrs[11].state();
        let pi = <AssignedMmr<F, CAPACITY> as Instantiable<F>>::as_public_input(&state);
        // 11 = 0b01011: slot 2 is absent (entry 3 of the public input).
        let absent_slot_entry = 1 + 2;
        for tampered_entry in [None, Some(1), Some(absent_slot_entry)] {
            let circuit = TestCircuit::<F, N, H> {
                small: Value::known(state),
                big: Value::unknown(),
                path: Value::unknown(),
                elem: Value::unknown(),
                membership: Value::unknown(),
                mode: MmrTests::Assign,
                verdict: None,
                _marker: PhantomData,
            };
            let mut pi = pi.clone();
            if let Some(entry) = tampered_entry {
                pi[entry] += F::ONE;
            }
            let prover = MockProver::run(&circuit, vec![vec![], pi]).unwrap();
            if tampered_entry.is_none() {
                assert!(prover.verify().is_ok(), "honest assignment rejected");
            } else {
                assert!(
                    prover.verify().is_err(),
                    "tampered public input ({tampered_entry:?}) accepted"
                );
            }
        }
    }

    fn test_mmr_membership<F, N, H>(cost_model: bool)
    where
        F: CircuitField + ff::FromUniformBytes<64> + Ord,
        N: NativeInstructions<F> + FromScratch<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        // 22 = 0b10110: mountains of heights 4, 2 and 1 (the height-0 mountain
        // is absent).
        let n = 22u64;
        let mmr = &all_mmrs::<F, H>(0, n)[n as usize];
        let leaves: Vec<F> = (0..n).map(F::from).collect();
        let state = mmr.state();

        // (elem, proof, expect_ok, description).
        let mut cases: Vec<(F, MembershipProof<F, CAPACITY>, bool, String)> = vec![
            (
                leaves[0],
                mmr.prove_membership(0),
                true,
                "oldest (tallest mountain)".into(),
            ),
            (
                leaves[7],
                mmr.prove_membership(7),
                true,
                "interior of the tallest".into(),
            ),
            (
                leaves[16],
                mmr.prove_membership(16),
                true,
                "in a smaller mountain".into(),
            ),
            (
                leaves[(n - 1) as usize],
                mmr.prove_membership(n - 1),
                true,
                "newest".into(),
            ),
        ];

        // Wrong element against an honest path.
        cases.push((
            leaves[0] + F::ONE,
            mmr.prove_membership(0),
            false,
            "wrong element".into(),
        ));

        // Tampered sibling.
        let mut proof = mmr.prove_membership(5);
        proof.siblings[0] += F::ONE;
        cases.push((leaves[5], proof, false, "tampered sibling".into()));

        // Flipped direction bit selects the wrong subtree.
        let mut proof = mmr.prove_membership(5);
        proof.leaf_index ^= 1;
        cases.push((leaves[5], proof, false, "flipped direction bit".into()));

        // Height pointing at the absent height-0 mountain.
        let mut proof = mmr.prove_membership(0);
        proof.height = 0;
        cases.push((leaves[0], proof, false, "absent mountain".into()));

        for (elem, proof, expect_ok, description) in cases.into_iter() {
            // Each case runs through the asserting form (accepted exactly on
            // the true cases) and through the verifying form twice: asserting
            // the true verdict must satisfy the circuit, asserting its
            // negation must not — which is what shows the returned bit is
            // constrained rather than merely witnessed.
            for verdict in [None, Some(expect_ok), Some(!expect_ok)] {
                let circuit = TestCircuit::<F, N, H> {
                    small: Value::known(state),
                    big: Value::unknown(),
                    path: Value::unknown(),
                    elem: Value::known(elem),
                    membership: Value::known(proof),
                    mode: MmrTests::Membership,
                    verdict,
                    _marker: PhantomData,
                };
                let accepts = match verdict {
                    None => expect_ok,
                    Some(expected) => expected == expect_ok,
                };
                let prover = MockProver::run(&circuit, vec![vec![], vec![]]).unwrap();
                if accepts {
                    assert!(
                        prover.verify().is_ok(),
                        "membership case {description} (verdict {verdict:?}) rejected"
                    );
                } else {
                    assert!(
                        prover.verify().is_err(),
                        "membership case {description} (verdict {verdict:?}) accepted"
                    );
                }

                if cost_model && verdict.is_none() && description == "oldest (tallest mountain)" {
                    circuit_to_json::<F>("MMR gadget", "Membership", circuit);
                }
            }
        }

        // An index hint beyond CAPACITY bits keeps only its low bits, so it is
        // just a wrong hint and the verdict is false.
        let mut proof = mmr.prove_membership(5);
        proof.leaf_index = u64::MAX;
        for verdict in [None, Some(true), Some(false)] {
            let circuit = TestCircuit::<F, N, H> {
                small: Value::known(state),
                big: Value::unknown(),
                path: Value::unknown(),
                elem: Value::known(leaves[5]),
                membership: Value::known(proof),
                mode: MmrTests::Membership,
                verdict,
                _marker: PhantomData,
            };
            let prover = MockProver::run(&circuit, vec![vec![], vec![]]).unwrap();
            if verdict == Some(false) {
                assert!(
                    prover.verify().is_ok(),
                    "out-of-range leaf index (verdict {verdict:?}) rejected"
                );
            } else {
                assert!(
                    prover.verify().is_err(),
                    "out-of-range leaf index (verdict {verdict:?}) accepted"
                );
            }
        }
    }

    #[test]
    fn test_mmr_state_public_input_roundtrip() {
        type F = midnight_curves::Fq;
        type H = PoseidonChip<F>;

        let state = all_mmrs::<F, H>(0, 11)[11].state();
        let pi = <AssignedMmr<F, CAPACITY> as Instantiable<F>>::as_public_input(&state);
        assert_eq!(pi.len(), CAPACITY + 1);
        assert_eq!(AssignedMmr::<F, CAPACITY>::from_public_input(&pi), Some(state));

        // Wrong length.
        assert_eq!(AssignedMmr::<F, CAPACITY>::from_public_input(&pi[1..]), None);

        // Nonzero peak at an absent slot (11 = 0b01011: slot 2 is absent).
        let mut tampered = pi.clone();
        tampered[1 + 2] = F::ONE;
        assert_eq!(AssignedMmr::<F, CAPACITY>::from_public_input(&tampered), None);

        // Size out of range.
        let mut tampered = pi.clone();
        tampered[0] = F::from(1 << CAPACITY);
        assert_eq!(AssignedMmr::<F, CAPACITY>::from_public_input(&tampered), None);
    }

    #[test]
    fn test_mmr_gadget_poseidon() {
        type F = midnight_curves::Fq;
        test_mmr_gadget::<F, Ng<F>, PoseidonChip<F>>(true);
    }

    #[test]
    fn test_mmr_membership_poseidon() {
        type F = midnight_curves::Fq;
        test_mmr_membership::<F, Ng<F>, PoseidonChip<F>>(true);
    }
}

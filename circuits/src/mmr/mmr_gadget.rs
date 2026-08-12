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
    instructions::{HashInstructions, NativeInstructions},
    mmr::cpu::{MmrState, SummitPath},
    types::{AssignedBit, AssignedNative, InnerValue, Instantiable},
    CircuitField,
};

/// An assigned Merkle Mountain Range state (see [MmrState]).
///
/// The following invariants are enforced at construction:
/// - `size` equals `sum_i size_bits[i] * 2^i` (in particular, the size is
///   range-checked to be smaller than `2^SIZE`),
/// - `peaks[i]` is zero whenever `size_bits[i]` is zero (canonical encoding of
///   absent mountains).
#[derive(Clone, Debug)]
pub struct AssignedMmr<F: CircuitField, const SIZE: usize> {
    pub(crate) size: AssignedNative<F>,
    pub(crate) size_bits: [AssignedBit<F>; SIZE],
    pub(crate) peaks: [AssignedNative<F>; SIZE],
}

impl<F: CircuitField, const SIZE: usize> InnerValue for AssignedMmr<F, SIZE> {
    type Element = MmrState<F, SIZE>;

    fn value(&self) -> Value<MmrState<F, SIZE>> {
        let size = self.size.value().copied();
        let peaks = self.peaks.value();
        size.zip(peaks).map(|(size, peaks)| MmrState {
            size: u64::try_from(size.to_biguint()).expect("MMR size fits in u64"),
            peaks,
        })
    }
}

impl<F: CircuitField, const SIZE: usize> Instantiable<F> for AssignedMmr<F, SIZE> {
    fn as_public_input(element: &MmrState<F, SIZE>) -> Vec<F> {
        let mut public_input = vec![F::from(element.size)];
        public_input.extend(element.peaks);
        public_input
    }

    #[cfg(any(test, feature = "testing"))]
    fn from_public_input(fields: &[F]) -> Option<MmrState<F, SIZE>> {
        if fields.len() != SIZE + 1 {
            return None;
        }
        let size = u64::try_from(fields[0].to_biguint()).ok()?;
        if SIZE < 64 && size >= (1u64 << SIZE) {
            return None;
        }
        let peaks: [F; SIZE] = fields[1..].try_into().ok()?;
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
pub struct AssignedSummitPath<F: CircuitField, const SIZE: usize> {
    pub(crate) steps: [AssignedNative<F>; SIZE],
}

impl<F: CircuitField, const SIZE: usize> InnerValue for AssignedSummitPath<F, SIZE> {
    type Element = SummitPath<F, SIZE>;

    fn value(&self) -> Value<SummitPath<F, SIZE>> {
        self.steps.value().map(|steps| SummitPath { steps })
    }
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
    /// invariants: the assigned size is range-checked to `SIZE` bits and the
    /// peaks at absent slots are (re)set to zero.
    pub fn assign<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        state: Value<MmrState<F, SIZE>>,
    ) -> Result<AssignedMmr<F, SIZE>, Error> {
        let size = self.native_gadget.assign(layouter, state.map(|s| F::from(s.size)))?;
        let peaks = state.map(|s| s.peaks).transpose_array();
        let peaks = self.native_gadget.assign_many(layouter, &peaks)?;
        self.enforce_state_invariants(layouter, size, peaks)
    }

    /// Assigns a fixed (constant) MMR state.
    pub fn assign_fixed<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        state: MmrState<F, SIZE>,
    ) -> Result<AssignedMmr<F, SIZE>, Error> {
        let size = self.native_gadget.assign_fixed(layouter, F::from(state.size))?;
        let peaks = self.native_gadget.assign_many_fixed(layouter, &state.peaks)?;
        self.enforce_state_invariants(layouter, size, peaks)
    }

    /// Assigns the state of the empty MMR.
    pub fn assign_empty<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<AssignedMmr<F, SIZE>, Error> {
        self.assign_fixed(
            layouter,
            MmrState {
                size: 0,
                peaks: [F::ZERO; SIZE],
            },
        )
    }

    /// Constrains the given MMR state as a public input, in the order of
    /// [AssignedMmr::as_public_input]: the size followed by the peaks.
    pub fn constrain_as_public_input<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        mmr: &AssignedMmr<F, SIZE>,
    ) -> Result<(), Error> {
        self.native_gadget.constrain_as_public_input(layouter, &mmr.size)?;
        (mmr.peaks.iter())
            .try_for_each(|peak| self.native_gadget.constrain_as_public_input(layouter, peak))
    }

    /// Assigns a [SummitPath] as a private input.
    ///
    /// The path is not constrained in any way: its steps get verified when
    /// consumed by [Self::assert_prefix].
    pub fn assign_summit_path<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        path: Value<SummitPath<F, SIZE>>,
    ) -> Result<AssignedSummitPath<F, SIZE>, Error> {
        let steps = path.map(|p| p.steps).transpose_array();
        let steps = self.native_gadget.assign_many(layouter, &steps)?;
        Ok(AssignedSummitPath {
            steps: steps.try_into().unwrap(),
        })
    }

    /// Asserts that the elements of the MMR with state `small` are a prefix
    /// of the elements of the MMR with state `big`, given a summit path
    /// witness (produced off-circuit with
    /// [Mmr::prove_prefix](crate::mmr::cpu::Mmr::prove_prefix) on the big
    /// MMR).
    ///
    /// This is the in-circuit counterpart of
    /// [Mmr::verify_prefix](crate::mmr::cpu::Mmr::verify_prefix), which
    /// specifies the constraints implemented here.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If `small` is not a prefix of `big` (in particular, whenever
    /// `small.size > big.size`), or if the summit path steps are incorrect.
    pub fn assert_prefix<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        small: &AssignedMmr<F, SIZE>,
        big: &AssignedMmr<F, SIZE>,
        path: &AssignedSummitPath<F, SIZE>,
    ) -> Result<(), Error> {
        let ng = &self.native_gadget;
        let a_bits = &small.size_bits;
        let b_bits = &big.size_bits;

        // agree[i]: the two sizes agree on all bits at positions >= i
        // (computed top-down; agree[SIZE] is trivially true).
        let mut agree: Vec<AssignedBit<F>> = Vec::with_capacity(SIZE + 1);
        agree.push(ng.assign_fixed(layouter, true)?);
        for i in (0..SIZE).rev() {
            let bits_equal = ng.is_equal(layouter, &a_bits[i], &b_bits[i])?;
            let and = ng.and(layouter, &[agree.last().unwrap().clone(), bits_equal])?;
            agree.push(and);
        }
        agree.reverse();

        // started[i]: the small MMR has a peak at some height < i, i.e. the
        // climb is underway when reaching height i.
        let mut started: Vec<AssignedBit<F>> = Vec::with_capacity(SIZE + 1);
        started.push(ng.assign_fixed(layouter, false)?);
        for a_bit in a_bits.iter() {
            let or = ng.or(layouter, &[started.last().unwrap().clone(), a_bit.clone()])?;
            started.push(or);
        }

        // The climbing node; its initial value is irrelevant (it is never
        // consumed before being overwritten by a starting peak).
        let mut cur: AssignedNative<F> = ng.assign_fixed(layouter, F::ZERO)?;

        for i in 0..SIZE {
            // The sizes agree above height i and both MMRs have a mountain
            // here: their peaks must match directly.
            let direct_match = ng.and(
                layouter,
                &[agree[i + 1].clone(), a_bits[i].clone(), b_bits[i].clone()],
            )?;
            ng.cond_assert_equal(layouter, &direct_match, &small.peaks[i], &big.peaks[i])?;

            // fin: highest bit where the sizes differ (at most one height).
            let bits_differ = ng.xor(layouter, &[a_bits[i].clone(), b_bits[i].clone()])?;
            let fin = ng.and(layouter, &[agree[i + 1].clone(), bits_differ])?;

            // At said height, the small size must have the unset bit;
            // otherwise small > big and it cannot be a prefix.
            let violation = ng.and(layouter, &[fin.clone(), a_bits[i].clone()])?;
            ng.assert_equal_to_fixed(layouter, &violation, false)?;

            // The climb starts at the lowest peak of the small MMR.
            let not_started = ng.not(layouter, &started[i])?;
            let is_start = ng.and(layouter, &[a_bits[i].clone(), not_started])?;
            let input = ng.select(layouter, &is_start, &small.peaks[i], &cur)?;

            // If a climb took place, it must land exactly on big's peak at
            // the height of the first size disagreement.
            let must_land = ng.and(layouter, &[fin, started[i].clone()])?;
            ng.cond_assert_equal(layouter, &must_land, &input, &big.peaks[i])?;

            // Climb one level up: the node at height i is combined either
            // with small's own peak at this height (as left sibling) or with
            // a witnessed node of the big MMR (as right sibling). The top
            // height never climbs.
            if i < SIZE - 1 {
                let absorb_own_peak = ng.and(layouter, &[a_bits[i].clone(), started[i].clone()])?;
                let left = ng.select(layouter, &absorb_own_peak, &small.peaks[i], &input)?;
                let right = ng.select(layouter, &absorb_own_peak, &input, &path.steps[i])?;
                let hash = self.hash_chip.hash(layouter, &[left, right])?;

                let not_agree = ng.not(layouter, &agree[i + 1])?;
                let climbing = ng.and(layouter, &[started[i + 1].clone(), not_agree])?;
                cur = ng.select(layouter, &climbing, &hash, &input)?;
            }
        }

        Ok(())
    }

    /// Enforces the [AssignedMmr] invariants over an assigned size and
    /// assigned peaks: the size is linked to its `SIZE`-bit decomposition
    /// (hence range-checked) and the peaks at absent slots are set to zero.
    fn enforce_state_invariants<const SIZE: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        size: AssignedNative<F>,
        peaks: Vec<AssignedNative<F>>,
    ) -> Result<AssignedMmr<F, SIZE>, Error> {
        let size_bits: [AssignedBit<F>; SIZE] = self
            .native_gadget
            .assigned_to_le_bits(layouter, &size, Some(SIZE), true)?
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
        field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
        hash::poseidon::{constants::PoseidonField, PoseidonChip},
        mmr::cpu::Mmr,
        utils::circuit_modeling::{circuit_to_json, cost_measure_end, cost_measure_start},
    };

    const SIZE: usize = 5;

    #[derive(Clone, Debug)]
    enum MmrTests {
        Assign,
        Prefix,
    }

    struct TestCircuit<F, N, H>
    where
        F: CircuitField,
        N: NativeInstructions<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
    {
        small: Value<MmrState<F, SIZE>>,
        big: Value<MmrState<F, SIZE>>,
        path: Value<SummitPath<F, SIZE>>,
        mode: MmrTests,
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
                mode: self.mode.clone(),
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
                }
                MmrTests::Prefix => {
                    let small = mmr_gadget.assign(&mut layouter, self.small)?;
                    let big = mmr_gadget.assign(&mut layouter, self.big)?;
                    mmr_gadget.constrain_as_public_input(&mut layouter, &small)?;
                    mmr_gadget.constrain_as_public_input(&mut layouter, &big)?;

                    let path = mmr_gadget.assign_summit_path(&mut layouter, self.path.clone())?;

                    cost_measure_start(&mut layouter);
                    mmr_gadget.assert_prefix(&mut layouter, &small, &big, &path)?;
                    cost_measure_end(&mut layouter);
                }
            }

            mmr_gadget.load_from_scratch(&mut layouter)
        }
    }

    /// Builds the MMRs over the leaves `first, first + 1, ...` of all sizes
    /// up to `max_size`.
    fn all_mmrs<F, H>(first: u64, max_size: u64) -> Vec<Mmr<F, H, SIZE>>
    where
        F: CircuitField,
        H: crate::instructions::hash::HashCPU<F, F>,
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
            steps: [F::ZERO; SIZE],
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
            // Direct match at the top slot (bit SIZE - 1) plus a climb.
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
            (&mmrs[11], &mmrs[3], empty_path.clone(), false, "(11, 3)"),
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
            let circuit = TestCircuit::<F, N, H> {
                small: Value::known(small.state()),
                big: Value::known(big.state()),
                path: Value::known(path),
                mode: MmrTests::Prefix,
                _marker: PhantomData,
            };

            let pi = [
                AssignedMmr::<F, SIZE>::as_public_input(&small.state()),
                AssignedMmr::<F, SIZE>::as_public_input(&big.state()),
            ]
            .concat();

            let prover = MockProver::run(&circuit, vec![vec![], pi]).unwrap();
            if expect_ok {
                assert!(
                    prover.verify().is_ok(),
                    "prefix case {description} rejected"
                );
            } else {
                assert!(
                    prover.verify().is_err(),
                    "prefix case {description} accepted"
                );
            }

            if cost_model && description == "(3, 11)" {
                circuit_to_json::<F>("MMR gadget", "Prefix", circuit);
            }
        }

        // Assignment and public-input encoding: the honest state passes and
        // any tampered public input is rejected. In particular, tampering
        // with the (zero) entry of an absent slot must fail: the assignment
        // canonicalizes absent peaks to zero.
        let state = mmrs[11].state();
        let pi = AssignedMmr::<F, SIZE>::as_public_input(&state);
        // 11 = 0b01011: slot 2 is absent (entry 3 of the public input).
        let absent_slot_entry = 1 + 2;
        for tampered_entry in [None, Some(1), Some(absent_slot_entry)] {
            let circuit = TestCircuit::<F, N, H> {
                small: Value::known(state),
                big: Value::unknown(),
                path: Value::unknown(),
                mode: MmrTests::Assign,
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

    #[test]
    fn test_mmr_state_public_input_roundtrip() {
        type F = midnight_curves::Fq;
        type H = PoseidonChip<F>;

        let state = all_mmrs::<F, H>(0, 11)[11].state();
        let pi = AssignedMmr::<F, SIZE>::as_public_input(&state);
        assert_eq!(pi.len(), SIZE + 1);
        assert_eq!(AssignedMmr::<F, SIZE>::from_public_input(&pi), Some(state));

        // Wrong length.
        assert_eq!(AssignedMmr::<F, SIZE>::from_public_input(&pi[1..]), None);

        // Nonzero peak at an absent slot (11 = 0b01011: slot 2 is absent).
        let mut tampered = pi.clone();
        tampered[1 + 2] = F::ONE;
        assert_eq!(AssignedMmr::<F, SIZE>::from_public_input(&tampered), None);

        // Size out of range.
        let mut tampered = pi.clone();
        tampered[0] = F::from(1 << SIZE);
        assert_eq!(AssignedMmr::<F, SIZE>::from_public_input(&tampered), None);
    }

    fn run_poseidon_test<F: PoseidonField + ff::FromUniformBytes<64> + Ord>(cost_model: bool) {
        test_mmr_gadget::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>, PoseidonChip<F>>(
            cost_model,
        )
    }

    #[test]
    fn test_mmr_gadget_poseidon() {
        run_poseidon_test::<midnight_curves::Fq>(true);
    }
}

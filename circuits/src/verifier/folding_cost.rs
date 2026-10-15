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

//! Row counts of [`FoldingGadget`] (cost model, no witnesses), for the test
//! relation and for synthetic shapes with the counts of the IVC relation.
//! Run with
//! `cargo test --release -p midnight-circuits --lib folding_gadget_costs --
//! --ignored --nocapture`.
//!
//! The fresh instance is read by the same transcript operations as
//! `VerifierGadget::parse_trace` (vk representation, public inputs, phase-1
//! points, `θ⃗, β, γ, trash`, phase-2 points, `y⃗`), so that relations we
//! cannot build here (the IVC step circuit) can be measured from their
//! counts alone.

use ff::{Field, PrimeField};
use group::Group;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::cost_model::circuit_model,
    plonk::{Circuit, ConstraintSystem, Error},
    poly::PolynomialLabel,
};

use super::folding_test::{Chips, ChipsConfig, F, Native, S, chips, configure_chips};
use crate::{
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
        hash::HashInstructions,
    },
    types::ComposableChip,
    utils::circuit_modeling::{cost_measure_end, cost_measure_start},
    verifier::{
        AssignedKZGCommitment, AssignedKZGMultiCommitment, FoldingGadget, FoldingShape,
        InCircuitPCS, SelfEmulation,
        folding_types::{
            AssignedChallenges, AssignedFoldingAccumulator, AssignedFoldingInstance, points,
        },
        transcript_gadget::TranscriptGadget,
        utils::AssignedBoundedScalar,
    },
};

type CS = <<S as SelfEmulation>::PCS as InCircuitPCS<S>>::OffCircuitPCS;
type C = <S as SelfEmulation>::C;

/// The part of the circuit whose rows are reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Window {
    /// The whole circuit (no markers).
    All,
    /// Reading the fresh instance (replaying its transcript).
    Replay,
    /// Assigning the previous accumulator.
    AssignAcc,
    /// `init` (genesis).
    Init,
    /// `fold` without the commitment folding.
    FoldScalars,
    /// The commitment folding of `fold` (naive or optimistic).
    FoldCommitments,
    /// Hashing the output accumulator once (Poseidon).
    Hash,
}

#[derive(Clone, Debug)]
struct CostCircuit {
    shape: FoldingShape,
    window: Window,
    init: bool,
    optimistic: bool,
}

impl CostCircuit {
    fn rows(shape: &FoldingShape, window: Window, init: bool, optimistic: bool) -> (usize, u32) {
        let circuit = CostCircuit {
            shape: shape.clone(),
            window,
            init,
            optimistic,
        };
        let model = circuit_model::<F, CS>(&circuit, 0);
        (model.rows, model.k)
    }
}

/// Reads a fresh instance of `shape` with the transcript operations of
/// `parse_trace`, from an unknown partial proof.
fn replay(
    layouter: &mut impl Layouter<F>,
    chips: &Chips,
    shape: &FoldingShape,
) -> Result<AssignedFoldingInstance<S>, Error> {
    let mut transcript = TranscriptGadget::<S>::new(&chips.scalar, &chips.curve, &chips.sponge);
    transcript.init_with_proof(layouter, Value::unknown())?;
    let vk_repr = chips.scalar.assign(layouter, Value::unknown())?;
    transcript.common_scalar(layouter, &vk_repr)?;
    let mut instances = Vec::new();
    for len in &shape.instance_lens {
        let n = chips.scalar.assign_fixed(layouter, F::from(*len as u64))?;
        transcript.common_scalar(layouter, &n)?;
        let pis = (0..*len)
            .map(|_| chips.scalar.assign(layouter, Value::unknown()))
            .collect::<Result<Vec<_>, Error>>()?;
        pis.iter().try_for_each(|pi| transcript.common_scalar(layouter, pi))?;
        instances.push(pis);
    }
    let phase1 = transcript.read_commitment(layouter, &shape.phase1_labels)?;
    let mut challenges = transcript.squeeze_challenges(layouter, shape.nb_theta + 3)?;
    let phase2 = transcript.read_commitment(layouter, &shape.phase2_labels)?;
    challenges.extend(transcript.squeeze_challenges(layouter, shape.nb_y)?);
    Ok(AssignedFoldingInstance {
        phase1,
        phase2,
        instances,
        challenges: AssignedChallenges::from_scalars(shape, challenges.into_iter()),
    })
}

/// Plan 5.5 (ablation, not the protocol): witness `A_i = [γ](C_i − acc_i)`,
/// absorb them, squeeze `ρ_i` (`ρ_1 = 1`), check
/// `Σ ρ_i A_i − Σ (γρ_i) D_i = 0` with one MSM, and set `acc_i' = acc_i + A_i`.
fn fold_commitments_optimistic(
    layouter: &mut impl Layouter<F>,
    chips: &Chips,
    acc: &AssignedFoldingAccumulator<S>,
    fresh: &AssignedFoldingInstance<S>,
    gamma: &AssignedBoundedScalar<F>,
) -> Result<Vec<<S as SelfEmulation>::AssignedPoint>, Error> {
    let curve = &chips.curve;
    let acc_points = points(&acc.instance.phase1)?.into_iter().chain(points(&acc.instance.phase2)?);
    let fresh_points = points(&fresh.phase1)?.into_iter().chain(points(&fresh.phase2)?);
    let mut transcript = TranscriptGadget::<S>::new(&chips.scalar, curve, &chips.sponge);
    transcript.init_with_proof(layouter, Value::unknown())?;

    let (mut scalars, mut bases, mut out) = (Vec::new(), Vec::new(), Vec::new());
    for (i, ((a, label), (c, _))) in acc_points.zip(fresh_points).enumerate() {
        let witness = S::assign_without_subgroup_check(layouter, curve, Value::unknown())?;
        let com = AssignedKZGMultiCommitment(vec![AssignedKZGCommitment::simple(
            witness.clone(),
            label.clone(),
        )]);
        transcript.common_commitment(layouter, &com)?;
        let rho = if i == 0 {
            AssignedBoundedScalar::one(layouter, &chips.scalar)?
        } else {
            let rho = transcript.squeeze_challenge(layouter)?;
            #[cfg(feature = "truncated-challenges")]
            let rho = crate::verifier::utils::truncate::<F>(layouter, &chips.scalar, &rho)?;
            #[cfg(not(feature = "truncated-challenges"))]
            let rho = AssignedBoundedScalar::new(&rho, None);
            rho
        };
        let minus_a = S::negate(layouter, curve, a)?;
        let diff = S::add(layouter, curve, c, &minus_a)?;
        let minus_gamma_rho =
            chips.scalar.mul(layouter, &gamma.scalar, &rho.scalar, Some(-F::ONE))?;
        scalars.push((rho.scalar.clone(), rho.bound.bits() as usize));
        bases.push(witness.clone());
        scalars.push((minus_gamma_rho, F::NUM_BITS as usize));
        bases.push(diff);
        out.push(S::add(layouter, curve, a, &witness)?);
    }
    let check = S::msm(layouter, curve, &scalars, &bases)?;
    curve.assert_equal_to_fixed(layouter, &check, C::identity())?;
    Ok(out)
}

impl Circuit<F> for CostCircuit {
    type Config = ChipsConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        configure_chips(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chips = chips(&config);
        let gadget = FoldingGadget::<S>::new(
            &chips.curve,
            &chips.scalar,
            &chips.sponge,
            self.shape.clone(),
        );
        let layouter = &mut layouter;
        let start = |w: Window, l: &mut _| {
            if self.window == w {
                cost_measure_start::<F>(l)
            }
        };
        let end = |w: Window, l: &mut _| {
            if self.window == w {
                cost_measure_end::<F>(l)
            }
        };

        start(Window::Replay, layouter);
        let fresh = replay(layouter, &chips, &self.shape)?;
        end(Window::Replay, layouter);

        let next = if self.init {
            start(Window::Init, layouter);
            let next = gadget.init(layouter, fresh)?;
            end(Window::Init, layouter);
            next
        } else {
            start(Window::AssignAcc, layouter);
            let acc = gadget.assign_accumulator(layouter, Value::unknown())?;
            end(Window::AssignAcc, layouter);

            start(Window::FoldScalars, layouter);
            let (mut next, gamma) =
                gadget.fold_scalars(layouter, &acc, &fresh, Value::unknown())?;
            end(Window::FoldScalars, layouter);

            start(Window::FoldCommitments, layouter);
            if self.optimistic {
                fold_commitments_optimistic(layouter, &chips, &acc, &fresh, &gamma)?;
            } else {
                let (a, f) = (&acc.instance, &fresh);
                next.instance.phase1 =
                    gadget.fold_commitment(layouter, &a.phase1, &f.phase1, &gamma)?;
                next.instance.phase2 =
                    gadget.fold_commitment(layouter, &a.phase2, &f.phase2, &gamma)?;
            }
            end(Window::FoldCommitments, layouter);
            next
        };

        start(Window::Hash, layouter);
        let inputs = next.as_public_input(layouter, &chips.curve)?;
        let digest = chips.sponge.hash(layouter, &inputs)?;
        end(Window::Hash, layouter);
        chips.scalar.constrain_as_public_input(layouter, &digest)?;
        chips.core_decomp.load(layouter)
    }
}

/// Prints the row counts of one `init` and one `fold` for `shape`.
fn report(name: &str, shape: &FoldingShape) {
    let rows = |w, init, optimistic| CostCircuit::rows(shape, w, init, optimistic).0;
    let (fold_total, k) = CostCircuit::rows(shape, Window::All, false, false);
    let (init_total, init_k) = CostCircuit::rows(shape, Window::All, true, false);
    let commitments = rows(Window::FoldCommitments, false, false);
    let c = shape.nb_points();
    println!(
        "{name}: log n {}, d_total {}, c_var {c}, |PI| {}, nb_theta {}, nb_y {}",
        shape.log_n,
        shape.d_total,
        shape.instance_lens.iter().sum::<usize>(),
        shape.nb_theta,
        shape.nb_y
    );
    println!(
        "  fold circuit total {fold_total} (k = {k}); init circuit total {init_total} (k = {init_k})"
    );
    println!(
        "  replay fresh {}; assign acc {}; init {}; fold scalars {}; fold commitments {commitments} \
         ({} per point); hash output {}",
        rows(Window::Replay, false, false),
        rows(Window::AssignAcc, false, false),
        rows(Window::Init, true, false),
        rows(Window::FoldScalars, false, false),
        commitments / c,
        rows(Window::Hash, false, false),
    );
    println!(
        "  fold circuit without commitment folding {}; optimistic commitment folding {}",
        fold_total - commitments,
        rows(Window::FoldCommitments, false, true),
    );
}

#[test]
#[ignore]
fn folding_gadget_costs() {
    let truncated = cfg!(feature = "truncated-challenges");
    println!("truncated-challenges: {truncated}");
    report(
        "test relation (SquareCircuit, k = 6)",
        &Native::new().shape(),
    );
    let ivc = |c| FoldingShape::synthetic(16, 13, c, &[2], (16, 50));
    report("IVC shape, T_MAX = 8 (synthetic)", &ivc((3, 2)));
    report("IVC shape, T_MAX = 16 (synthetic)", &ivc((2, 1)));
}

impl FoldingShape {
    /// A shape given by its counts only, with `c1` + `c2` commitment chunks.
    fn synthetic(
        log_n: usize,
        d_total: usize,
        (c1, c2): (usize, usize),
        instance_lens: &[usize],
        (nb_theta, nb_y): (usize, usize),
    ) -> Self {
        let labels = |phase, c| (0..c).map(move |i| PolynomialLabel::Custom(format!("{phase}{i}")));
        Self {
            log_n,
            d_total,
            phase1_labels: labels(1, c1).collect(),
            phase2_labels: labels(2, c2).collect(),
            instance_lens: instance_lens.to_vec(),
            nb_theta,
            nb_y,
        }
    }
}

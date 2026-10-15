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

use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::cost_model::circuit_model,
    plonk::{Circuit, ConstraintSystem, Error},
    poly::PolynomialLabel,
};

use super::folding_test::{Chips, ChipsConfig, F, Native, S, chips, configure_chips};
use crate::{
    instructions::{AssignmentInstructions, PublicInputInstructions, hash::HashInstructions},
    types::ComposableChip,
    utils::circuit_modeling::{cost_measure_end, cost_measure_start},
    verifier::{
        FoldingGadget, FoldingShape, InCircuitPCS, SelfEmulation,
        folding_types::{AssignedChallenges, AssignedFoldingInstance, trash_powers},
        transcript_gadget::TranscriptGadget,
    },
};

type CS = <<S as SelfEmulation>::PCS as InCircuitPCS<S>>::OffCircuitPCS;

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
    /// The commitment folding of `fold` .
    FoldCommitments,
    /// Hashing the output accumulator once (Poseidon).
    Hash,
}

#[derive(Clone, Debug)]
struct CostCircuit {
    shape: FoldingShape,
    window: Window,
    init: bool,
}

impl CostCircuit {
    fn rows(shape: &FoldingShape, window: Window, init: bool) -> (usize, u32) {
        let circuit = CostCircuit {
            shape: shape.clone(),
            window,
            init,
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
    let mut challenges = transcript.squeeze_challenges(layouter, shape.nb_theta + 2)?;
    let trash = transcript.squeeze_challenge(layouter)?;
    challenges.extend(trash_powers::<S>(
        layouter,
        &chips.scalar,
        &trash,
        shape.nb_trash,
    )?);
    let phase2 = transcript.read_commitment(layouter, &shape.phase2_labels)?;
    challenges.extend(transcript.squeeze_challenges(layouter, shape.nb_y)?);
    Ok(AssignedFoldingInstance {
        phase1,
        phase2,
        instances,
        challenges: AssignedChallenges::from_scalars(shape, challenges.into_iter()),
    })
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

            // Stands for the hash of `acc`, which the caller has computed already.
            let acc_hash = chips.scalar.assign(layouter, Value::unknown())?;
            start(Window::FoldScalars, layouter);
            let (mut next, gamma, mut transcript) =
                gadget.fold_scalars(layouter, &acc, &acc_hash, &fresh, Value::unknown())?;
            end(Window::FoldScalars, layouter);

            start(Window::FoldCommitments, layouter);
            (next.instance.phase1, next.instance.phase2) = gadget.fold_commitments(
                layouter,
                &acc.instance,
                &fresh,
                &gamma,
                &mut transcript,
                None,
            )?;
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
    let rows = |w, init| CostCircuit::rows(shape, w, init).0;
    let (fold_total, k) = CostCircuit::rows(shape, Window::All, false);
    let (init_total, init_k) = CostCircuit::rows(shape, Window::All, true);
    let commitments = rows(Window::FoldCommitments, false);
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
        rows(Window::Replay, false),
        rows(Window::AssignAcc, false),
        rows(Window::Init, true),
        rows(Window::FoldScalars, false),
        commitments / c,
        rows(Window::Hash, false),
    );
    println!(
        "  fold circuit without commitment folding {}",
        fold_total - commitments
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
    // `d_total` 7: the IVC step circuit, whose lookup chunk bound is 3.
    let ivc = |c| FoldingShape::synthetic(16, 7, c, &[2], (16, 50));
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
            // Stands in for `cs.max_trash_terms()`: the Poseidon partial-round trashcan.
            nb_trash: 8,
            nb_y,
        }
    }
}

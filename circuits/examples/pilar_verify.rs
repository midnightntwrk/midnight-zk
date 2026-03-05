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

//! Example: create a PilarChip proof and verify it in-circuit.
//!
//! The inner circuit uses PilarChip to prove a + b = c.
//! The outer circuit uses the VerifierGadget to verify the inner proof.
//!
//! Run with:
//! ```sh
//! cargo run -p midnight-circuits --example pilar_verify
//! ```

use std::time::Instant;

use ff::Field;
use group::Group;
use midnight_circuits::{
    ecc::{
        curves::CircuitCurve,
        foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
    },
    field::{
        decomposition::{
            chip::{P2RDecompositionChip, P2RDecompositionConfig},
            pow2range::Pow2RangeChip,
        },
        foreign::FieldChip,
        native::NB_ARITH_COLS,
        NativeChip, NativeConfig, NativeGadget,
    },
    hash::poseidon::{
        PoseidonChip, PoseidonConfig, PoseidonState, NB_POSEIDON_ADVICE_COLS,
        NB_POSEIDON_FIXED_COLS,
    },
    instructions::{AssignmentInstructions, PublicInputInstructions},
    pilar::{PilarChip, PilarConfig, NB_PILAR_FIXED_COLS},
    types::{ComposableChip, Instantiable},
    verifier::{
        fixed_bases, Accumulator, AssignedAccumulator, AssignedVk, BlstrsEmulation, SelfEmulation,
        VerifierGadget,
    },
};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::{cost_model::circuit_model, MockProver},
    plonk::{
        create_proof, keygen_pk, keygen_vk_with_k, prepare, Circuit, Column, ConstraintSystem,
        Error, Fixed, Instance,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;
type E = <S as SelfEmulation>::Engine;
type CBase = <C as CircuitCurve>::Base;
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

const NB_INNER_INSTANCES: usize = 1;

// ---------------------------------------------------------------------------
// Inner circuit: proves a + b = c using PilarChip.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default)]
struct InnerPilarCircuit {
    a: Value<F>,
    b: Value<F>,
}

impl Circuit<F> for InnerPilarCircuit {
    type Config = (PilarConfig, Column<Instance>, Column<Instance>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // The committed instance column MUST be created before the regular one.
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();
        meta.enable_equality(instance_column);

        let advice = meta.advice_column();
        let fixed_cols: [Column<Fixed>; NB_PILAR_FIXED_COLS] =
            core::array::from_fn(|_| meta.fixed_column());

        let pilar_config =
            PilarChip::<F>::configure(meta, &(advice, fixed_cols, instance_column));

        (pilar_config, committed_instance_column, instance_column)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let (pilar_config, _committed_col, instance_col) = config;

        let c_cell = layouter.assign_region(
            || "pilar addition gate",
            |mut region| {
                region.assign_advice(|| "a", pilar_config.advice, 0, || self.a)?;
                region.assign_advice(|| "b", pilar_config.advice, 1, || self.b)?;

                let c_cell = region.assign_advice(
                    || "c = a + b",
                    pilar_config.advice,
                    2,
                    || self.a.zip(self.b).map(|(a, b)| a + b),
                )?;

                // Gate at row 1: q_a·a_prev + q_b·a_cur + q_c·a_next = 0.
                // With rotations {-1,0,1}, row 1 accesses a[0], a[1], a[2].
                region.assign_fixed(|| "q_a", pilar_config.q_a, 1, || Value::known(F::ONE))?;
                region.assign_fixed(|| "q_b", pilar_config.q_b, 1, || Value::known(F::ONE))?;
                region.assign_fixed(|| "q_c", pilar_config.q_c, 1, || Value::known(-F::ONE))?;
                region.assign_fixed(|| "q_m", pilar_config.q_m, 1, || Value::known(F::ZERO))?;
                region.assign_fixed(|| "q_k", pilar_config.q_k, 1, || Value::known(F::ZERO))?;

                Ok(c_cell)
            },
        )?;

        // Constrain c = a + b as a public input.
        layouter.constrain_instance(c_cell.cell(), instance_col, 0)
    }
}

// ---------------------------------------------------------------------------
// Outer circuit: verifies the inner PilarChip proof in-circuit.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct OuterVerifierCircuit {
    inner_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>),
    inner_committed_instance: Value<C>,
    inner_instances: Value<[F; NB_INNER_INSTANCES]>,
    inner_proof: Value<Vec<u8>>,
}

impl Circuit<F> for OuterVerifierCircuit {
    type Config = (
        NativeConfig,
        P2RDecompositionConfig,
        ForeignEccConfig<C>,
        PoseidonConfig<F>,
    );
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, C, NG>();
        let nb_fixed_cols = NB_ARITH_COLS + 4;

        let advice_columns: Vec<_> = (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
        let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_columns[..NB_ARITH_COLS + 4].try_into().unwrap(),
                [committed_instance_column, instance_column],
            ),
        );

        let core_decomp_config = {
            let pow2_config = Pow2RangeChip::configure(meta, &advice_columns[1..NB_ARITH_COLS]);
            P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2_config))
        };

        let base_config = FieldChip::<F, CBase, C, NG>::configure(meta, &advice_columns);
        let curve_config =
            ForeignEccChip::<F, C, C, NG, NG>::configure(meta, &base_config, &advice_columns);

        let poseidon_config = PoseidonChip::configure(
            meta,
            &(
                advice_columns[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
                fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
            ),
        );

        (
            native_config,
            core_decomp_config,
            curve_config,
            poseidon_config,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
        let core_decomp_chip = P2RDecompositionChip::new(&config.1, &16);
        let native_gadget = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
        let curve_chip = ForeignEccChip::new(&config.2, &native_gadget, &native_gadget);
        let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

        let verifier_chip = VerifierGadget::<S>::new(&curve_chip, &native_gadget, &poseidon_chip);

        let assigned_inner_vk = verifier_chip.assign_vk_as_public_input(
            &mut layouter,
            "inner_vk",
            &self.inner_vk.0,
            &self.inner_vk.1,
            self.inner_vk.2,
        )?;

        let assigned_committed_instance =
            curve_chip.assign(&mut layouter, self.inner_committed_instance)?;

        let assigned_inner_pi =
            native_gadget.assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

        let mut inner_proof_acc = verifier_chip.prepare(
            &mut layouter,
            &assigned_inner_vk,
            &[assigned_committed_instance],
            &[&assigned_inner_pi],
            self.inner_proof.clone(),
        )?;

        inner_proof_acc.collapse(&mut layouter, &curve_chip, &native_gadget)?;

        verifier_chip.constrain_as_public_input(&mut layouter, &inner_proof_acc)?;

        core_decomp_chip.load(&mut layouter)
    }
}

// ---------------------------------------------------------------------------
// Main: generate inner proof, then verify it in-circuit.
// ---------------------------------------------------------------------------

fn print_cost_model(name: &str, circuit: &impl Circuit<F>) {
    // BLS12-381: 48-byte commitments, 32-byte scalars.
    let model = circuit_model::<F, 48, 32>(circuit);
    println!("\n  Cost model for {name}:");
    println!("    k (log2 rows) .... {}", model.k);
    println!("    rows ............. {}", model.rows);
    println!("    table rows ....... {}", model.table_rows);
    println!("    unusable rows .... {}", model.nb_unusable_rows);
    println!("    max degree ....... {}", model.max_deg);
    println!("    advice columns ... {}", model.advice_columns);
    println!("    fixed columns .... {}", model.fixed_columns);
    println!("    lookups .......... {}", model.lookups);
    println!("    permutations ..... {}", model.permutations);
    println!("    column queries ... {}", model.column_queries);
    println!("    point sets ....... {}", model.point_sets);
    println!("    proof size ....... {} bytes", model.size);
}

fn main() {
    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    let total = Instant::now();

    // --- Step 1: Create inner PilarChip proof ---

    let a = F::from(3u64);
    let b = F::from(5u64);
    let c = a + b;
    let inner_public_inputs = vec![c];

    let t = Instant::now();
    let inner_k = 5;
    let inner_params = ParamsKZG::unsafe_setup(inner_k, &mut rng);
    let inner_vk = keygen_vk_with_k(&inner_params, &InnerPilarCircuit::default(), inner_k).unwrap();
    let inner_pk = keygen_pk(inner_vk.clone(), &InnerPilarCircuit::default()).unwrap();
    println!("Inner keygen ......... {:?}", t.elapsed());

    print_cost_model("inner circuit", &InnerPilarCircuit::default());

    let t = Instant::now();
    let inner_proof = {
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
        create_proof::<
            F,
            KZGCommitmentScheme<E>,
            CircuitTranscript<PoseidonState<F>>,
            InnerPilarCircuit,
        >(
            &inner_params,
            &inner_pk,
            &[InnerPilarCircuit {
                a: Value::known(a),
                b: Value::known(b),
            }],
            1,
            &[&[&[], &inner_public_inputs]],
            &mut rng,
            &mut transcript,
        )
        .expect("Failed to create inner proof");
        transcript.finalize()
    };
    println!(
        "\nInner proof .......... {:?} ({} bytes)",
        t.elapsed(),
        inner_proof.len()
    );

    // --- Step 2: Prepare accumulator off-circuit ---

    let t = Instant::now();
    let inner_dual_msm = {
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&inner_proof);
        prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
            &inner_vk,
            &[&[C::identity()]],
            &[&[&inner_public_inputs]],
            &mut transcript,
        )
        .expect("Failed to prepare inner proof")
    };

    // Print DualMSM contents.
    {
        let (lhs, rhs) = inner_dual_msm.split();
        println!("\n  DualMSM (pairing check: e(lhs, [τ]₂) = e(rhs, [1]₂)):");
        println!("    LHS ({} terms):", lhs.len());
        for (label, _scalar, _base) in &lhs {
            println!("      {label}");
        }
        println!("    RHS ({} terms):", rhs.len());
        for (label, _scalar, _base) in &rhs {
            println!("      {label}");
        }

        use midnight_proofs::poly::CommitmentLabel;
        let is_fixed_base = |label: &CommitmentLabel| match label {
            CommitmentLabel::Fixed(_) | CommitmentLabel::Permutation(_) => true,
            CommitmentLabel::Custom(s) if s == "-G" => true,
            _ => false,
        };
        let count_variable = |side: &[(&CommitmentLabel, _, _)]| {
            side.iter().filter(|(label, _, _)| !is_fixed_base(label)).count()
        };
        let lhs_var = count_variable(&lhs);
        let rhs_var = count_variable(&rhs);
        let lhs_fixed = lhs.len() - lhs_var;
        let rhs_fixed = rhs.len() - rhs_var;
        println!(
            "    Variable-base MSMs: {} (lhs: {lhs_var}, rhs: {rhs_var})",
            lhs_var + rhs_var
        );
        println!(
            "    Fixed-base MSMs:    {} (lhs: {lhs_fixed}, rhs: {rhs_fixed})",
            lhs_fixed + rhs_fixed
        );
    }

    let fb = fixed_bases::<S>("inner_vk", &inner_vk);
    let mut inner_acc = Accumulator::<S>::from_dual_msm(inner_dual_msm.clone(), "inner_vk", &fb);

    let inner_verifier_params = inner_params.verifier_params();
    assert!(inner_dual_msm.check(&inner_verifier_params));
    assert!(inner_acc.check(&inner_verifier_params, &fb));

    inner_acc.collapse();
    println!("Off-circuit verify ... {:?}", t.elapsed());

    // --- Step 3: Verify the inner proof in-circuit ---

    const OUTER_K: u32 = 17;

    let mut public_inputs = AssignedVk::<S>::as_public_input(&inner_vk);
    public_inputs.extend(AssignedAccumulator::as_public_input(&inner_acc));

    let circuit = OuterVerifierCircuit {
        inner_vk: (
            inner_vk.get_domain().clone(),
            inner_vk.cs().clone(),
            Value::known(inner_vk.transcript_repr()),
        ),
        inner_committed_instance: Value::known(C::identity()),
        inner_instances: Value::known([c]),
        inner_proof: Value::known(inner_proof),
    };

    print_cost_model("outer verifier circuit", &circuit);

    let t = Instant::now();
    let prover =
        MockProver::run(OUTER_K, &circuit, vec![vec![], public_inputs]).expect("MockProver failed");
    println!("\nMockProver::run ...... {:?}", t.elapsed());

    let t = Instant::now();
    prover.assert_satisfied();
    println!("MockProver::verify ... {:?}", t.elapsed());

    println!("\nTotal ................ {:?}", total.elapsed());
}

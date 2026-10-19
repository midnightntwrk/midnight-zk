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

//! Tests of [`FoldingGadget`] against the native folding verifier of
//! `midnight_proofs::plonk::protogalaxy` (BLS12-381 self-emulation, fflonk
//! over KZG): the accumulator computed in-circuit must equal the native one,
//! constrained as public input of a MockProver run.

use ff::Field;
use group::{GroupEncoding, prime::PrimeCurveAffine};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Instance,
        ProvingKey, Selector, TableColumn, keygen_pk, keygen_vk_with_k,
        protogalaxy::{
            Accumulator, FoldingInstance, ProverAccumulator, ProverInstance, commit_instance,
            read_instance,
        },
    },
    poly::{Rotation, commitment::PolynomialCommitmentScheme},
    transcript::{CircuitTranscript, Transcript},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
    ecc::{
        curves::CircuitCurve,
        foreign::weierstrass_chip::{
            ForeignWeierstrassEccChip, ForeignWeierstrassEccConfig, nb_foreign_ecc_chip_columns,
        },
    },
    field::{
        NativeChip, NativeConfig, NativeGadget,
        decomposition::{
            chip::{P2RDecompositionChip, P2RDecompositionConfig},
            pow2range::Pow2RangeChip,
        },
        foreign::FieldChip,
        native::NB_EXTRA_ARITH_FIXED_COLS,
    },
    hash::poseidon::{
        NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS, PoseidonChip, PoseidonConfig,
        PoseidonState,
    },
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::ComposableChip,
    verifier::{
        BlstrsFflonkEmulation, FoldingGadget, FoldingShape, InCircuitPCS, NativeAccumulator,
        SelfEmulation, VerifierGadget, VerifyingKey, accumulator_as_public_input,
    },
};

type S = BlstrsFflonkEmulation;
type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;
type CBase = <C as CircuitCurve>::Base;
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
type CS = <<S as SelfEmulation>::PCS as InCircuitPCS<S>>::OffCircuitPCS;
type T = CircuitTranscript<PoseidonState<F>>;

/// `log n` of the folded circuit.
const INNER_K: u32 = 4;
/// Number of rows of the folded circuit's gate and lookup table.
const ROWS: u64 = 4;

// ---------------------------------------------------------------------------
// Inner circuit: `b = a²` (gate), `a ∈ [1, ROWS]` (lookup), `b₀` is public.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct SquareCircuit {
    start: u64,
}

#[derive(Clone, Debug)]
struct SquareConfig {
    s: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    table: TableColumn,
    instance: Column<Instance>,
}

impl SquareCircuit {
    fn a(&self, row: u64) -> F {
        F::from((self.start + row) % ROWS + 1)
    }

    fn public_input(&self) -> F {
        self.a(0).square()
    }
}

impl Circuit<F> for SquareCircuit {
    type Config = SquareConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        *self
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> SquareConfig {
        let config = SquareConfig {
            s: meta.complex_selector(),
            a: meta.advice_column(),
            b: meta.advice_column(),
            table: meta.lookup_table_column(),
            instance: meta.instance_column(),
        };
        meta.enable_equality(config.b);
        meta.enable_equality(config.instance);
        meta.create_gate("square", |meta| {
            let s = meta.query_selector(config.s);
            let a = meta.query_advice(config.a, Rotation::cur());
            let b = meta.query_advice(config.b, Rotation::cur());
            Constraints::without_selector(vec![s * (a.clone() * a - b)])
        });
        meta.lookup("range", None, |meta| {
            let s = meta.query_selector(config.s);
            let a = meta.query_advice(config.a, Rotation::cur());
            vec![(s.clone() * a + (Expression::from(1) - s), config.table)]
        });
        config
    }

    fn synthesize(
        &self,
        config: SquareConfig,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                for row in 0..ROWS {
                    let value = Value::known(F::from(row + 1));
                    table.assign_cell(|| "t", config.table, row as usize, || value)?;
                }
                Ok(())
            },
        )?;
        let first_b = layouter.assign_region(
            || "squares",
            |mut region| {
                let mut first_b = None;
                for row in 0..ROWS {
                    config.s.enable(&mut region, row as usize)?;
                    let a = self.a(row);
                    region.assign_advice(|| "a", config.a, row as usize, || Value::known(a))?;
                    let b = Value::known(a.square());
                    let b = region.assign_advice(|| "b", config.b, row as usize, || b)?;
                    first_b.get_or_insert(b.cell());
                }
                Ok(first_b.unwrap())
            },
        )?;
        layouter.constrain_instance(first_b, config.instance, 0)
    }
}

// ---------------------------------------------------------------------------
// Native side: partial proofs and the native folding verifier.
// ---------------------------------------------------------------------------

/// A fresh instance: its partial proof (commit phases), public input and the
/// native verifier's view of it.
#[derive(Clone)]
struct Fresh {
    public: FoldingInstance<F, CS>,
    proof: Vec<u8>,
    pi: F,
}

struct Native {
    params: <CS as PolynomialCommitmentScheme<F>>::Parameters,
    pk: ProvingKey<F, CS>,
}

impl Native {
    fn new() -> Self {
        let params = CS::gen_params(INNER_K);
        let circuit = SquareCircuit { start: 0 };
        let vk = keygen_vk_with_k::<_, CS, _>(&params, &circuit, INNER_K).unwrap();
        let pk = keygen_pk(vk, &circuit).unwrap();
        Native { params, pk }
    }

    fn vk(&self) -> &VerifyingKey<S> {
        self.pk.get_vk()
    }

    /// The partial proof of step `i` (shifted witness), prover and verifier
    /// views.
    fn step(&self, i: u64) -> (ProverInstance<'_, F, CS>, Fresh) {
        let circuit = SquareCircuit { start: 3 * i };
        let pi = circuit.public_input();
        let mut transcript = T::init();
        let rng = ChaCha8Rng::seed_from_u64(i);
        let prover = commit_instance(
            &self.params,
            &self.pk,
            &circuit,
            &[&[pi]],
            &mut transcript,
            rng,
        )
        .unwrap();
        let proof = transcript.finalize();
        let public = read_instance(self.vk(), &[&[pi]], &mut T::init_from_bytes(&proof)).unwrap();
        (prover, Fresh { public, proof, pi })
    }

    fn shape(&self) -> FoldingShape {
        FoldingShape::new::<S>(self.vk().cs(), INNER_K, &[1])
    }

    /// The native verifier's accumulator after folding `fresh` into `acc`.
    fn verify_fold(
        &self,
        acc: &NativeAccumulator<S>,
        fresh: &Fresh,
        folding_proof: &[u8],
    ) -> NativeAccumulator<S> {
        let transcript = &mut T::init_from_bytes(folding_proof);
        acc.fold(self.vk(), std::slice::from_ref(&fresh.public), transcript).unwrap()
    }
}

// ---------------------------------------------------------------------------
// The folding verifier circuit.
// ---------------------------------------------------------------------------

type ChipsConfig = (
    NativeConfig,
    P2RDecompositionConfig,
    ForeignWeierstrassEccConfig<C>,
    PoseidonConfig<F>,
);

fn configure_chips(meta: &mut ConstraintSystem<F>) -> ChipsConfig {
    const NB_ARITH_COLS: usize = 5;
    const NB_ARITH_FIXED_COLS: usize = NB_ARITH_COLS + NB_EXTRA_ARITH_FIXED_COLS;
    let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, C, NG>();
    let advice_columns: Vec<_> = (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
    let fixed_columns: Vec<_> = (0..NB_ARITH_FIXED_COLS).map(|_| meta.fixed_column()).collect();
    let committed_instance_column = meta.instance_column();
    let instance_column = meta.instance_column();

    let native_config = NativeChip::configure(
        meta,
        &(
            advice_columns[..NB_ARITH_COLS].to_vec(),
            fixed_columns[..NB_ARITH_FIXED_COLS].to_vec(),
            [committed_instance_column, instance_column],
        ),
    );
    let nb_parallel_range_checks = NB_ARITH_COLS - 1;
    let max_bit_len = 16;
    let pow2_config = Pow2RangeChip::configure(meta, &advice_columns[1..=nb_parallel_range_checks]);
    let core_decomp_config =
        P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2_config));
    let base_config = FieldChip::<F, CBase, C, NG>::configure(
        meta,
        &advice_columns,
        nb_parallel_range_checks,
        max_bit_len,
    );
    let curve_config = ForeignWeierstrassEccChip::<F, C, C, NG, NG>::configure(
        meta,
        &base_config,
        &advice_columns,
        nb_parallel_range_checks,
        max_bit_len,
    );
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

struct Chips {
    core_decomp: P2RDecompositionChip<F>,
    scalar: NG,
    curve: ForeignWeierstrassEccChip<F, C, C, NG, NG>,
    sponge: PoseidonChip<F>,
}

fn chips(config: &ChipsConfig) -> Chips {
    let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
    let core_decomp = P2RDecompositionChip::new(&config.1, &16);
    let scalar = NativeGadget::new(core_decomp.clone(), native_chip.clone());
    let curve = ForeignWeierstrassEccChip::new(&config.2, &scalar, &scalar);
    let sponge = PoseidonChip::new(&config.3, &native_chip);
    Chips {
        core_decomp,
        scalar,
        curve,
        sponge,
    }
}

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
enum Step {
    Init,
    Fold {
        acc: Value<NativeAccumulator<S>>,
        folding_proof: Value<Vec<u8>>,
    },
}

/// Reads a fresh instance of [`SquareCircuit`] from its partial proof, then
/// either initialises an accumulator with it or folds it into `acc`; the
/// resulting accumulator is the public input.
#[derive(Clone, Debug)]
struct FoldingCircuit {
    vk: VerifyingKey<S>,
    shape: FoldingShape,
    fresh_pi: Value<F>,
    partial_proof: Value<Vec<u8>>,
    step: Step,
}

impl Circuit<F> for FoldingCircuit {
    type Config = ChipsConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
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
        let verifier = VerifierGadget::<S>::new(&chips.curve, &chips.scalar, &chips.sponge);
        let gadget = FoldingGadget::<S>::new(
            &chips.curve,
            &chips.scalar,
            &chips.sponge,
            self.shape.clone(),
        );

        let vk = verifier.assign_fixed_vk(
            &mut layouter,
            self.vk.get_domain(),
            self.vk.cs(),
            self.vk.transcript_repr(),
        )?;
        let pi = chips.scalar.assign(&mut layouter, self.fresh_pi)?;
        let fresh =
            gadget.read_instance(&mut layouter, &vk, &[&[pi]], self.partial_proof.clone())?;

        let next = match &self.step {
            Step::Init => gadget.init(&mut layouter, fresh)?,
            Step::Fold { acc, folding_proof } => {
                let acc = gadget.assign_accumulator(&mut layouter, acc.as_ref())?;
                gadget.fold(&mut layouter, &acc, &fresh, folding_proof.clone())?
            }
        };
        for x in next.as_public_input(&mut layouter, &chips.curve)? {
            chips.scalar.constrain_as_public_input(&mut layouter, &x)?;
        }
        chips.core_decomp.load(&mut layouter)
    }
}

impl FoldingCircuit {
    fn new(native: &Native, fresh: &Fresh, step: Step) -> Self {
        FoldingCircuit {
            vk: native.vk().clone(),
            shape: native.shape(),
            fresh_pi: Value::known(fresh.pi),
            partial_proof: Value::known(fresh.proof.clone()),
            step,
        }
    }

    fn fold(native: &Native, acc: &NativeAccumulator<S>, fresh: &Fresh, proof: &[u8]) -> Self {
        let step = Step::Fold {
            acc: Value::known(acc.clone()),
            folding_proof: Value::known(proof.to_vec()),
        };
        Self::new(native, fresh, step)
    }

    /// Whether the circuit is satisfied with `expected` as public output.
    fn outputs(&self, expected: &NativeAccumulator<S>) -> bool {
        let pi = accumulator_as_public_input::<S>(expected);
        let prover = MockProver::run(self, vec![vec![], pi]).expect("MockProver failed");
        prover.verify().is_ok()
    }
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// One native fold: `acc` and the fresh instance `fresh` (step `round + 1`)
/// give `next` under `folding_proof`.
struct Round {
    acc: NativeAccumulator<S>,
    fresh: Fresh,
    folding_proof: Vec<u8>,
    next: NativeAccumulator<S>,
}

impl Round {
    fn circuit(&self, native: &Native) -> FoldingCircuit {
        FoldingCircuit::fold(native, &self.acc, &self.fresh, &self.folding_proof)
    }
}

/// `Accumulator::init` on step 0, then `rounds` folds of steps `1..=rounds`,
/// proving them (`ProverAccumulator`) and verifying them (`Accumulator`)
/// natively.
fn chain(native: &Native, rounds: u64) -> Vec<Round> {
    let (pk, vk) = (&native.pk, native.vk());
    let mut prover_acc = ProverAccumulator::init(pk, native.step(0).0, &mut T::init()).unwrap();
    let mut out = Vec::new();
    for i in 1..=rounds {
        let acc = prover_acc.accumulator().clone();
        let (prover_fresh, fresh) = native.step(i);
        let mut transcript = T::init();
        prover_acc = prover_acc.fold(pk, vec![prover_fresh], &mut transcript).unwrap();
        let folding_proof = transcript.finalize();
        let next = native.verify_fold(&acc, &fresh, &folding_proof);
        assert_eq!(&next, prover_acc.accumulator());
        assert!(prover_acc.is_satisfied(pk));
        assert_ne!(next.error(), F::ZERO, "e' should be non-trivial");
        assert_eq!(vk.get_domain().k(), INNER_K);
        out.push(Round {
            acc,
            fresh,
            folding_proof,
            next,
        });
    }
    out
}

#[test]
fn folding_gadget_init() {
    let native = Native::new();
    let (_, fresh) = native.step(0);
    let expected = Accumulator::init(native.vk(), fresh.public.clone(), &mut T::init()).unwrap();
    assert!(FoldingCircuit::new(&native, &fresh, Step::Init).outputs(&expected));
}

/// Two chained folds: the second one folds into an accumulator with a
/// non-trivial error term and an already folded instance.
#[test]
fn folding_gadget_fold() {
    let native = Native::new();
    for round in chain(&native, 2) {
        assert!(round.circuit(&native).outputs(&round.next));
    }
}

/// The folding verifier cannot reject (soundness comes from the decider), so
/// a tampered input must make the gadget output *the native verifier's
/// output on the tampered data* (circuit satisfied with it), which differs
/// from the honest accumulator (circuit unsatisfied with that one).
#[test]
fn folding_gadget_tampered() {
    let native = Native::new();
    let round = &chain(&native, 1)[0];
    let scalar_len = {
        let mut t = T::init();
        t.write(&F::ONE).unwrap();
        t.finalize().len()
    };

    // Checks the circuit on (acc, fresh, proof), a tampered version of the
    // round.
    let check = |fresh: &Fresh, proof: &[u8]| {
        let tampered = native.verify_fold(&round.acc, fresh, proof);
        assert_ne!(tampered, round.next);
        let circuit = FoldingCircuit::fold(&native, &round.acc, fresh, proof);
        assert!(circuit.outputs(&tampered));
        assert!(!circuit.outputs(&round.next));
    };

    // Replaces the scalar at `offset` of the folding proof by itself plus one.
    let bump = |offset: usize| {
        let mut proof = round.folding_proof.clone();
        let old: F = T::init_from_bytes(&proof[offset..]).read().unwrap();
        let mut t = T::init();
        t.write(&(old + F::ONE)).unwrap();
        proof[offset..offset + scalar_len].copy_from_slice(&t.finalize());
        proof
    };

    // A tampered perturbator coefficient F_1 (the first folding message).
    check(&round.fresh, &bump(0));

    // A tampered K_0 (the first coefficient after the log n F's).
    check(&round.fresh, &bump(native.shape().log_n * scalar_len));

    // A tampered fresh phase-1 commitment: its first point (after the 4-byte
    // polynomial count) replaced by the generator.
    let mut fresh = round.fresh.clone();
    let generator = GroupEncoding::to_bytes(&<S as SelfEmulation>::G1Affine::generator());
    let point = generator.as_ref();
    fresh.proof[4..4 + point.len()].copy_from_slice(point);
    fresh.public = read_instance(
        native.vk(),
        &[&[fresh.pi]],
        &mut T::init_from_bytes(&fresh.proof),
    )
    .unwrap();
    check(&fresh, &round.folding_proof);
}

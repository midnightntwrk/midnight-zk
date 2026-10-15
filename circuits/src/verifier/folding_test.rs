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
//! `midnight_proofs::plonk::protogalaxy` (BLS12-381, fflonk with `T_MAX = 8`
//! over KZG): the accumulator computed in-circuit must equal
//! the native one, constrained as public input of a MockProver run.

use ff::Field;
use group::{GroupEncoding, prime::PrimeCurveAffine};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Instance,
        ProvingKey, Selector, TableColumn, VerifyingKey, keygen_pk, keygen_vk_with_k,
        protogalaxy::{
            Accumulator, FoldingInstance, ProverAccumulator, ProverInstance, commit_instance,
            read_instance,
        },
    },
    poly::{
        Rotation, commitment::PolynomialCommitmentScheme, fflonk::Fflonk, kzg::KZGCommitmentScheme,
    },
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
        NativeChip, NativeConfig, NativeGadget, RangeCheckChip, RangeCheckConfig,
        foreign::FieldChip, native::NB_EXTRA_ARITH_FIXED_COLS,
    },
    hash::poseidon::{
        NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS, PoseidonChip, PoseidonConfig,
        PoseidonState,
    },
    instructions::{
        AssignmentInstructions, PublicInputInstructions,
        hash::{HashCPU, HashInstructions},
    },
    types::ComposableChip,
    verifier::{
        FoldingGadget, FoldingShape, NativeAccumulator, VerifierGadget, accumulator_as_public_input,
    },
};

type E = midnight_curves::Bls12;
pub(super) type F = midnight_curves::Fq;
type C = midnight_curves::G1Projective;
type CBase = <C as CircuitCurve>::Base;
type NG = NativeGadget<F>;
type CS = Fflonk<KZGCommitmentScheme<E>, 3>;
type T = CircuitTranscript<PoseidonState<F>>;

const INNER_K: u32 = 6;
const ROWS: u64 = 16;

// ---------------------------------------------------------------------------
// Inner circuit: `b = a²` (gate), `a ∈ [1, 16]` (lookup), `b₀` is public.
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

    fn vk(&self) -> &VerifyingKey<F, CS> {
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
        FoldingShape::new::<E, CS>(self.vk().cs(), INNER_K, &[1])
    }
}

// ---------------------------------------------------------------------------
// The folding verifier circuit.
// ---------------------------------------------------------------------------

pub(super) type ChipsConfig = (
    NativeConfig,
    RangeCheckConfig<F>,
    ForeignWeierstrassEccConfig<C>,
    PoseidonConfig<F>,
);

/// The chips of the verifier gadget tests.
pub(super) fn configure_chips(meta: &mut ConstraintSystem<F>) -> ChipsConfig {
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
    let range_check_config = RangeCheckChip::configure(
        meta,
        &(
            advice_columns[..5].to_vec(),
            fixed_columns[..4].to_vec(),
            16,
        ),
    );
    let base_config = FieldChip::<F, CBase, C, NG>::configure(meta, &advice_columns);
    let curve_config = ForeignWeierstrassEccChip::<F, C, C, NG, NG>::configure(
        meta,
        &base_config,
        &advice_columns,
        &fixed_columns,
        16,
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
        range_check_config,
        curve_config,
        poseidon_config,
    )
}

pub(super) struct Chips {
    pub(super) range_check: RangeCheckChip<F>,
    pub(super) scalar: NG,
    pub(super) curve: ForeignWeierstrassEccChip<F, C, C, NG, NG>,
    pub(super) sponge: PoseidonChip<F>,
}

pub(super) fn chips(config: &ChipsConfig) -> Chips {
    let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
    let range_check = RangeCheckChip::new(&config.1, &native_chip);
    let scalar = NativeGadget::new(native_chip.clone(), range_check.clone());
    let curve = ForeignWeierstrassEccChip::new(&config.2, &scalar, &scalar);
    let sponge = PoseidonChip::new(&config.3, &native_chip);
    Chips {
        range_check,
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
        acc: Value<NativeAccumulator<E, CS>>,
        folding_proof: Value<Vec<u8>>,
    },
}

/// Reads a fresh instance of [`SquareCircuit`] from its partial proof, then
/// either initialises an accumulator with it or folds it into `acc`; the
/// resulting accumulator is the public input.
#[derive(Clone, Debug)]
struct FoldingCircuit {
    vk: VerifyingKey<F, CS>,
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
        let verifier = VerifierGadget::<F, CS>::new(&chips.curve, &chips.scalar);
        let gadget = FoldingGadget::<E, CS>::new(
            &chips.curve,
            &chips.scalar,
            &chips.sponge,
            self.shape.clone(),
        );

        let domain = self.vk.get_domain();
        let vk = verifier.assign_fixed_vk(
            &mut layouter,
            domain,
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
                let acc_pi = acc.as_public_input(&mut layouter, &chips.curve)?;
                let acc_hash = chips.sponge.hash(&mut layouter, &acc_pi)?;
                gadget.fold(
                    &mut layouter,
                    &acc,
                    &acc_hash,
                    &fresh,
                    folding_proof.clone(),
                    None,
                )?
            }
        };
        for x in next.as_public_input(&mut layouter, &chips.curve)? {
            chips.scalar.constrain_as_public_input(&mut layouter, &x)?;
        }
        chips.range_check.load(&mut layouter)
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

    fn fold(native: &Native, acc: &NativeAccumulator<E, CS>, fresh: &Fresh, proof: &[u8]) -> Self {
        let step = Step::Fold {
            acc: Value::known(acc.clone()),
            folding_proof: Value::known(proof.to_vec()),
        };
        Self::new(native, fresh, step)
    }

    /// Whether the circuit is satisfied with `expected` as public output.
    fn outputs(&self, expected: &NativeAccumulator<E, CS>) -> bool {
        let pi = accumulator_as_public_input::<E, CS>(expected);
        let prover = MockProver::run(self, vec![vec![], pi]).expect("MockProver failed");
        prover.verify().is_ok()
    }
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// The native accumulators after `init` (step 0) and one `fold` (step 1),
/// and the native folding proof of step 2 into the latter, with its result.
struct Chain {
    acc1: NativeAccumulator<E, CS>,
    fresh2: Fresh,
    folding_proof: Vec<u8>,
    acc2: NativeAccumulator<E, CS>,
}

/// The hash binding an accumulator (a Poseidon hash of its public input).
fn acc_hash(acc: &NativeAccumulator<E, CS>) -> F {
    <PoseidonChip<F> as HashCPU<F, F>>::hash(&accumulator_as_public_input::<E, CS>(acc))
}

fn chain(native: &Native) -> Chain {
    let (pk, vk) = (&native.pk, native.vk());
    let acc0 = ProverAccumulator::init(pk, native.step(0).0, &mut T::init()).unwrap();
    let acc0_hash = acc_hash(acc0.accumulator());
    let acc1 = acc0.fold(pk, native.step(1).0, Some(acc0_hash), &mut T::init()).unwrap();
    let acc1_public = acc1.accumulator().clone();
    let hash1 = acc_hash(&acc1_public);

    let (prover2, fresh2) = native.step(2);
    let mut transcript = T::init();
    let acc2_prover = acc1.fold(pk, prover2, Some(hash1), &mut transcript).unwrap();
    let folding_proof = transcript.finalize();
    let acc2 = (acc1_public.fold(
        vk,
        &fresh2.public,
        Some(hash1),
        &mut T::init_from_bytes(&folding_proof),
    ))
    .unwrap();
    assert_eq!(&acc2, acc2_prover.accumulator());
    assert_ne!(acc2.error(), F::ZERO, "e' should be non-trivial");
    Chain {
        acc1: acc1_public,
        fresh2,
        folding_proof,
        acc2,
    }
}

#[test]
fn folding_gadget_init() {
    let native = Native::new();
    let (_, fresh) = native.step(0);
    let expected = Accumulator::init(native.vk(), fresh.public.clone(), &mut T::init()).unwrap();
    assert!(FoldingCircuit::new(&native, &fresh, Step::Init).outputs(&expected));
}

#[test]
fn folding_gadget_fold() {
    let native = Native::new();
    let c = chain(&native);
    let circuit = FoldingCircuit::fold(&native, &c.acc1, &c.fresh2, &c.folding_proof);
    assert!(circuit.outputs(&c.acc2));
}

/// A tampered folding message or fresh instance changes `γ` (or the
/// differences `fresh − acc`), so the products `R_i` the honest prover wrote
/// no longer match: the native verifier rejects them and the circuit is
/// unsatisfiable (with the honest output, the only one known).
#[test]
fn folding_gadget_tampered() {
    let native = Native::new();
    let c = chain(&native);
    let acc1 = &c.acc1;
    let vk = native.vk();
    let scalar_len = {
        let mut t = T::init();
        t.write(&F::ONE).unwrap();
        t.finalize().len()
    };
    let generator = midnight_curves::G1Affine::generator();
    let point = GroupEncoding::to_bytes(&generator);
    let point = point.as_ref();

    let rejected = |fresh: &Fresh, proof: &[u8]| {
        let native_fold = acc1.fold(
            vk,
            &fresh.public,
            Some(acc_hash(acc1)),
            &mut T::init_from_bytes(proof),
        );
        assert!(native_fold.is_err());
        let circuit = FoldingCircuit::fold(&native, acc1, fresh, proof);
        assert!(!circuit.outputs(&c.acc2));
    };

    // A tampered perturbator coefficient F_1 (the first folding message).
    let mut proof = c.folding_proof.clone();
    let f1: F = T::init_from_bytes(&proof).read().unwrap();
    let mut t = T::init();
    t.write(&(f1 + F::ONE)).unwrap();
    proof[..scalar_len].copy_from_slice(&t.finalize());
    rejected(&c.fresh2, &proof);

    // A tampered fresh phase-1 commitment: its first point (after the 4-byte
    // polynomial count) replaced by the generator.
    let mut fresh = c.fresh2.clone();
    fresh.proof[4..4 + point.len()].copy_from_slice(point);
    fresh.public =
        read_instance(vk, &[&[fresh.pi]], &mut T::init_from_bytes(&fresh.proof)).unwrap();
    rejected(&fresh, &c.folding_proof);

    // A wrong product: R_2, the second point of the phase-1 products, which
    // follow the log n + d − 1 scalars and a 4-byte polynomial count.
    let mut proof = c.folding_proof.clone();
    let offset = (native.shape().log_n + native.shape().d_total - 1) * scalar_len;
    let r2 = offset + 4 + point.len();
    proof[r2..r2 + point.len()].copy_from_slice(point);
    rejected(&c.fresh2, &proof);
}

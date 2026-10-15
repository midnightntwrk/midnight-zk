//! Folding chain + decider, for KZG and fflonk.

use std::time::{Duration, Instant};

use blake2b_simd::State;
use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_core::OsRng;

use super::{
    Accumulator, ProverAccumulator, commit_instance, folding_degree,
    poly::{inner_product, pow_vector},
    prove_relaxed_trace, read_instance,
    sparse_gates::SparseGates,
    trace::{evaluate_rows, evaluate_rows_dense, fold_trace},
    verify_relaxed_trace,
};
use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Instance,
        ProvingKey, Selector, TableColumn, keygen_pk, keygen_vk_with_k,
    },
    poly::{
        Rotation,
        commitment::{Guard, PolynomialCommitmentScheme},
        fflonk::Fflonk,
        kzg::KZGCommitmentScheme,
    },
    transcript::{CircuitTranscript, Hashable, Transcript},
};

const K: u32 = 6;
const ROWS: u64 = 16;
const NB_FOLDS: u64 = 4;

type T = CircuitTranscript<State>;

/// `b = a²` on enabled rows (gate), `a ∈ {1..16}` (lookup), `b` of row 0 is
/// the public input (copy constraint). `start` varies the witness; `corrupt`
/// breaks the gate on one row.
#[derive(Clone, Copy)]
struct SquareCircuit {
    start: u64,
    corrupt: bool,
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
    fn a(&self, row: u64) -> Fq {
        Fq::from((self.start + row) % ROWS + 1)
    }

    fn public_input(&self) -> Fq {
        self.a(0).square()
    }
}

impl Circuit<Fq> for SquareCircuit {
    type Config = SquareConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        *self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> SquareConfig {
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
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                for row in 0..ROWS {
                    let value = Value::known(Fq::from(row + 1));
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
                    let b = a.square() + Fq::from((self.corrupt && row == 5) as u64);
                    region.assign_advice(|| "a", config.a, row as usize, || Value::known(a))?;
                    let b =
                        region.assign_advice(|| "b", config.b, row as usize, || Value::known(b))?;
                    first_b.get_or_insert(b.cell());
                }
                Ok(first_b.unwrap())
            },
        )?;

        layouter.constrain_instance(first_b, config.instance, 0)
    }
}

/// The row-sparse evaluation of the custom gates agrees with the dense one.
fn assert_sparse_matches_dense<CS: PolynomialCommitmentScheme<Fq>>(
    pk: &ProvingKey<Fq, CS>,
    trace: &crate::plonk::traces::ProverTrace<'_, Fq, crate::poly::LagrangeCoeff>,
    sparse: &SparseGates<Fq>,
) {
    assert_eq!(
        &*evaluate_rows(pk, trace, sparse),
        &*evaluate_rows_dense(pk, trace)
    );
}

/// `Σᵢ powᵢ(β⃗)·fᵢ` computed directly from the prover's folded trace.
fn relaxed_sum<CS: PolynomialCommitmentScheme<Fq>>(
    pk: &ProvingKey<Fq, CS>,
    acc: &ProverAccumulator<'_, Fq, CS>,
) -> Fq {
    inner_product(
        &pow_vector(&acc.public.betas),
        &evaluate_rows(pk, &acc.trace, &acc.sparse),
    )
}

#[derive(Default)]
struct Timings {
    commit: Duration,
    fold: Duration,
    fold_verify: Duration,
    // One call each per fold, to split `fold` (which does `d` row evaluations
    // and `d` trace folds, see `ProverAccumulator::fold`).
    evaluate_rows: Duration,
    fold_trace: Duration,
}

/// Initialises with instance 0, folds instances 1..=NB_FOLDS (the last one
/// corrupted if `corrupt_last`), checking prover and verifier agree, then
/// proves and verifies the decider. Returns whether the decider verified.
fn fold_chain<CS: PolynomialCommitmentScheme<Fq>>(k: u32, corrupt_last: bool) -> bool
where
    CS::Commitment: Hashable<State>,
{
    let circuit = |start, corrupt| SquareCircuit { start, corrupt };
    let params = CS::gen_params(k);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &circuit(0, false), k).unwrap();
    let pk = keygen_pk(vk, &circuit(0, false)).unwrap();
    let vk = pk.get_vk();
    let d = folding_degree(vk.cs());
    let sparse = SparseGates::new(vk.cs(), &pk.fixed_values);

    // One step: the partial proof of instance `i` and both views of it.
    let step = |i: u64| {
        let circuit = circuit(3 * i, corrupt_last && i == NB_FOLDS);
        let pi = [circuit.public_input()];
        let instances: &[&[Fq]] = &[&pi];
        let mut transcript = T::init();
        let instance =
            commit_instance(&params, &pk, &circuit, instances, &mut transcript, OsRng).unwrap();
        let bytes = transcript.finalize();
        let read = read_instance(vk, instances, &mut T::init_from_bytes(&bytes)).unwrap();
        assert_eq!(&read, instance.public());
        (instance, read)
    };

    let (instance, fresh) = step(0);
    if !corrupt_last {
        assert!(evaluate_rows(&pk, &instance.trace, &sparse).iter().all(|f| *f == Fq::ZERO));
    }
    let mut acc = ProverAccumulator::init(&pk, instance, &mut T::init()).unwrap();
    let mut acc_v = Accumulator::init(vk, fresh, &mut T::init()).unwrap();
    assert_eq!(&acc_v, acc.accumulator());

    let mut timings = Timings::default();
    for i in 1..=NB_FOLDS {
        let start = Instant::now();
        let (instance, fresh) = step(i);
        timings.commit += start.elapsed();
        if !(corrupt_last && i == NB_FOLDS) {
            assert!(evaluate_rows(&pk, &instance.trace, &sparse).iter().all(|f| *f == Fq::ZERO));
        }

        let start = Instant::now();
        let folded = fold_trace(&acc.trace, &instance.trace, Fq::from(2));
        timings.fold_trace += start.elapsed();
        let start = Instant::now();
        evaluate_rows(&pk, &folded, &sparse);
        timings.evaluate_rows += start.elapsed();
        drop(folded);
        // Fresh trace, and a trace folded with a random `x` (folded challenges).
        assert_sparse_matches_dense(&pk, &instance.trace, &sparse);
        let random_fold = fold_trace(&acc.trace, &instance.trace, Fq::random(OsRng));
        assert_sparse_matches_dense(&pk, &random_fold, &sparse);

        let mut transcript = T::init();
        let start = Instant::now();
        acc = acc.fold(&pk, instance, &mut transcript).unwrap();
        timings.fold += start.elapsed();
        let bytes = transcript.finalize();

        let start = Instant::now();
        acc_v = acc_v.fold(vk, &fresh, &mut T::init_from_bytes(&bytes)).unwrap();
        timings.fold_verify += start.elapsed();
        assert_eq!(&acc_v, acc.accumulator());
        if !corrupt_last {
            // e' is the relaxed sum of the folded trace at β⃗*.
            assert_eq!(relaxed_sum(&pk, &acc), acc.public.error);
        }
    }

    let mut transcript = T::init();
    let start = Instant::now();
    prove_relaxed_trace(&params, &pk, acc, &mut transcript).unwrap();
    let decider_prove = start.elapsed();
    let proof = transcript.finalize();

    let start = Instant::now();
    let verified = verify_relaxed_trace(vk, &acc_v, &mut T::init_from_bytes(&proof))
        .and_then(|guard| {
            guard.verify(&CS::get_verifier_params(&params)).map_err(|_| Error::Opening)
        })
        .is_ok();
    let decider_verify = start.elapsed();

    let per_fold = |d: Duration| d / NB_FOLDS as u32;
    eprintln!(
        "{}: k = {k}, d_total = {d}, per fold: commit {:?}, fold {:?}, fold verify {:?} \
         (one evaluate_rows {:?}, one fold_trace {:?}); decider: prove {:?}, verify {:?}, {} bytes",
        std::any::type_name::<CS>(),
        per_fold(timings.commit),
        per_fold(timings.fold),
        per_fold(timings.fold_verify),
        per_fold(timings.evaluate_rows),
        per_fold(timings.fold_trace),
        decider_prove,
        decider_verify,
        proof.len(),
    );
    verified
}

type Kzg = KZGCommitmentScheme<Bls12>;
type FflonkKzg = Fflonk<KZGCommitmentScheme<Bls12>, 3>;

#[test]
fn fold_chain_and_decider_kzg() {
    assert!(fold_chain::<Kzg>(K, false));
}

#[test]
fn fold_chain_and_decider_fflonk() {
    assert!(fold_chain::<FflonkKzg>(K, false));
}

#[test]
fn corrupted_instance_is_rejected_kzg() {
    assert!(!fold_chain::<Kzg>(K, true));
}

#[test]
fn corrupted_instance_is_rejected_fflonk() {
    assert!(!fold_chain::<FflonkKzg>(K, true));
}

/// The decider on the first accumulator (no fold) accepts it, and rejects it
/// with a wrong error term.
fn decider_checks_error<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let circuit = SquareCircuit {
        start: 0,
        corrupt: false,
    };
    let params = CS::gen_params(K);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &circuit, K).unwrap();
    let pk = keygen_pk(vk, &circuit).unwrap();
    let vk = pk.get_vk();
    let pi = [circuit.public_input()];
    let instances: &[&[Fq]] = &[&pi];
    let instance =
        commit_instance(&params, &pk, &circuit, instances, &mut T::init(), OsRng).unwrap();
    let acc_v = Accumulator::init(vk, instance.public().clone(), &mut T::init()).unwrap();
    let acc = ProverAccumulator::init(&pk, instance, &mut T::init()).unwrap();

    let mut transcript = T::init();
    prove_relaxed_trace(&params, &pk, acc, &mut transcript).unwrap();
    let proof = transcript.finalize();
    let verify = |acc: &Accumulator<Fq, CS>| {
        verify_relaxed_trace(vk, acc, &mut T::init_from_bytes(&proof))
            .and_then(|guard| {
                guard.verify(&CS::get_verifier_params(&params)).map_err(|_| Error::Opening)
            })
            .is_ok()
    };
    assert!(verify(&acc_v));
    let mut wrong = acc_v;
    wrong.error += Fq::ONE;
    assert!(!verify(&wrong));
}

#[test]
fn decider_checks_error_kzg() {
    decider_checks_error::<Kzg>();
}

#[test]
fn decider_checks_error_fflonk() {
    decider_checks_error::<FflonkKzg>();
}

/// Same chain on a larger domain, for timings:
/// `cargo test --release -p midnight-proofs fold_timings -- --ignored
/// --nocapture`.
#[test]
#[ignore]
fn fold_timings() {
    assert!(fold_chain::<Kzg>(14, false));
    assert!(fold_chain::<FflonkKzg>(14, false));
}

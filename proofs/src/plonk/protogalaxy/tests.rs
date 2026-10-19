//! Fresh instances: the prover's commit phases and the verifier's read agree,
//! and the commitments of instances combine like their polynomials. Folding:
//! prover and verifier agree, the relaxed relation holds, and the folding
//! degree bounds the degree of `G`. Decider: the relaxed-trace proof of the
//! prover's accumulator verifies against the verifier's, and not against one
//! with a wrong error term.

use blake2b_simd::State;
use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_core::OsRng;
use rayon::iter::ParallelIterator;

use super::{
    Accumulator, FoldingInstance, ProverAccumulator, ProverInstance, commit_instance,
    folding_degree,
    poly::{inner_product, interpolate, lagrange_basis, pow_vector},
    prove_one_shot, prove_relaxed_trace, read_instance,
    trace::{evaluate_rows, evaluate_rows_dense, linear_combination},
    verify_one_shot, verify_relaxed_trace,
};
use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Fixed, ProvingKey, Selector,
        argument::prover::Committed,
        keygen_pk, keygen_vk_with_k,
        test_circuit::{K, SquareCircuit},
        traces::ProverTrace,
    },
    poly::{
        LagrangeCoeff, Polynomial, Rotation,
        commitment::{Guard, PolynomialCommitmentScheme},
        fflonk::Fflonk,
        kzg::KZGCommitmentScheme,
    },
    transcript::{CircuitTranscript, Hashable, Transcript},
};

type T = CircuitTranscript<State>;

/// Commits `circuit` as a fresh instance; returns it with the transcript
/// bytes.
fn commit<'a, CS: PolynomialCommitmentScheme<Fq>>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<Fq, CS>,
    circuit: SquareCircuit,
) -> (ProverInstance<'a, Fq, CS>, Vec<u8>)
where
    CS::Commitment: Hashable<State>,
{
    let mut transcript = T::init();
    let instance = commit_instance(
        params,
        pk,
        &circuit,
        &[&[circuit.public_input()]],
        &mut transcript,
        OsRng,
    )
    .unwrap();
    (instance, transcript.finalize())
}

fn setup<CS: PolynomialCommitmentScheme<Fq>>() -> (CS::Parameters, ProvingKey<Fq, CS>) {
    let params = CS::gen_params(K);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &SquareCircuit::default(), K).unwrap();
    let pk = keygen_pk(vk, &SquareCircuit::default()).unwrap();
    (params, pk)
}

/// The `index`-th fresh instance of a chain (its own witness), as the prover
/// has it and as the verifier reads it from the transcript bytes.
fn fresh_instance<'a, CS: PolynomialCommitmentScheme<Fq>>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<Fq, CS>,
    index: usize,
    corrupt: bool,
) -> (ProverInstance<'a, Fq, CS>, FoldingInstance<Fq, CS>)
where
    CS::Commitment: Hashable<State>,
{
    let circuit = SquareCircuit {
        start: 3 * index as u64,
        corrupt,
    };
    let (instance, bytes) = commit(params, pk, circuit);
    let read = read_instance(
        pk.get_vk(),
        &[&[circuit.public_input()]],
        &mut T::init_from_bytes(&bytes),
    )
    .unwrap();
    (instance, read)
}

/// Initialises with fresh instance 0, then folds `rounds[r]` fresh instances
/// at once in round `r` (instances are numbered in order; `corrupt` is the
/// index of the one with a broken gate). After every round, asserts that the
/// verifier's accumulator is the prover's, and returns whether the relaxed
/// relation holds for the prover's folded trace (one entry per round). Stops
/// at the first round after which it fails: the prover's perturbator has the
/// true relaxed sum as constant term, the verifier's the claimed `e`, so the
/// two accumulators diverge when folding an invalid one.
fn fold_chain<CS: PolynomialCommitmentScheme<Fq>>(
    rounds: &[usize],
    corrupt: Option<usize>,
) -> Vec<bool>
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    run_chain(&params, &pk, rounds, corrupt).2
}

/// The fold loop of [`fold_chain`] on the given parameters and key; returns
/// the final prover and verifier accumulators, and the per-round results.
fn run_chain<'a, CS: PolynomialCommitmentScheme<Fq>>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<Fq, CS>,
    rounds: &[usize],
    corrupt: Option<usize>,
) -> (
    ProverAccumulator<'a, Fq, CS>,
    Accumulator<Fq, CS>,
    Vec<bool>,
)
where
    CS::Commitment: Hashable<State>,
{
    let fresh = |i| fresh_instance(params, pk, i, corrupt == Some(i));

    let (instance, read) = fresh(0);
    let mut acc = ProverAccumulator::init(pk, instance, &mut T::init()).unwrap();
    let mut acc_v = Accumulator::init(pk.get_vk(), read, &mut T::init()).unwrap();
    assert_eq!(&acc_v, acc.accumulator());

    let mut next = 1;
    let mut holds = vec![];
    for &k in rounds {
        let (instances, reads): (Vec<_>, Vec<_>) = (next..next + k).map(fresh).unzip();
        next += k;

        let mut transcript = T::init();
        acc = acc.fold(pk, instances, None, &mut transcript).unwrap();
        let bytes = transcript.finalize();
        acc_v = acc_v.fold(pk.get_vk(), &reads, None, &mut T::init_from_bytes(&bytes)).unwrap();

        assert_eq!(&acc_v, acc.accumulator());
        if corrupt.is_none() {
            assert_eq!(acc.rows.values, evaluate_rows(pk, &acc.trace).values);
        }
        holds.push(acc.is_satisfied(pk));
        if !holds[holds.len() - 1] {
            break;
        }
    }
    (acc, acc_v, holds)
}

fn check_honest_chains<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    for rounds in [&[1, 1, 1][..], &[2], &[3, 1], &[2, 2]] {
        let holds = fold_chain::<CS>(rounds, None);
        assert_eq!(holds, vec![true; rounds.len()], "rounds {rounds:?}");
    }
}

/// The relation fails at the fold of the corrupted instance.
fn check_corrupted_chains<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    // Instance 0 is the initial one; round `r` folds the next `rounds[r]`.
    for (rounds, corrupt, expected) in [
        (&[1, 1, 1][..], 2, vec![true, false]),
        (&[3, 1], 1, vec![false]),
        (&[2, 2], 4, vec![true, false]),
    ] {
        let holds = fold_chain::<CS>(rounds, Some(corrupt));
        assert_eq!(holds, expected, "rounds {rounds:?}, corrupted {corrupt}");
    }
}

/// Proves the decider on `acc`, then checks the proof against `acc_v` (must
/// verify) and against a copy with a wrong error term (must not).
fn check_decider_accepts<CS: PolynomialCommitmentScheme<Fq>>(
    params: &CS::Parameters,
    pk: &ProvingKey<Fq, CS>,
    acc: ProverAccumulator<'_, Fq, CS>,
    acc_v: &Accumulator<Fq, CS>,
) where
    CS::Commitment: Hashable<State>,
{
    let mut transcript = T::init();
    prove_relaxed_trace(params, pk, acc, &mut transcript).unwrap();
    let proof = transcript.finalize();

    let verify = |acc_v: &Accumulator<Fq, CS>| {
        verify_relaxed_trace(pk.get_vk(), acc_v, &mut T::init_from_bytes(&proof))
            .and_then(|guard| {
                guard.verify(&CS::get_verifier_params(params)).map_err(|_| Error::Opening)
            })
            .is_ok()
    };
    assert!(verify(acc_v), "honest accumulator rejected");
    let mut wrong = acc_v.clone();
    wrong.error += Fq::ONE;
    assert!(!verify(&wrong), "wrong error term accepted");
}

/// The decider accepts the final accumulator of honest chains, and rejects
/// the same proof against a wrong error term.
fn check_decider<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    for rounds in [&[1, 1][..], &[2]] {
        let (acc, acc_v, holds) = run_chain(&params, &pk, rounds, None);
        assert_eq!(holds, vec![true; rounds.len()], "rounds {rounds:?}");
        check_decider_accepts(&params, &pk, acc, &acc_v);
    }
}

/// The decider on a fresh accumulator (no fold) accepts.
fn check_decider_init<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    let (instance, read) = fresh_instance(&params, &pk, 0, false);
    let acc = ProverAccumulator::init(&pk, instance, &mut T::init()).unwrap();
    let acc_v = Accumulator::init(pk.get_vk(), read, &mut T::init()).unwrap();
    check_decider_accepts(&params, &pk, acc, &acc_v);
}

/// `G(X) = Σᵢ powᵢ(β⃗*)·fᵢ(Σⱼ Lⱼ(X)·ωⱼ)` of 3 honest traces, with `k = 2`,
/// has degree at most `d·k`: interpolated at `d·k + 2` points, its top
/// coefficient vanishes.
fn check_folding_degree<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    let (instances, _): (Vec<_>, Vec<_>) =
        (0..3).map(|i| fresh_instance(&params, &pk, i, false)).unzip();
    let traces: Vec<_> = instances.iter().map(|i| &i.trace).collect();

    let (k, d) = (2, folding_degree(&pk.get_vk().cs));
    let betas: Vec<Fq> = (0..K).map(|_| Fq::random(OsRng)).collect();
    let pows = pow_vector(&betas);
    let g = |x: Fq| {
        let folded = linear_combination(&traces, &lagrange_basis(k, x));
        inner_product(&pows, &evaluate_rows(&pk, &folded))
    };

    let points: Vec<Fq> = (0..d * k + 2).map(|_| Fq::random(OsRng)).collect();
    let evals: Vec<Fq> = points.iter().map(|x| g(*x)).collect();
    let coeffs = interpolate(&points, &evals);
    assert_eq!(coeffs.len(), d * k + 2);
    assert_eq!(
        coeffs[d * k + 1],
        Fq::ZERO,
        "G has degree above d·k, d = {d}"
    );
}

fn check_empty_fresh<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    let (instance, read) = fresh_instance(&params, &pk, 0, false);
    let acc = ProverAccumulator::init(&pk, instance, &mut T::init()).unwrap();
    let acc_v = Accumulator::init(pk.get_vk(), read, &mut T::init()).unwrap();

    let folded = acc_v.fold(pk.get_vk(), &[], None, &mut T::init_from_bytes(&[]));
    assert!(matches!(folded, Err(Error::InvalidInstances)));
    let folded = acc.fold(&pk, vec![], None, &mut T::init());
    assert!(matches!(folded, Err(Error::InvalidInstances)));
}

/// Rounds absorbing a caller-provided hash instead of the accumulator: the
/// verifier agrees with the prover when passing the same hash, and rejects
/// (another `γ`, so the products do not match) when passing another one.
fn check_acc_hash<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    let vk = pk.get_vk();
    let (instance, read) = fresh_instance(&params, &pk, 0, false);
    let mut acc = ProverAccumulator::init(&pk, instance, &mut T::init()).unwrap();
    let mut acc_v = Accumulator::init(vk, read, &mut T::init()).unwrap();

    for round in 1..=2 {
        let (instance, read) = fresh_instance(&params, &pk, round, false);
        let hash = Some(Fq::from(round as u64));

        let mut transcript = T::init();
        acc = acc.fold(&pk, vec![instance], hash, &mut transcript).unwrap();
        let bytes = transcript.finalize();

        let verify = |hash| {
            acc_v.fold(
                vk,
                std::slice::from_ref(&read),
                hash,
                &mut T::init_from_bytes(&bytes),
            )
        };
        assert!(matches!(
            verify(Some(Fq::from(100))),
            Err(Error::InvalidInstances)
        ));
        acc_v = verify(hash).unwrap();
        assert_eq!(&acc_v, acc.accumulator());
        assert!(acc.is_satisfied(&pk));
    }
}

fn check_round_trip<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let circuit = SquareCircuit::default();
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &circuit, K).unwrap();
    let pk = keygen_pk(vk, &circuit).unwrap();

    let (instance, bytes) = commit(&params, &pk, circuit);
    let public_input = [circuit.public_input()];
    let read: FoldingInstance<Fq, CS> = read_instance(
        pk.get_vk(),
        &[&public_input],
        &mut T::init_from_bytes(&bytes),
    )
    .unwrap();

    assert_eq!(&read, instance.public());
    assert_eq!(read.instances(), [public_input.to_vec()]);
    assert!(!read.challenges().theta.is_empty() && read.challenges().y.len() > 1);
}

fn check_commitment_combination<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &SquareCircuit::default(), K).unwrap();
    let pk = keygen_pk(vk, &SquareCircuit::default()).unwrap();

    let (a, _) = commit(&params, &pk, SquareCircuit::default());
    let other = SquareCircuit {
        start: 3,
        corrupt: false,
    };
    let (b, _) = commit(&params, &pk, other);
    let weights = [Fq::random(OsRng), Fq::random(OsRng)];

    let combined =
        FoldingInstance::linear_combination(&[a.public(), b.public()], &weights).unwrap();

    // The phase-1 group of the combined witness, committed as `commit_phases`
    // does (into a throwaway transcript).
    let group = Committed::linear_combination(
        &[&a.trace.phase1_committed, &b.trace.phase1_committed],
        &weights,
    );
    let polys = group.par_polys().map(|(l, p)| (l.clone(), p.clone())).collect();
    let (_, commitment) =
        Committed::commit::<CS, _, _>(&params, polys, Polynomial::to_delta, &mut T::init())
            .unwrap();
    assert!(combined.phase1_commitment() == &commitment);
}

/// Rows used by [`GateMixCircuit`].
const MIX_ROWS: usize = 16;

/// Gates of every shape the sparse evaluator treats differently: a fixed
/// query at a nonzero rotation as gating factor, a polynomial whose top node
/// is a `Sum` (ungated), and a product of two selectors.
#[derive(Clone, Copy, Default)]
struct GateMixCircuit {
    start: u64,
}

#[derive(Clone, Debug)]
struct GateMixConfig {
    s1: Selector,
    s2: Selector,
    q: Column<Fixed>,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
}

impl Circuit<Fq> for GateMixCircuit {
    type Config = GateMixConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        *self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> GateMixConfig {
        let config = GateMixConfig {
            s1: meta.complex_selector(),
            s2: meta.complex_selector(),
            q: meta.fixed_column(),
            a: meta.advice_column(),
            b: meta.advice_column(),
            c: meta.advice_column(),
        };
        meta.create_gate("mix", |meta| {
            let s1 = meta.query_selector(config.s1);
            let s2 = meta.query_selector(config.s2);
            let q_next = meta.query_fixed(config.q, Rotation::next());
            let q_prev = meta.query_fixed(config.q, Rotation::prev());
            let a = meta.query_advice(config.a, Rotation::cur());
            let b = meta.query_advice(config.b, Rotation::cur());
            let c = meta.query_advice(config.c, Rotation::cur());
            Constraints::without_selector(vec![
                // Gated by a fixed query at a shifted rotation.
                q_next * (a.clone() - b.clone()),
                q_prev * s1 * (a.clone() * b.clone() - c.clone()),
                // Top node is a `Sum`: active on every row.
                a.clone() + b.clone() - c.clone(),
                // Product of two selectors.
                s2 * meta.query_selector(config.s1) * (a * b - c),
            ])
        });
        config
    }

    fn synthesize(
        &self,
        config: GateMixConfig,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mix",
            |mut region| {
                for row in 0..MIX_ROWS {
                    // Different supports for each selector and for `q`.
                    if row % 2 == 0 {
                        config.s1.enable(&mut region, row)?;
                    }
                    if row % 3 == 0 {
                        config.s2.enable(&mut region, row)?;
                    }
                    if row % 5 != 4 {
                        region.assign_fixed(|| "q", config.q, row, || Value::known(Fq::ONE))?;
                    }
                    let a = Fq::from(self.start + row as u64 + 1);
                    let b = Fq::from(2 * self.start + 3 * row as u64 + 1);
                    region.assign_advice(|| "a", config.a, row, || Value::known(a))?;
                    region.assign_advice(|| "b", config.b, row, || Value::known(b))?;
                    region.assign_advice(|| "c", config.c, row, || Value::known(a * b))?;
                }
                Ok(())
            },
        )
    }
}

/// Commit phases of `circuit` (with the given public inputs) as a fresh
/// instance; returns its trace.
fn trace_of<'a, CS: PolynomialCommitmentScheme<Fq>, C: Circuit<Fq>>(
    params: &CS::Parameters,
    pk: &'a ProvingKey<Fq, CS>,
    circuit: &C,
    instances: &[&[Fq]],
) -> ProverTrace<'a, Fq, LagrangeCoeff>
where
    CS::Commitment: Hashable<State>,
{
    commit_instance(params, pk, circuit, instances, &mut T::init(), OsRng)
        .unwrap()
        .trace
}

/// The row-sparse evaluation agrees with the dense one, row by row. Returns
/// whether some row is nonzero.
fn assert_sparse_matches_dense<CS: PolynomialCommitmentScheme<Fq>>(
    pk: &ProvingKey<Fq, CS>,
    trace: &ProverTrace<'_, Fq, LagrangeCoeff>,
) -> bool {
    let sparse = evaluate_rows(pk, trace);
    let dense = evaluate_rows_dense(pk, trace);
    assert_eq!(sparse.len(), dense.len());
    for (row, (s, d)) in sparse.iter().zip(dense.iter()).enumerate() {
        assert_eq!(s, d, "sparse and dense evaluations differ on row {row}");
    }
    sparse.iter().any(|v| *v != Fq::ZERO)
}

fn check_sparse_matches_dense<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let weights = [Fq::random(OsRng), Fq::random(OsRng)];

    // SquareCircuit: honest, corrupted and linearly combined traces.
    let (_, pk) = setup::<CS>();
    let square = |start, corrupt| SquareCircuit { start, corrupt };
    let trace = |c: SquareCircuit| trace_of(&params, &pk, &c, &[&[c.public_input()]]);
    let (a, b) = (trace(square(0, false)), trace(square(3, false)));
    assert!(!assert_sparse_matches_dense(&pk, &a));
    assert!(assert_sparse_matches_dense(&pk, &trace(square(0, true))));
    let combined = linear_combination(&[&a, &b], &weights);
    assert!(assert_sparse_matches_dense(&pk, &combined));

    // GateMixCircuit.
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &GateMixCircuit::default(), K).unwrap();
    let pk = keygen_pk(vk, &GateMixCircuit::default()).unwrap();
    let mix = |start| trace_of(&params, &pk, &GateMixCircuit { start }, &[]);
    let (a, b) = (mix(0), mix(5));
    assert_sparse_matches_dense(&pk, &a);
    let combined = linear_combination(&[&a, &b], &weights);
    assert!(assert_sparse_matches_dense(&pk, &combined));
}

#[test]
fn sparse_matches_dense_kzg() {
    check_sparse_matches_dense::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn sparse_matches_dense_fflonk() {
    check_sparse_matches_dense::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn round_trip_kzg() {
    check_round_trip::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn round_trip_fflonk() {
    check_round_trip::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn commitment_combination_kzg() {
    check_commitment_combination::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn commitment_combination_fflonk() {
    check_commitment_combination::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn honest_chains_kzg() {
    check_honest_chains::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn honest_chains_fflonk() {
    check_honest_chains::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn corrupted_chains_kzg() {
    check_corrupted_chains::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn corrupted_chains_fflonk() {
    check_corrupted_chains::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn folding_degree_bounds_g_kzg() {
    check_folding_degree::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn folding_degree_bounds_g_fflonk() {
    check_folding_degree::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn empty_fresh_is_an_error_kzg() {
    check_empty_fresh::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn empty_fresh_is_an_error_fflonk() {
    check_empty_fresh::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn acc_hash_kzg() {
    check_acc_hash::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn acc_hash_fflonk() {
    check_acc_hash::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn decider_kzg() {
    check_decider::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn decider_fflonk() {
    check_decider::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn decider_init_kzg() {
    check_decider_init::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn decider_init_fflonk() {
    check_decider_init::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

/// Proves `k` circuits one-shot (circuit `i` is the `i`-th of a chain, the
/// `corrupt`-th has a broken gate) and verifies against the honest public
/// inputs (or, with `wrong_inputs`, ones with the last altered). `None` if
/// the prover fails.
fn one_shot_verifies<CS: PolynomialCommitmentScheme<Fq>>(
    k: usize,
    corrupt: Option<usize>,
    wrong_inputs: bool,
) -> Option<bool>
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    let circuits: Vec<_> = (0..k)
        .map(|i| SquareCircuit {
            start: 3 * i as u64,
            corrupt: corrupt == Some(i),
        })
        .collect();
    let inputs: Vec<[Fq; 1]> = circuits.iter().map(|c| [c.public_input()]).collect();
    let cols: Vec<[&[Fq]; 1]> = inputs.iter().map(|i| [&i[..]]).collect();
    let prove_instances: Vec<&[&[Fq]]> = cols.iter().map(|c| &c[..]).collect();

    let mut transcript = T::init();
    prove_one_shot(
        &params,
        &pk,
        &circuits,
        &prove_instances,
        &mut transcript,
        OsRng,
    )
    .ok()?;
    let proof = transcript.finalize();

    let mut claimed = inputs.clone();
    if wrong_inputs {
        claimed[k - 1][0] += Fq::ONE;
    }
    let cols: Vec<[&[Fq]; 1]> = claimed.iter().map(|i| [&i[..]]).collect();
    let verify_instances: Vec<&[&[Fq]]> = cols.iter().map(|c| &c[..]).collect();
    Some(
        verify_one_shot(
            pk.get_vk(),
            &verify_instances,
            &mut T::init_from_bytes(&proof),
        )
        .and_then(|guard| {
            guard.verify(&CS::get_verifier_params(&params)).map_err(|_| Error::Opening)
        })
        .is_ok(),
    )
}

fn check_one_shot_honest<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    for k in [1, 2, 4] {
        assert_eq!(
            one_shot_verifies::<CS>(k, None, false),
            Some(true),
            "k = {k}"
        );
    }
}

fn check_one_shot_wrong_inputs<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    for k in [1, 2] {
        assert_eq!(
            one_shot_verifies::<CS>(k, None, true),
            Some(false),
            "k = {k}"
        );
    }
}

fn check_one_shot_corrupted<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    assert_ne!(one_shot_verifies::<CS>(3, Some(1), false), Some(true));
}

fn check_one_shot_empty<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let (params, pk) = setup::<CS>();
    let result =
        prove_one_shot::<Fq, CS, T, SquareCircuit>(&params, &pk, &[], &[], &mut T::init(), OsRng);
    assert!(matches!(result, Err(Error::InvalidInstances)));
    let result = verify_one_shot::<Fq, CS, T>(pk.get_vk(), &[], &mut T::init_from_bytes(&[]));
    assert!(matches!(result, Err(Error::InvalidInstances)));
}

#[test]
fn one_shot_honest_kzg() {
    check_one_shot_honest::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn one_shot_honest_fflonk() {
    check_one_shot_honest::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn one_shot_wrong_inputs_kzg() {
    check_one_shot_wrong_inputs::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn one_shot_wrong_inputs_fflonk() {
    check_one_shot_wrong_inputs::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn one_shot_corrupted_kzg() {
    check_one_shot_corrupted::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn one_shot_corrupted_fflonk() {
    check_one_shot_corrupted::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

#[test]
fn one_shot_empty_kzg() {
    check_one_shot_empty::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn one_shot_empty_fflonk() {
    check_one_shot_empty::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

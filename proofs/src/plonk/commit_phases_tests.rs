//! The commit phases of the prover ([`commit_phases`]) and of the verifier
//! ([`parse_trace`]) agree on the commitments and on the challenges.

use blake2b_simd::State;
use ff::Field;
use midnight_curves::{Bls12, Fq};
use rand_core::OsRng;
use rayon::iter::ParallelIterator;

use super::{
    Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Instance, Selector,
    TableColumn, argument::prover::Committed, create_proof, keygen_pk, keygen_vk_with_k,
    parse_trace, prepare, prover::commit_phases,
};
use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    poly::{
        Polynomial, PolynomialLabel, PolynomialRepresentation, Rotation,
        commitment::{Guard, PolynomialCommitmentScheme},
        fflonk::Fflonk,
        kzg::KZGCommitmentScheme,
    },
    transcript::{CircuitTranscript, Hashable, Transcript},
};

const K: u32 = 6;
const TABLE_SIZE: u64 = 16;

type T = CircuitTranscript<State>;

/// `b = a²` on enabled rows, `a ∈ {1..16}` by lookup, `b` of row 0 is public.
#[derive(Clone, Copy)]
struct SquareCircuit;

#[derive(Clone, Debug)]
struct SquareConfig {
    s: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    table: TableColumn,
    instance: Column<Instance>,
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
                for row in 0..TABLE_SIZE {
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
                for row in 0..TABLE_SIZE {
                    config.s.enable(&mut region, row as usize)?;
                    let a = Fq::from(row + 1);
                    region.assign_advice(|| "a", config.a, row as usize, || Value::known(a))?;
                    let b = region.assign_advice(
                        || "b",
                        config.b,
                        row as usize,
                        || Value::known(a.square()),
                    )?;
                    first_b.get_or_insert(b.cell());
                }
                Ok(first_b.unwrap())
            },
        )?;

        layouter.constrain_instance(first_b, config.instance, 0)
    }
}

/// Commits to the polynomials of `group` as the prover does.
fn recommit<CS, B, E>(
    params: &CS::Parameters,
    group: &Committed<Fq, B>,
    encode: impl Fn(&Polynomial<Fq, B>) -> Polynomial<Fq, E> + Send + Sync,
) -> CS::Commitment
where
    CS: PolynomialCommitmentScheme<Fq>,
    B: PolynomialRepresentation,
    E: PolynomialRepresentation,
{
    let (labels, polys): (Vec<PolynomialLabel>, Vec<_>) =
        group.par_polys().map(|(label, poly)| (label.clone(), encode(poly))).unzip();
    CS::commit_many(params, &polys.iter().collect::<Vec<_>>(), &labels)
}

fn check_commit_phases<CS: PolynomialCommitmentScheme<Fq>>()
where
    CS::Commitment: Hashable<State>,
{
    let params = CS::gen_params(K);
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &SquareCircuit, K).unwrap();
    let pk = keygen_pk(vk, &SquareCircuit).unwrap();
    let vk = pk.get_vk();
    let instance = [Fq::ONE];
    let instances: &[&[Fq]] = &[&instance];

    // Prover: commit phases only.
    let mut prover_transcript = T::init();
    let committed = commit_phases(
        &params,
        &pk,
        &SquareCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        &mut prover_transcript,
        OsRng,
    )
    .unwrap();
    let trace = &committed.trace;
    assert!(!trace.theta.is_empty() && trace.y.len() > 1);

    // The returned Lagrange polynomials are the committed ones.
    let phase1 = recommit::<CS, _, _>(&params, &trace.phase1_committed, Polynomial::to_delta);
    let phase2 = recommit::<CS, _, _>(
        &params,
        &trace.phase2_committed,
        Polynomial::to_double_delta,
    );
    assert_eq!(phase1, committed.phase1_commitment);
    assert_eq!(phase2, committed.phase2_commitment);

    // Verifier: read the commit phases from the same bytes.
    let prover_after: Fq = prover_transcript.squeeze_challenge();
    let bytes = prover_transcript.finalize();
    let mut verifier_transcript = T::init_from_bytes(&bytes);
    let parsed = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        &mut verifier_transcript,
    )
    .unwrap();

    assert_eq!(parsed.phase1_commitment(), &committed.phase1_commitment);
    assert_eq!(parsed.phase2_commitment(), &committed.phase2_commitment);
    assert_eq!(parsed.theta, trace.theta);
    assert_eq!(parsed.beta, trace.beta);
    assert_eq!(parsed.gamma, trace.gamma);
    assert_eq!(parsed.trash_challenge, trace.trash_challenge);
    assert_eq!(parsed.y, trace.y);
    // Both transcripts are left in the same state.
    let verifier_after: Fq = verifier_transcript.squeeze_challenge();
    assert_eq!(verifier_after, prover_after);

    // The full proof, which starts with the same commit phases, still verifies.
    let mut transcript = T::init();
    create_proof::<_, CS, _, _>(
        &params,
        &pk,
        &SquareCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        &mut transcript,
        OsRng,
    )
    .unwrap();
    let proof = transcript.finalize();
    let mut transcript = T::init_from_bytes(&proof);
    let guard = prepare::<_, CS, _>(
        vk,
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        &mut transcript,
    )
    .unwrap();
    guard.verify(&CS::get_verifier_params(&params)).unwrap();
}

#[test]
fn commit_phases_match_verifier_kzg() {
    check_commit_phases::<KZGCommitmentScheme<Bls12>>();
}

#[test]
fn commit_phases_match_verifier_fflonk() {
    check_commit_phases::<Fflonk<KZGCommitmentScheme<Bls12>, 3>>();
}

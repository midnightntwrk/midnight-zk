//! The configurable lookup chunk bound: more helper columns, lower folding
//! degree, and proofs that still verify.

use blake2b_simd::State;
use midnight_curves::{Bls12, Fq};
use rand_core::OsRng;

use super::{
    Advice, Circuit, Column, ConstraintSystem, Constraints, Error, TableColumn, create_proof,
    keygen_pk, keygen_vk_with_k, prepare, protogalaxy::folding_degree,
};
use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    poly::{
        Rotation,
        commitment::{Guard, PolynomialCommitmentScheme},
        kzg::KZGCommitmentScheme,
    },
    transcript::{CircuitTranscript, Transcript},
};

const K: u32 = 5;
const TABLE_SIZE: u64 = 8;
const NB_TUPLES: usize = 4;

/// Four degree-1 lookup tuples into one table, next to a degree-5 gate (so the
/// circuit degree is 5 and, by default, all tuples fit in one helper). A
/// `BOUND` of 0 leaves the bound unset.
#[derive(Clone, Copy, Default)]
struct BatchedLookupCircuit<const BOUND: usize>;

#[derive(Clone, Debug)]
struct Config {
    advice: [Column<Advice>; NB_TUPLES],
    table: TableColumn,
}

impl<const BOUND: usize> Circuit<Fq> for BatchedLookupCircuit<BOUND> {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        *self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Config {
        let advice = [(); NB_TUPLES].map(|_| meta.advice_column());
        let table = meta.lookup_table_column();

        meta.create_gate("degree 5", |meta| {
            let a = meta.query_advice(advice[0], Rotation::cur());
            let a5 = a.clone() * a.clone() * a.clone() * a.clone() * a;
            Constraints::without_selector(vec![a5.clone() - a5])
        });

        meta.batched_lookup("range", None, |meta| {
            let inputs = advice.iter().map(|c| meta.query_advice(*c, Rotation::cur())).collect();
            vec![(inputs, table)]
        });

        if BOUND != 0 {
            meta.set_lookup_chunk_bound(BOUND);
        }
        Config { advice, table }
    }

    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                for row in 0..TABLE_SIZE {
                    let value = Value::known(Fq::from(row));
                    table.assign_cell(|| "t", config.table, row as usize, || value)?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "inputs",
            |mut region| {
                for row in 0..TABLE_SIZE as usize {
                    for (i, column) in config.advice.iter().enumerate() {
                        let v = Fq::from((row + i) as u64 % TABLE_SIZE);
                        region.assign_advice(|| "a", *column, row, || Value::known(v))?;
                    }
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

type CS = KZGCommitmentScheme<Bls12>;

fn cs_of<C: Circuit<Fq> + Default>() -> ConstraintSystem<Fq> {
    let mut cs = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    C::configure_with_params(&mut cs, C::params(&C::default()));
    #[cfg(not(feature = "circuit-params"))]
    C::configure(&mut cs);
    cs
}

#[test]
fn bound_gives_more_chunks_and_lower_folding_degree() {
    let default = cs_of::<BatchedLookupCircuit<0>>();
    let bounded = cs_of::<BatchedLookupCircuit<3>>();
    assert_eq!(default.degree(), 5);
    assert_eq!(default.lookup_chunk_bound(), 5);
    assert_eq!(bounded.lookup_chunk_bound(), 3);

    assert_eq!(
        default.lookups()[0].num_chunks(default.lookup_chunk_bound()),
        1
    );
    assert_eq!(
        bounded.lookups()[0].num_chunks(bounded.lookup_chunk_bound()),
        2
    );
    assert!(bounded.nb_y_challenges() > default.nb_y_challenges());
    assert!(folding_degree(&bounded) < folding_degree(&default));
}

#[test]
fn pinned_form_changes_only_when_bound_is_set() {
    let default = format!("{:?}", cs_of::<BatchedLookupCircuit<0>>().pinned());
    let bounded = format!("{:?}", cs_of::<BatchedLookupCircuit<3>>().pinned());
    assert!(!default.contains("lookup_chunk_bound"));
    assert!(bounded.contains("lookup_chunk_bound: Some(3)"));
}

#[test]
fn proof_with_bound_verifies() {
    let params = CS::gen_params(K);
    let circuit = BatchedLookupCircuit::<3>;
    let vk = keygen_vk_with_k::<_, CS, _>(&params, &circuit, K).unwrap();
    let pk = keygen_pk(vk, &circuit).unwrap();
    let instances: &[&[Fq]] = &[];

    let mut transcript = CircuitTranscript::<State>::init();
    create_proof::<_, CS, _, _>(
        &params,
        &pk,
        &circuit,
        #[cfg(feature = "committed-instances")]
        0,
        instances,
        &mut transcript,
        OsRng,
    )
    .unwrap();
    let proof = transcript.finalize();
    let mut transcript = CircuitTranscript::<State>::init_from_bytes(&proof);
    let guard = prepare::<_, CS, _>(
        pk.get_vk(),
        #[cfg(feature = "committed-instances")]
        &[],
        instances,
        &mut transcript,
    )
    .unwrap();
    guard.verify(&CS::get_verifier_params(&params)).unwrap();
}

#[test]
#[should_panic(expected = "lookup chunk bound 1 must be in 2..=")]
fn bound_below_two_panics() {
    let mut cs = ConstraintSystem::<Fq>::default();
    cs.set_lookup_chunk_bound(1);
    cs.lookup_chunk_bound();
}

#[test]
#[should_panic(expected = "lookup chunk bound 9 must be in 2..=")]
fn bound_above_degree_panics() {
    let mut cs = cs_of::<BatchedLookupCircuit<0>>();
    cs.set_lookup_chunk_bound(9);
    cs.lookup_chunk_bound();
}

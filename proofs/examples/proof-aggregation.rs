use std::{convert::TryInto, time::Instant};

use ff::Field;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        compute_trace, finalise_proof, keygen_pk, keygen_vk_with_k, traces::ProverTrace, Advice,
        Circuit, Column, ConstraintSystem, Error, Expression, Selector, TableColumn,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        EvaluationDomain, Rotation,
    },
    protogalaxy::{prover::fold, FoldingPk},
    transcript::{CircuitTranscript, Transcript},
};
use rand_chacha::{
    rand_core::{RngCore, SeedableRng},
    ChaCha8Rng,
};

#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[derive(Clone, Copy)]
struct TestCircuit {
    witness: [Value<Fq>; 1 << 8],
}

impl TestCircuit {
    fn from(witness: [Value<Fq>; 1 << 8]) -> Self {
        Self { witness }
    }
}

#[derive(Debug, Clone)]
struct MyConfig {
    mul_selector: Selector,
    table_selector: Selector,
    table: TableColumn,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
}

impl Circuit<Fq> for TestCircuit {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            witness: [Value::unknown(); 1 << 8],
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> MyConfig {
        let config = MyConfig {
            mul_selector: meta.complex_selector(),
            table_selector: meta.complex_selector(),
            table: meta.lookup_table_column(),
            a: meta.advice_column(),
            b: meta.advice_column(),
            c: meta.advice_column(),
        };

        meta.enable_equality(config.a);
        meta.enable_equality(config.b);

        meta.create_gate("mul", |meta| {
            let a = meta.query_advice(config.a, Rotation::cur());
            let b = meta.query_advice(config.b, Rotation::cur());
            let c = meta.query_advice(config.c, Rotation::cur());
            let q = meta.query_selector(config.mul_selector);
            vec![q * (a * b - c)]
        });

        meta.lookup("lookup", |meta| {
            let selector = meta.query_selector(config.table_selector);
            let not_selector = Expression::Constant(Fq::ONE) - selector.clone();

            let a = meta.query_advice(config.a, Rotation::cur());
            vec![(selector * a + not_selector, config.table)]
        });

        config
    }

    fn synthesize(&self, config: MyConfig, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        layouter.assign_table(
            || "8-bit table",
            |mut table| {
                for row in 0u64..(1 << 8) {
                    table.assign_cell(
                        || format!("row {row}"),
                        config.table,
                        row as usize,
                        || Value::known(Fq::from(row + 1)),
                    )?;
                }

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assign values",
            |mut region| {
                for (offset, val) in self.witness.into_iter().enumerate() {
                    config.table_selector.enable(&mut region, offset)?;
                    config.mul_selector.enable(&mut region, offset)?;
                    let a = region.assign_advice(|| "a", config.a, offset, || val)?;
                    a.copy_advice(|| "copy a to b", &mut region, config.b, offset)?;
                    // region.assign_advice(|| "b", config.b, offset, || val)?;
                    region.assign_advice(|| "c", config.c, offset, || val.map(|v| v * v))?;
                }

                Ok(())
            },
        )?;

        Ok(())
    }
}

fn main() {
    const K: u32 = 15;
    let k = 8; // number of folding instances

    // setup memory profiler
    let profiler = dhat::Profiler::new_ad_hoc();

    let rng = ChaCha8Rng::from_seed([0u8; 32]);
    let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, rng);

    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    let mut rand_bytes = [0u8; 1 << 8];
    rng.fill_bytes(&mut rand_bytes);

    let witnesses = (0..k)
        .map(|_| {
            rand_bytes
                .into_iter()
                .map(|byte| Value::known(Fq::from((byte as u64) + 1)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        })
        .collect::<Vec<_>>();
    let circuits = witnesses
        .into_iter()
        .map(TestCircuit::from)
        .collect::<Vec<_>>();

    let vk = keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuits[0], K)
        .expect("keygen_vk should not fail");
    let pk = keygen_pk(vk.clone(), &circuits[0]).expect("keygen_pk should not fail");

    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

    // Compute traces
    let folding = Instant::now();
    let now = Instant::now();
    let mut transcript = CircuitTranscript::init();

    let traces = circuits
        .into_iter()
        .map(|c| {
            compute_trace(
                &params,
                &pk,
                &[c],
                #[cfg(feature = "committed-instances")]
                0,
                &[&[]],
                &mut rng,
                &mut transcript,
            )
            .expect("Failed to compute the folding trace")
            .into_folding_trace(pk.fixed_values.clone())
        })
        .collect::<Vec<_>>();

    let traces_time = now.elapsed().as_millis();

    // We now perform folding of the traces
    let degree = pk.get_vk().cs().degree() as u32;

    let k_log2_ceil = (k as f64 - 1.).log2() as u32 + 1;
    // We must increase the degree, since we need to count y as a variable.
    // Computing the real degree seems hard.
    let dk_domain = EvaluationDomain::new(degree + 3, k_log2_ceil);
    let folding_pk = FoldingPk::from(pk.clone());
    let folded_trace = fold(&folding_pk, &dk_domain, &traces.iter().collect::<Vec<&_>>());

    let folding_time = folding.elapsed().as_millis();
    // Now we create the final proof
    let final_pk = folding_pk.into_proving_key(&folded_trace, &vk);
    finalise_proof(
        &params,
        &final_pk,
        #[cfg(feature = "committed-instances")]
        0,
        ProverTrace::from_folding_trace(folded_trace),
        &mut transcript,
    )
    .expect("Failed to finalise proof");

    let final_proof_time = folding.elapsed().as_millis() - folding_time;

    // Now we see how long it would have taken to produce four normal proofs
    let now = Instant::now();
    let mut finalise_transcript = transcript.clone();

    traces
        .into_iter()
        .try_for_each(|t| {
            finalise_proof(
                &params,
                &pk,
                #[cfg(feature = "committed-instances")]
                0,
                ProverTrace::from_folding_trace(t),
                &mut finalise_transcript,
            )
        })
        .expect("Failed to finalise proofs");

    let full_proof_time = now.elapsed().as_millis();
    println!("Compute {k}    traces      :  {:?}ms", traces_time);
    println!(
        "Compute {k} full proofs    : {:?}ms",
        traces_time + full_proof_time
    );
    println!("Protogalaxy              : {:?}ms", folding_time);
    println!("Protogalaxy final time   : {:?}ms", final_proof_time);
}

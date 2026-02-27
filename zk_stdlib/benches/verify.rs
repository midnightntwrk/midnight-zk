//! Benchmarks for single and batch proof verification.

#[macro_use]
extern crate criterion;

use criterion::{BenchmarkId, Criterion, Throughput};
use ff::Field;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use rand::{rngs::OsRng, SeedableRng};
use rand_chacha::ChaCha8Rng;

type F = midnight_curves::Fq;

/// Minimal Poseidon circuit used as the benchmark relation.
#[derive(Clone, Default)]
struct PoseidonBench;

impl Relation for PoseidonBench {
    type Instance = F;
    type Witness = [F; 3];

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonBench)
    }
}

const BATCH_SIZE: usize = 25;

fn bench_verify(c: &mut Criterion) {
    let srs = filecoin_srs(6);
    let relation = PoseidonBench;
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let params_verifier = srs.verifier_params();

    let proofs: Vec<(F, Vec<u8>)> = (0..BATCH_SIZE)
        .map(|_| {
            let mut rng = ChaCha8Rng::from_entropy();
            let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
            let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);
            let proof = midnight_zk_stdlib::prove::<PoseidonBench, blake2b_simd::State>(
                &srs, &pk, &relation, &instance, witness, OsRng,
            )
            .expect("proof generation failed");
            (instance, proof)
        })
        .collect();

    let vks: Vec<_> = (0..BATCH_SIZE).map(|_| vk.clone()).collect();
    let pis: Vec<Vec<F>> = proofs
        .iter()
        .map(|(inst, _)| PoseidonBench::format_instance(inst).expect("format_instance failed"))
        .collect();
    let proof_bytes: Vec<Vec<u8>> = proofs.iter().map(|(_, p)| p.clone()).collect();

    let (instance, proof) = &proofs[0];
    let mut group = c.benchmark_group("verify");
    group.sample_size(20);
    group.throughput(Throughput::Elements(1));
    group.bench_function("single", |b| {
        b.iter(|| {
            midnight_zk_stdlib::verify::<PoseidonBench, blake2b_simd::State>(
                &params_verifier,
                &vk,
                instance,
                None,
                proof,
            )
            .expect("verify failed");
        });
    });

    group.throughput(Throughput::Elements(BATCH_SIZE as u64));
    group.bench_function(BenchmarkId::new("batch", BATCH_SIZE), |b| {
        b.iter(|| {
            midnight_zk_stdlib::batch_verify::<blake2b_simd::State>(
                &params_verifier,
                &vks,
                &pis,
                &proof_bytes,
            )
            .expect("batch_verify failed");
        });
    });

    group.finish();
}

criterion_group!(benches, bench_verify);
criterion_main!(benches);

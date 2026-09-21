use criterion::{Criterion, criterion_group, criterion_main};
use ff::Field;
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, permutation_cpu, round_skips::PreComputedRoundCPU},
    instructions::hash::HashCPU,
};
use rand::SeedableRng;
use rand_chacha::ChaCha12Rng;

type F = midnight_curves::Fq;

const WIDTH: usize = PoseidonChip::<F>::register_size();

fn bench_poseidon_cpu(c: &mut Criterion) {
    let pre_computed = PreComputedRoundCPU::init();

    let mut rng = ChaCha12Rng::seed_from_u64(0xf007ba11);
    let mut group = c.benchmark_group("sample-size-example");
    group.sample_size(500); // increase the sample size to reduce noise

    group.bench_function("bench_poseidon_cpu_optim", |b| {
        b.iter(|| {
            let mut input: [F; WIDTH] = core::array::from_fn(|_| F::random(&mut rng));
            std::hint::black_box({
                permutation_cpu(&pre_computed, &mut input);
                input
            })
        });
    });

    group.finish();
}

/// `HashCPU::hash`, the entry point a caller uses.
///
/// `bench_poseidon_cpu` hoists the pre-computation out of the loop; `hash`
/// pays it on every invocation, through `SpongeCPU::init`. The difference
/// between the two is that setup.
fn bench_poseidon_hash(c: &mut Criterion) {
    let mut rng = ChaCha12Rng::seed_from_u64(0xf007ba11);
    let mut group = c.benchmark_group("poseidon_hash");
    group.sample_size(500);
    // Two elements: a Merkle node's shape.
    let inputs: [F; 2] = core::array::from_fn(|_| F::random(&mut rng));
    group.bench_function("hash_2", |b| {
        b.iter(|| std::hint::black_box(<PoseidonChip<F> as HashCPU<F, F>>::hash(&inputs)))
    });
    group.finish();
}

criterion_group!(benches, bench_poseidon_cpu, bench_poseidon_hash);
criterion_main!(benches);

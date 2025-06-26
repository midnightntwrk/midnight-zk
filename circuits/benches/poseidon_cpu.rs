use criterion::{criterion_group, criterion_main, Criterion};
use ff::Field;
use midnight_circuits::hash::poseidon::{
    permutation_cpu, round_skips::PreComputedRoundCPU, PoseidonChip,
};
use rand::SeedableRng;
use rand_chacha::ChaCha12Rng;

type F = blstrs::Fq;

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

criterion_group!(benches, bench_poseidon_cpu);
criterion_main!(benches);

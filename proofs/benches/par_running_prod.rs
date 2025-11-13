use criterion::{criterion_group, criterion_main, Criterion};
use ff::Field;
use midnight_proofs::utils::arithmetic::parallelize_running_prod;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

type F = midnight_curves::Fq;

fn bench_speedup(c: &mut Criterion) {
    for k in 13..=18 {
        let n = 1usize << k;
        let mut rng = ChaCha8Rng::from_seed([0; 32]);
        let input: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();

        let group_name = format!("running_product_k_{}", k);
        let mut group = c.benchmark_group(&group_name);
        group.sample_size(100);

        // Benchmark sequential implementation
        group.bench_function("sequential", |b| {
            b.iter(|| {
                let mut result: Vec<F> = Vec::with_capacity(n);
                result.push(input[0]);
                for row in 1..n {
                    let mut tmp = result[row - 1];
                    tmp *= input[row];
                    result.push(tmp);
                }
                std::hint::black_box(result)
            });
        });

        // Benchmark parallel implementation
        group.bench_function("parallel", |b| {
            b.iter(|| {
                let mut data = input.clone();
                parallelize_running_prod(&mut data, n);
                std::hint::black_box(data)
            });
        });

        group.finish();
    }
}

criterion_group!(benches, bench_speedup);
criterion_main!(benches);

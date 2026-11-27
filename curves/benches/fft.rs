//! Benchmarks the pruned DIF FFT behind `EvaluationDomain::coeff_to_extended`.
//!
//! To run this benchmark:
//!
//!     cargo bench --bench fft

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use ff::{Field, PrimeField};
use midnight_curves::{
    Fq,
    fft::{compute_twiddles, fft_coeff_to_extended},
};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

/// Blow-up of the extended domain, as for a degree-4 constraint system.
const EXT: u32 = 2;

fn bench_coeff_to_extended(c: &mut Criterion) {
    let mut rng = XorShiftRng::seed_from_u64(0);
    let mut group = c.benchmark_group("fft_coeff_to_extended");
    for k in [14u32, 16, 18] {
        let ext_k = k + EXT;
        let omega = Fq::ROOT_OF_UNITY.pow_vartime([1u64 << (Fq::S - ext_k)]);
        let twiddles = compute_twiddles(&omega, ext_k);
        let coeffs: Vec<Fq> = (0..1 << k).map(|_| Fq::random(&mut rng)).collect();
        group.bench_with_input(BenchmarkId::from_parameter(k), &k, |b, &k| {
            b.iter_batched_ref(
                || {
                    let mut a = coeffs.clone();
                    a.resize(1 << ext_k, Fq::ZERO);
                    a
                },
                |a| fft_coeff_to_extended(a, &twiddles, ext_k, 1 << k),
                BatchSize::LargeInput,
            )
        });
    }
    group.finish();
}

criterion_group!(benches, bench_coeff_to_extended);
criterion_main!(benches);

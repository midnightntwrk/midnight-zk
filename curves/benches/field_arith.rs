//! Benchmark field arithmetic operations.
//! It measures the base field `Fp` and scalar field `Scalar` from the Bls12-381
//! curve. Note: The bencharks are generic and can be easily extended for Jubjub
//! scalar field and G2 base field Fp2.
//!
//! To run this benchmark:
//!
//!     cargo bench --bench field_arith

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use ff::Field;
use midnight_curves::*;
use rand_core::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;

const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

fn bench_field_arithmetic<F: Field>(c: &mut Criterion, name: &'static str) {
    let mut rng = XorShiftRng::from_seed(SEED);

    let a = <F as Field>::random(&mut rng);
    let b = <F as Field>::random(&mut rng);
    let mut ret = a;
    let exp = rng.next_u64();

    let mut group = c.benchmark_group(format!("{} arithmetic", name));

    group.significance_level(0.1).sample_size(1000);
    group.throughput(Throughput::Elements(1));

    group.bench_function(format!("{}_add", name), |bencher| {
        bencher.iter(|| black_box(&a).add(black_box(&b)))
    });

    group.bench_function(format!("{}_add_assign", name), |bencher| {
        bencher.iter(|| black_box(&mut ret).add_assign(black_box(&b)))
    });

    group.bench_function(format!("{}_sub", name), |bencher| {
        bencher.iter(|| black_box(&a).sub(black_box(&b)))
    });

    group.bench_function(format!("{}_sub_assign", name), |bencher| {
        bencher.iter(|| black_box(&mut ret).sub_assign(black_box(&b)))
    });

    group.bench_function(format!("{}_double", name), |bencher| {
        bencher.iter(|| black_box(&a).double())
    });

    group.bench_function(format!("{}_neg", name), |bencher| {
        bencher.iter(|| black_box(&a).neg())
    });

    group.bench_function(format!("{}_mul", name), |bencher| {
        bencher.iter(|| black_box(&a).mul(black_box(&b)))
    });

    group.bench_function(format!("{}_mul_assign", name), |bencher| {
        bencher.iter(|| black_box(&mut ret).mul_assign(black_box(&b)))
    });

    group.bench_function(format!("{}_square", name), |bencher| {
        bencher.iter(|| black_box(&a).square())
    });

    group.bench_function(format!("{}_pow_vartime", name), |bencher| {
        bencher.iter(|| black_box(&a).pow_vartime(black_box(&[exp])))
    });

    group.bench_function(format!("{}_invert", name), |bencher| {
        bencher.iter(|| black_box(&a).invert())
    });

    group.bench_function(format!("{}_sqrt", name), |bencher| {
        bencher.iter(|| black_box(&a).sqrt())
    });
    group.finish()
}

fn bench_bls_base_field(c: &mut Criterion) {
    bench_field_arithmetic::<Fp>(c, "base-field")
}

fn bench_bls_scalar_field(c: &mut Criterion) {
    bench_field_arithmetic::<Fq>(c, "scalar-field")
}

// fn bench_bls_fp2(c: &mut Criterion) {
//     bench_field_arithmetic::<Fp2>(c, "Fp2")
// }

criterion_group!(
    benches,
    bench_bls_base_field,
    bench_bls_scalar_field,
    // bench_bls_fp2
);
criterion_main!(benches);

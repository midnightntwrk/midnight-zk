//! Benchmark pairing and associated functions.
//!
//! To run this benchmark:
//!
//!     cargo bench --bench  pairing

use blstrs::{G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective};
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use group::Group;
use pairing_lib::{Engine, MillerLoopResult, MultiMillerLoop};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

fn bench_pairing(c: &mut Criterion) {
    let mut rng = XorShiftRng::from_seed(SEED);
    let g1_affine = G1Affine::from(G1Projective::random(&mut rng));
    let g2_projective = G2Projective::random(&mut rng);
    let g2_affine = G2Affine::from(&g2_projective);
    let g2_prepared = G2Prepared::from(g2_affine);

    let mm_loop_res = blstrs::Bls12::multi_miller_loop(&[(&g1_affine, &g2_prepared)]);

    let mut group = c.benchmark_group("Bls12-381 pairing");
    group.significance_level(0.1).sample_size(100);
    group.throughput(Throughput::Elements(1));

    group.bench_function("G2 prepare", |b| {
        b.iter(|| G2Prepared::from(black_box(g2_affine)))
    });

    group.bench_function("Multi-miller loop", |b| {
        b.iter(|| blstrs::Bls12::multi_miller_loop(black_box(&[(&g1_affine, &g2_prepared)])))
    });

    group.bench_function("Final exponentiantion", |b| {
        b.iter(|| black_box(mm_loop_res).final_exponentiation())
    });

    group.bench_function("Full Pairing", |b| {
        b.iter(|| blstrs::Bls12::pairing(black_box(&g1_affine), black_box(&g2_affine)))
    });

    group.finish();
}

criterion_group!(benches, bench_pairing);
criterion_main!(benches);

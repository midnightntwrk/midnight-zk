//! Benchmark EC operations.
//! It measures Bls12-381 G1 operations.
//! Note: The bencharks are generic and can be easily extended for G2 and
//! Jubjub.
//!
//! To run this benchmark:
//!
//!     cargo bench --bench ec

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use ff::Field;
use group::prime::PrimeCurveAffine;
use halo2curves::CurveExt;
use midnight_curves::G1Projective;
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

fn bench_curve_ops<G: CurveExt>(c: &mut Criterion, name: &'static str) {
    {
        let mut rng = XorShiftRng::seed_from_u64(0xdeadbeef);

        // Generate 2 random points.
        let mut p1 = G::random(&mut rng);
        let p2 = G::random(&mut rng);
        p1 += p2; // this makes p1's z!=1

        let p2_affine = G::AffineExt::from(p2);
        let mut ret = p1;

        let s = G::ScalarExt::random(&mut rng);

        const N: usize = 1000;
        let v: Vec<G> = (0..N).map(|_| p1 + G::random(&mut rng)).collect();

        let mut q = vec![G::AffineExt::identity(); N];

        let mut group = c.benchmark_group(format!("{} arithmetic", name));

        group.significance_level(0.1).sample_size(1000);
        group.throughput(Throughput::Elements(1));

        group.bench_function(format!("{name} check on curve"), move |b| {
            b.iter(|| black_box(p1).is_on_curve())
        });
        group.bench_function(format!("{name} check equality"), move |b| {
            b.iter(|| black_box(p1) == black_box(p1))
        });
        group.bench_function(format!("{name} to affine"), move |b| {
            b.iter(|| G::AffineExt::from(black_box(p1)))
        });

        group.bench_function(format!("{name} addition"), move |b| {
            b.iter(|| black_box(&p1).add(&p2))
        });

        group.bench_function(format!("{name} assigned addition"), move |b| {
            b.iter(|| black_box(&mut ret).add_assign(&p2))
        });

        group.bench_function(format!("{name} mixed addition"), move |b| {
            b.iter(|| black_box(&p1).add(&p2_affine))
        });

        ret = p1;
        group.bench_function(format!("{name} assigned mixed addition"), move |b| {
            b.iter(|| black_box(&mut ret).add(&p2_affine))
        });

        group.bench_function(format!("{name} scalar multiplication"), move |b| {
            b.iter(|| black_box(p1) * black_box(s))
        });

        group.bench_function(format!("{name} assigned scalar multiplication"), move |b| {
            b.iter(|| black_box(&mut ret).mul_assign(black_box(s)))
        });

        group.bench_function(format!("{name} doubling"), move |b| {
            b.iter(|| black_box(&p1).double())
        });
        group.bench_function(format!("{name} batch to affine n={N}"), move |b| {
            b.iter(|| {
                G::batch_normalize(black_box(&v), black_box(&mut q));
            })
        });
        group.finish();
    }
}

fn bench_g1_ops(c: &mut Criterion) {
    bench_curve_ops::<G1Projective>(c, "G1")
}

// fn bench_g2_ops(c: &mut Criterion) {
//     bench_curve_ops::<G2Projective>(c, "G2")
// }

criterion_group!(
    benches,
    bench_g1_ops,
    // bench_g2_ops
);
criterion_main!(benches);

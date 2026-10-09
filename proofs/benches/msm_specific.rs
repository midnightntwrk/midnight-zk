//! `msm_specific`, the KZG multi-scalar multiplication, on BLS12-381 G1 (blst) and G2
//! (generic Pippenger), over a ladder of sizes.
//!
//!     cargo bench -p midnight-proofs --bench msm_specific

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use ff::Field;
use group::{Curve, Group};
use midnight_curves::{CurveAffine, G1Affine, G2Affine, msm::msm_best};
use midnight_proofs::poly::kzg::msm::msm_specific;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

fn terms<C: CurveAffine>(n: usize) -> (Vec<C::Scalar>, Vec<C>) {
    let mut rng = ChaCha20Rng::seed_from_u64(42);
    let coeffs = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
    let bases = (0..n).map(|_| C::Curve::random(&mut rng).to_affine()).collect();
    (coeffs, bases)
}

fn ladder<C: CurveAffine>(c: &mut Criterion, name: &str, ks: &[u32]) {
    let mut group = c.benchmark_group(name);
    for &k in ks {
        let (coeffs, bases) = terms::<C>(1 << k);
        group.bench_with_input(BenchmarkId::from_parameter(k), &k, |b, _| {
            b.iter(|| msm_specific(&coeffs, &bases))
        });
    }
    group.finish();
}

/// BLS12-381 G1 by both backends: blst's `multi_exp_affine` and the Rust Pippenger `msm_best`
fn g1_backends(c: &mut Criterion, ks: &[u32]) {
    let mut group = c.benchmark_group("g1_backend");
    for &k in ks {
        let (coeffs, bases) = terms::<G1Affine>(1 << k);
        group.bench_with_input(BenchmarkId::new("blst", k), &k, |b, _| {
            b.iter(|| G1Affine::multi_exp_affine(&bases, &coeffs))
        });
        group.bench_with_input(BenchmarkId::new("pippenger", k), &k, |b, _| {
            b.iter(|| msm_best(&coeffs, &bases))
        });
    }
    group.finish();
}

fn bench(c: &mut Criterion) {
    ladder::<G1Affine>(c, "msm_specific_g1", &[4, 8, 12, 16]);
    ladder::<G2Affine>(c, "msm_specific_g2", &[4, 8, 12]);
    g1_backends(c, &[2, 4, 6, 8, 10, 12, 14, 16, 18]);
}

criterion_group!(benches, bench);
criterion_main!(benches);

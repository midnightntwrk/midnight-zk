//! Mirrors the prover's quotient-commitment scenarios to separate the two
//! candidate causes of the `single-h-commitment` regression:
//!
//! * "chunked"      : `m` MSMs of size `n`, all reusing the SAME `n` bases
//!   (default mode), run in parallel like the prover does.
//! * "single_blst"  : ONE MSM of size `m*n` over `m*n` distinct bases via blst
//!   `multi_exp_affine` (only valid when m*n <= 2^19).
//! * "single_best"  : ONE MSM of size `m*n` over `m*n` distinct bases via
//!   `msm_best` (the path `msm_specific` takes above 2^19).
//!
//! Run with:  cargo bench --bench h_commit -p midnight-curves

#[macro_use]
extern crate criterion;

use criterion::{BenchmarkId, Criterion};
use ff::Field;
use group::Group;
use midnight_curves::{msm::msm_best, Fq, G1Affine, G1Projective};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;

const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

// (k, m): n = 1<<k, total MSM size = n*m.
const CONFIGS: &[(u32, usize)] = &[(15, 4), (15, 8), (16, 4), (16, 8), (17, 4), (17, 8)];

fn gen_bases(n: usize) -> Vec<G1Affine> {
    (0..n)
        .into_par_iter()
        .map_init(
            || XorShiftRng::from_seed(SEED),
            |rng, _| G1Projective::random(&mut *rng).into(),
        )
        .collect()
}

fn gen_coeffs(n: usize) -> Vec<Fq> {
    (0..n)
        .into_par_iter()
        .map_init(
            || XorShiftRng::from_seed(SEED),
            |rng, _| Fq::random(&mut *rng),
        )
        .collect()
}

fn bench(c: &mut Criterion) {
    let max_total = CONFIGS.iter().map(|(k, m)| (1usize << k) * m).max().unwrap();
    println!("Generating {max_total} bases / coeffs (max total)...");
    let bases = gen_bases(max_total);
    let coeffs = gen_coeffs(max_total);

    let mut group = c.benchmark_group("h_commit");
    group.sample_size(10);

    for &(k, m) in CONFIGS {
        let n = 1usize << k;
        let total = n * m;
        let id = format!("k{k}_m{m}_total2p{}", (total as f64).log2().round() as u32);

        // Chunked: m parallel MSMs, each over the SAME bases[..n] slice.
        group.bench_function(BenchmarkId::new("chunked_parallel", &id), |b| {
            b.iter(|| {
                (0..m)
                    .into_par_iter()
                    .map(|i| G1Affine::multi_exp_affine(&bases[..n], &coeffs[i * n..i * n + n]))
                    .reduce(G1Projective::identity, |a, b| a + b)
            })
        });

        // Single via blst (what the prover does when total <= 2^19).
        if total <= (2 << 18) {
            group.bench_function(BenchmarkId::new("single_blst", &id), |b| {
                b.iter(|| G1Affine::multi_exp_affine(&bases[..total], &coeffs[..total]))
            });
        }

        // Single via msm_best (what msm_specific falls back to above 2^19).
        group.bench_function(BenchmarkId::new("single_msm_best", &id), |b| {
            b.iter(|| msm_best(&coeffs[..total], &bases[..total]))
        });
    }

    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);

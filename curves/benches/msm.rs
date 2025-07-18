//! This benchmarks Multi Scalar Multiplication (MSM).
//! Measurement on Bls12-381 G1.
//!
//! To run this benchmark:
//!
//!     cargo bench --bench msm
//!
//! To run the benchmark on halo2curve MSM version as well:
//!
//!     cargo bench --bench msm --features=h2c_compare

#[macro_use]
extern crate criterion;

use std::time::SystemTime;

use criterion::{BenchmarkId, Criterion};
use ff::PrimeField;
use group::Group;
use halo2curves::CurveAffine;
use rand_core::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use rayon::{
    current_thread_index,
    prelude::{IntoParallelIterator, ParallelIterator},
};

const SAMPLE_SIZE: usize = 10;
const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

const MULTICORE_RANGE: &[u8] = &[8, 10, 12, 14, 16, 18, 20];
const BITS: &[usize] = &[256];

fn generate_curvepoints<C: CurveAffine>(k: u8) -> Vec<C> {
    let n: u64 = 1 << k;
    println!("Generating 2^{k} = {n} curve points..",);

    let timer = SystemTime::now();
    let bases = (0..n)
        .into_par_iter()
        .map_init(
            || {
                let mut thread_seed = SEED;
                let uniq = current_thread_index().unwrap().to_ne_bytes();
                assert!(std::mem::size_of::<usize>() == 8);
                for i in 0..uniq.len() {
                    thread_seed[i] += uniq[i];
                    thread_seed[i + 8] += uniq[i];
                }
                XorShiftRng::from_seed(thread_seed)
            },
            |rng, _| <C::CurveExt as Group>::random(rng).into(),
        )
        .collect();
    let end = timer.elapsed().unwrap();
    println!(
        "Generating 2^{k} = {n} curve points took: {} sec.\n\n",
        end.as_secs()
    );
    bases
}

fn generate_coefficients<F: PrimeField>(k: u8, bits: usize) -> Vec<F> {
    let n: u64 = 1 << k;
    let max_val: Option<u128> = match bits {
        1 => Some(1),
        8 => Some(0xff),
        16 => Some(0xffff),
        32 => Some(0xffff_ffff),
        64 => Some(0xffff_ffff_ffff_ffff),
        128 => Some(0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff),
        256 => None,
        _ => panic!("unexpected bit size {}", bits),
    };

    (0..n)
        .into_par_iter()
        .map_init(
            || {
                let mut thread_seed = SEED;
                let uniq = current_thread_index().unwrap().to_ne_bytes();
                assert!(std::mem::size_of::<usize>() == 8);
                for i in 0..uniq.len() {
                    thread_seed[i] += uniq[i];
                    thread_seed[i + 8] += uniq[i];
                }
                XorShiftRng::from_seed(thread_seed)
            },
            |rng, _| {
                if let Some(max_val) = max_val {
                    let v_lo = rng.next_u64() as u128;
                    let v_hi = rng.next_u64() as u128;
                    let mut v = v_lo + (v_hi << 64);
                    v &= max_val; // Mask the 128bit value to get a lower number of bits
                    F::from_u128(v)
                } else {
                    F::random(rng)
                }
            },
        )
        .collect()
}

// Generates bases and coefficients for the given ranges and
// bit lenghts.
fn setup<C: CurveAffine>() -> (Vec<C>, Vec<Vec<C::ScalarExt>>) {
    let max_k = *MULTICORE_RANGE.iter().max().unwrap_or(&16);
    assert!(max_k < 64);

    let bases = generate_curvepoints::<C>(max_k);
    let coeffs: Vec<_> = BITS
        .iter()
        .map(|b| generate_coefficients(max_k, *b))
        .collect();

    (bases, coeffs)
}

fn msm_blst(c: &mut Criterion) {
    let mut group = c.benchmark_group("Msm");
    group.significance_level(0.1).sample_size(SAMPLE_SIZE);

    let (bases, coeffs) = setup::<midnight_curves::G1Affine>();

    // Blstrs version.
    for (b_index, b) in BITS.iter().enumerate() {
        for k in MULTICORE_RANGE {
            let n: usize = 1 << k;
            let id = format!("blstrs_{b}b_{k}");
            let points: Vec<midnight_curves::G1Projective> = bases.iter().map(Into::into).collect();
            group.bench_function(BenchmarkId::new("Blst", id), |b| {
                b.iter(|| {
                    midnight_curves::G1Projective::multi_exp(&points[..n], &coeffs[b_index][..n])
                })
            });
        }
    }

    #[cfg(feature = "h2c_compare")]
    // Halo2Curves version.
    for (b_index, b) in BITS.iter().enumerate() {
        for k in MULTICORE_RANGE {
            let n: usize = 1 << k;
            let id = format!("h2c_{b}b_{k}");
            group.bench_function(BenchmarkId::new("halo2curves", id), |b| {
                b.iter(|| {
                    halo2curves::msm::msm_best(&coeffs[b_index][..n], &bases[..n]);
                })
            });
        }
    }

    group.finish();
}

criterion_group!(benches, msm_blst);
criterion_main!(benches);

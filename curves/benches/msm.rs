//! This benchmarks Multi Scalar Multiplication (MSM).
//! Measurement on Bls12-381 G1.
//!
//! To run this benchmark:
//!
//!     cargo bench --bench msm

#[macro_use]
extern crate criterion;

use std::time::SystemTime;

use criterion::{BenchmarkId, Criterion};
use ff::PrimeField;
use group::Group;
use midnight_curves::CurveAffine;
use rand_core::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

const SAMPLE_SIZE: usize = 10;
const SEED: u64 = 0x5962_be5d_763d_318d;

const MULTICORE_RANGE: &[u8] = &[8, 10, 12, 14, 16, 18, 20];
const BITS: &[usize] = &[256];

/// A generator of its own for item `i` of `stream`. One per rayon job
/// (`map_init`) would replay the same values on every job of a thread.
fn item_rng(stream: u64, i: u64) -> XorShiftRng {
    XorShiftRng::seed_from_u64(SEED ^ (stream << 56) ^ i)
}

fn generate_curvepoints<C: CurveAffine>(k: u8) -> Vec<C> {
    let n: u64 = 1 << k;
    println!("Generating 2^{k} = {n} curve points..",);

    let timer = SystemTime::now();
    let bases = (0..n)
        .into_par_iter()
        .map(|i| <C::CurveExt as Group>::random(item_rng(0, i)).into())
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
        .map(|i| {
            let mut rng = item_rng(1, i);
            if let Some(max_val) = max_val {
                let v_lo = rng.next_u64() as u128;
                let v_hi = rng.next_u64() as u128;
                let mut v = v_lo + (v_hi << 64);
                v &= max_val; // Mask the 128bit value to get a lower number of bits
                F::from_u128(v)
            } else {
                F::random(rng)
            }
        })
        .collect()
}

// Generates bases and coefficients for the given ranges and
// bit lenghts.
fn setup<C: CurveAffine>() -> (Vec<C>, Vec<Vec<C::ScalarExt>>) {
    let max_k = *MULTICORE_RANGE.iter().max().unwrap_or(&16);
    assert!(max_k < 64);

    let bases = generate_curvepoints::<C>(max_k);
    let coeffs: Vec<_> = BITS.iter().map(|b| generate_coefficients(max_k, *b)).collect();

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

    // midnight-curves msm_best version.
    for (b_index, b) in BITS.iter().enumerate() {
        for k in MULTICORE_RANGE {
            let n: usize = 1 << k;
            let id = format!("msm_best_{b}b_{k}");
            group.bench_function(BenchmarkId::new("msm_best", id), |b| {
                b.iter(|| {
                    midnight_curves::msm::msm_best(&coeffs[b_index][..n], &bases[..n]);
                })
            });
        }
    }

    // midnight-curves msm_pippenger version (the commitments' MSM).
    for (b_index, b) in BITS.iter().enumerate() {
        for k in MULTICORE_RANGE {
            let n: usize = 1 << k;
            let id = format!("msm_pippenger_{b}b_{k}");
            group.bench_function(BenchmarkId::new("msm_pippenger", id), |b| {
                b.iter(|| {
                    midnight_curves::msm::msm_pippenger(&coeffs[b_index][..n], &bases[..n]);
                })
            });
        }
    }

    group.finish();
}

criterion_group!(benches, msm_blst);
criterion_main!(benches);

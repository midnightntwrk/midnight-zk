//! Differential tests of [`super::msm_pippenger`]: against blst's MSM
//! (`G1Affine::multi_exp_affine`), a naive sum, and sums with known discrete
//! logarithms, across sizes, windows, thread counts and adversarial scalars and
//! bases.
//!
//! `MSM_FUZZ_ITERS` and `MSM_FUZZ_SEED` lengthen or reseed [`fuzz`].

use std::ops::Neg;

use ff::{Field, PrimeField};
use group::{Curve, Group, prime::PrimeCurveAffine};
use rand_core::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::{Xyzz, chunk_count, get_booth_index, msm_pippenger, msm_with_window, window_size};
use crate::{CurveAffine, Fq, G1Affine, G1Projective, bn256};

fn rng(seed: u64) -> XorShiftRng {
    XorShiftRng::seed_from_u64(seed)
}

/// `n` random points of the prime-order subgroup, reproducibly from `seed`.
fn random_points<C: CurveAffine>(n: usize, seed: u64) -> Vec<C> {
    let points: Vec<C::Curve> = (0..n)
        .into_par_iter()
        .map(|i| C::Curve::random(rng(seed ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15))))
        .collect();
    let mut affine = vec![C::identity(); n];
    C::Curve::batch_normalize(&points, &mut affine);
    affine
}

fn random_scalars<F: Field>(n: usize, seed: u64) -> Vec<F> {
    let mut rng = rng(seed);
    (0..n).map(|_| F::random(&mut rng)).collect()
}

/// `Σ scalars[i]·points[i]`, one scalar multiplication at a time.
fn naive<C: CurveAffine>(scalars: &[C::Scalar], points: &[C]) -> C::Curve {
    scalars
        .iter()
        .zip(points)
        .fold(C::Curve::identity(), |acc, (s, p)| acc + *p * s)
}

/// blst's MSM, which panics on no terms.
fn blst(scalars: &[Fq], points: &[G1Affine]) -> G1Projective {
    if scalars.is_empty() {
        return G1Projective::identity();
    }
    G1Affine::multi_exp_affine(points, scalars)
}

/// `msm_with_window` in a pool of `threads` threads.
fn in_pool<C: CurveAffine>(threads: usize, f: impl FnOnce() -> C::Curve + Send) -> C::Curve {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
    pool.install(f)
}

/// Scalars of a given shape: the classes the fuzzer and the targeted tests
/// draw from.
#[derive(Clone, Copy, Debug)]
enum ScalarClass {
    Random,
    Zero,
    One,
    MinusOne,
    /// `2^j`, for random `j`.
    PowerOfTwo,
    /// `-2^j`: every top bit set.
    MinusPowerOfTwo,
    /// Below `2^64`, like most advice values.
    Small,
    /// `-s` for a small `s`: near the modulus.
    MinusSmall,
    /// The same scalar for every term of the class.
    Repeated,
}

const SCALAR_CLASSES: [ScalarClass; 9] = [
    ScalarClass::Random,
    ScalarClass::Zero,
    ScalarClass::One,
    ScalarClass::MinusOne,
    ScalarClass::PowerOfTwo,
    ScalarClass::MinusPowerOfTwo,
    ScalarClass::Small,
    ScalarClass::MinusSmall,
    ScalarClass::Repeated,
];

fn scalar_of<F: PrimeField>(class: ScalarClass, rng: &mut XorShiftRng, repeated: F) -> F {
    let pow2 =
        |rng: &mut XorShiftRng| F::from(2).pow_vartime([rng.next_u64() % F::NUM_BITS as u64]);
    match class {
        ScalarClass::Random => F::random(rng),
        ScalarClass::Zero => F::ZERO,
        ScalarClass::One => F::ONE,
        ScalarClass::MinusOne => -F::ONE,
        ScalarClass::PowerOfTwo => pow2(rng),
        ScalarClass::MinusPowerOfTwo => -pow2(rng),
        ScalarClass::Small => F::from(rng.next_u64()),
        ScalarClass::MinusSmall => -F::from(rng.next_u64()),
        ScalarClass::Repeated => repeated,
    }
}

/// Bases of a given shape.
#[derive(Clone, Copy, Debug)]
enum BaseClass {
    Random,
    Identity,
    /// One fixed point `P`: buckets meet it again and again (doublings).
    Repeated,
    /// `-P`: cancels `P` in a bucket.
    Negated,
}

const BASE_CLASSES: [BaseClass; 4] = [
    BaseClass::Random,
    BaseClass::Identity,
    BaseClass::Repeated,
    BaseClass::Negated,
];

fn base_of<C: CurveAffine>(class: BaseClass, random: C, p: C) -> C {
    match class {
        BaseClass::Random => random,
        BaseClass::Identity => C::identity(),
        BaseClass::Repeated => p,
        BaseClass::Negated => p.neg(),
    }
}

#[test]
fn test_booth_encoding() {
    fn mul(scalar: &Fq, point: &G1Affine, window: usize) -> G1Affine {
        let u = scalar.to_repr();
        let n = Fq::NUM_BITS as usize / window + 1;
        let table: Vec<_> = (0..=1 << (window - 1)).map(|i| point * Fq::from(i as u64)).collect();
        let mut acc = G1Projective::identity();
        for i in (0..n).rev() {
            for _ in 0..window {
                acc = acc.double();
            }
            let idx = get_booth_index(i, window, u.as_ref());
            if idx.is_negative() {
                acc += table[idx.unsigned_abs() as usize].neg();
            }
            if idx.is_positive() {
                acc += table[idx.unsigned_abs() as usize];
            }
        }
        acc.to_affine()
    }

    let mut rng = rng(1);
    let point = random_points::<G1Affine>(1, 2)[0];
    let mut scalars: Vec<Fq> = (0..10).map(|_| Fq::random(&mut rng)).collect();
    scalars.extend([
        Fq::ZERO,
        Fq::ONE,
        -Fq::ONE,
        -Fq::from(2),
        Fq::from(2).pow_vartime([254]),
    ]);
    for window in 1..=16 {
        for scalar in &scalars {
            assert_eq!(
                mul(scalar, &point, window),
                (point * scalar).to_affine(),
                "c {window}"
            );
        }
    }
}

/// The XYZZ formulas against projective arithmetic, including the doubling,
/// cancelling and identity cases.
#[test]
fn test_xyzz() {
    let pts = random_points::<G1Affine>(3, 3);
    let (p, q, r) = (pts[0], pts[1], pts[2]);
    let to = |a: &Xyzz<_>| a.to_curve::<G1Affine>();

    let mut a = Xyzz::identity();
    assert_eq!(to(&a), G1Projective::identity());
    a.add_affine(&p.x(), &p.y(), false);
    assert_eq!(to(&a), p.to_curve());
    a.add_affine(&q.x(), &q.y(), true);
    assert_eq!(to(&a), p - q);
    a.add_affine(&q.x(), &q.y(), false);
    assert_eq!(to(&a), p.to_curve());
    // Doubling through `add_affine`.
    a.add_affine(&p.x(), &p.y(), false);
    assert_eq!(to(&a), p + p);
    a.double();
    assert_eq!(to(&a), (p + p).double());

    // Cancelling through `add_affine`.
    let mut b = Xyzz::from_affine(&r.x(), &r.y());
    b.add_affine(&r.x(), &r.y(), true);
    assert!(b.is_identity());
    b.double();
    assert!(b.is_identity());

    // `add`, with ZZ, ZZZ != 1 on both sides.
    let mut c = Xyzz::identity();
    c.add_affine(&p.x(), &p.y(), false);
    c.add_affine(&q.x(), &q.y(), false);
    let mut d = Xyzz::identity();
    d.add_affine(&r.x(), &r.y(), false);
    d.add_affine(&q.x(), &q.y(), true);
    let mut e = c;
    e.add(&d);
    assert_eq!(to(&e), p + q + r - q);
    // `add` of equal points doubles, of opposite points cancels.
    let mut f = c;
    f.add(&c);
    assert_eq!(to(&f), (p + q).double());
    let mut neg_c = Xyzz::identity();
    neg_c.add_affine(&p.x(), &p.y(), true);
    neg_c.add_affine(&q.x(), &q.y(), true);
    let mut g = c;
    g.add(&neg_c);
    assert!(g.is_identity());
    // The identity on either side.
    let mut h = Xyzz::identity();
    h.add(&c);
    assert_eq!(to(&h), p + q);
    h.add(&Xyzz::identity());
    assert_eq!(to(&h), p + q);
}

/// Chunks are at least one and at most the threads, and more than one only
/// with at least 64 terms each.
#[test]
fn test_chunk_count() {
    for threads in 1..=64 {
        for n in [0, 1, 63, 64, 127, 128, 1000, 1 << 12, 1 << 16, 1 << 20] {
            for c in 1..=16 {
                let chunks = chunk_count(n, 255, c, threads);
                assert!(
                    (1..=threads).contains(&chunks),
                    "n {n} c {c} threads {threads}"
                );
                assert!(chunks == 1 || n.div_ceil(chunks) >= 64);
            }
        }
    }
    // More threads than windows: the terms are chunked.
    assert!(chunk_count(1 << 16, 255, 12, 64) > 1);
}

/// Every size up to 300 terms, at the table's window: the small sizes, the
/// XYZZ-bucket windows and the first scalar block boundary.
#[test]
fn test_every_size_up_to_300() {
    let points = random_points::<G1Affine>(300, 4);
    let scalars = random_scalars::<Fq>(300, 5);
    for n in 0..=300 {
        let (s, p) = (&scalars[..n], &points[..n]);
        let expected = naive(s, p);
        assert_eq!(msm_pippenger(s, p), expected, "n {n}");
        assert_eq!(blst(s, p), expected, "blst, n {n}");
    }
}

/// Every window size from 1 to 16, not just the table's choice.
#[test]
fn test_every_window() {
    let points = random_points::<G1Affine>(4097, 6);
    let scalars = random_scalars::<Fq>(4097, 7);
    for n in [
        0, 1, 2, 3, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257, 300, 1000, 4097,
    ] {
        let (s, p) = (&scalars[..n], &points[..n]);
        let expected = blst(s, p);
        for c in 1..=16 {
            assert_eq!(msm_with_window(s, p, c), expected, "n {n} c {c}");
        }
    }
}

/// Sizes around the powers of two the prover commits to.
#[test]
fn test_powers_of_two() {
    let max = (1 << 16) + 1;
    let points = random_points::<G1Affine>(max, 8);
    let scalars = random_scalars::<Fq>(max, 9);
    for k in 8..=16 {
        for n in [(1 << k) - 1, 1 << k, (1 << k) + 1] {
            let (s, p) = (&scalars[..n], &points[..n]);
            assert_eq!(msm_pippenger(s, p), blst(s, p), "n {n}");
        }
    }
}

/// Pools of many sizes: the chunking and the tile scheduling depend on the
/// thread count, and scalar blocks end raggedly.
#[test]
fn test_thread_pools() {
    let max = 20_000;
    let points = random_points::<G1Affine>(max, 10);
    let scalars = random_scalars::<Fq>(max, 11);
    for n in [100, 1000, 3000, 256 * 7 + 1, max] {
        let (s, p) = (&scalars[..n], &points[..n]);
        let expected = blst(s, p);
        for threads in [1, 2, 3, 4, 7, 12, 64] {
            for c in [window_size(n), 4, 8, 13] {
                let got = in_pool::<G1Affine>(threads, || msm_with_window(s, p, c));
                assert_eq!(got, expected, "n {n} threads {threads} c {c}");
            }
        }
    }
}

/// Each scalar class on its own, and all of them mixed.
#[test]
fn test_scalar_classes() {
    let n = 2000;
    let points = random_points::<G1Affine>(n, 12);
    let mut rng = rng(13);
    let repeated = Fq::random(&mut rng);
    let mut cases: Vec<(String, Vec<Fq>)> = SCALAR_CLASSES
        .iter()
        .map(|&class| {
            let s = (0..n).map(|_| scalar_of(class, &mut rng, repeated)).collect();
            (format!("{class:?}"), s)
        })
        .collect();
    let mixed = (0..n)
        .map(|i| scalar_of(SCALAR_CLASSES[i % SCALAR_CLASSES.len()], &mut rng, repeated))
        .collect();
    cases.push(("mixed".into(), mixed));
    for (name, scalars) in &cases {
        let expected = blst(scalars, &points);
        for c in [window_size(n), 5, 7, 9, 12, 13] {
            assert_eq!(
                msm_with_window(scalars, &points, c),
                expected,
                "{name} c {c}"
            );
        }
    }
}

/// Identities, repeated and negated bases: batched affine additions that
/// would double or cancel a bucket must take the XYZZ route, and the waiting
/// queue and side buckets fill up.
#[test]
fn test_base_classes() {
    let p = random_points::<G1Affine>(1, 14)[0];
    let q = random_points::<G1Affine>(1, 15)[0];
    for n in [300, 2000, 5000] {
        let random = random_points::<G1Affine>(n, 16);
        let scalars = random_scalars::<Fq>(n, 17);
        // Few distinct scalars, so buckets meet the same point again and again.
        let few: Vec<Fq> = (0..n).map(|i| Fq::from([3, 5, 1 << 40][i % 3])).collect();
        let mut cases: Vec<(String, Vec<G1Affine>)> = BASE_CLASSES
            .iter()
            .map(|&class| {
                let b = (0..n).map(|i| base_of(class, random[i], p)).collect();
                (format!("{class:?}"), b)
            })
            .collect();
        cases.push((
            "p,-p,q,p".into(),
            (0..n).map(|i| [p, -p, q, p][i % 4]).collect(),
        ));
        cases.push((
            "mixed".into(),
            (0..n).map(|i| base_of(BASE_CLASSES[i % 4], random[i], p)).collect(),
        ));
        for (name, bases) in &cases {
            for scalars in [&scalars, &few] {
                let expected = naive(scalars, bases);
                for c in [window_size(n), 4, 7, 8, 10, 13] {
                    assert_eq!(
                        msm_with_window(scalars, bases, c),
                        expected,
                        "{name} n {n} c {c}"
                    );
                }
            }
        }
    }
}

/// Bases with known discrete logarithms, `a_i·G`: the sum is `(Σ a_i s_i)·G`,
/// computed with no MSM at all.
#[test]
fn test_known_logs() {
    let n = 5000;
    let g = G1Projective::generator();
    let mut rng = rng(18);
    let logs: Vec<Fq> = (0..n)
        .map(|i| match i % 3 {
            0 => Fq::from(rng.next_u64() % 16),
            1 => Fq::random(&mut rng),
            _ => -Fq::from(rng.next_u64() % 16),
        })
        .collect();
    let projective: Vec<G1Projective> = logs.iter().map(|a| g * a).collect();
    let mut bases = vec![G1Affine::identity(); n];
    G1Projective::batch_normalize(&projective, &mut bases);
    let repeated = Fq::random(&mut rng);
    let scalars: Vec<Fq> = (0..n)
        .map(|i| scalar_of(SCALAR_CLASSES[i % SCALAR_CLASSES.len()], &mut rng, repeated))
        .collect();
    let expected = g * logs.iter().zip(&scalars).map(|(a, s)| *a * s).sum::<Fq>();
    for c in [window_size(n), 3, 5, 7, 9, 11, 13, 16] {
        assert_eq!(msm_with_window(&scalars, &bases, c), expected, "c {c}");
    }
}

/// BN256, which has no `xy_ref`: its coordinates are copied out first.
#[test]
fn test_bn256() {
    let n = 3000;
    let mut points = random_points::<bn256::G1Affine>(n, 19);
    for i in (0..n).step_by(7) {
        points[i] = bn256::G1Affine::identity();
    }
    let scalars = random_scalars::<bn256::Fr>(n, 20);
    for m in [0, 1, 31, 32, 100, 1000, n] {
        let (s, p) = (&scalars[..m], &points[..m]);
        let expected = naive(s, p);
        assert_eq!(
            crate::msm::msm_parallel(s, p),
            expected,
            "msm_parallel, n {m}"
        );
        for c in [window_size(m), 4, 7, 9, 13] {
            assert_eq!(msm_with_window(s, p, c), expected, "n {m} c {c}");
        }
    }
}

/// Random mixtures of every scalar and base class, at random sizes, windows
/// and thread counts.
#[test]
fn test_fuzz() {
    let iters = std::env::var("MSM_FUZZ_ITERS").map_or(64, |v| v.parse().unwrap());
    let seed = std::env::var("MSM_FUZZ_SEED").map_or(21, |v| v.parse().unwrap());
    let mut rng = rng(seed);
    let pool_points = random_points::<G1Affine>(5000, seed ^ 1);
    let p = random_points::<G1Affine>(1, seed ^ 2)[0];
    for iter in 0..iters {
        // Log-uniform sizes up to 5000.
        let n = (1usize << (rng.next_u32() % 13)).min(5000);
        let n = n + (rng.next_u32() as usize % n.max(1)).min(5000 - n);
        let (s_mask, b_mask) = (rng.next_u32() % 511 + 1, rng.next_u32() % 15 + 1);
        let scalar_classes: Vec<_> = SCALAR_CLASSES
            .iter()
            .enumerate()
            .filter(|(i, _)| s_mask >> i & 1 == 1)
            .collect();
        let base_classes: Vec<_> =
            BASE_CLASSES.iter().enumerate().filter(|(i, _)| b_mask >> i & 1 == 1).collect();
        let repeated = Fq::random(&mut rng);
        let mut scalars = Vec::with_capacity(n);
        let mut bases = Vec::with_capacity(n);
        for random in &pool_points[..n] {
            let sc = *scalar_classes[rng.next_u32() as usize % scalar_classes.len()].1;
            let bc = *base_classes[rng.next_u32() as usize % base_classes.len()].1;
            scalars.push(scalar_of(sc, &mut rng, repeated));
            bases.push(base_of(bc, *random, p));
        }
        let c = match rng.next_u32() % 3 {
            0 => window_size(n),
            _ => 1 + rng.next_u32() as usize % 16,
        };
        let threads = [1, 2, 3, 4, 7, 12, 64][rng.next_u32() as usize % 7];
        let expected = naive(&scalars, &bases);
        let got = in_pool::<G1Affine>(threads, || msm_with_window(&scalars, &bases, c));
        assert_eq!(
            got, expected,
            "seed {seed} iter {iter}: n {n} c {c} threads {threads} scalars {s_mask:#b} bases {b_mask:#b}"
        );
    }
}

/// A same-x collision while summing the buckets in lanes (a lane's running
/// sum meets the next bucket, its negation or its double, or the lanes' sum
/// meets a lane): the lane path must give up and the XYZZ summation take over.
/// With `c = 10` the scalars 8 and 7 fill buckets 7 and 6 of the first lane,
/// once each, so no side bucket is in use and the lane path runs.
#[test]
fn test_lane_collision() {
    let p = random_points::<G1Affine>(1, 30)[0];
    let two_p = (p + p).to_affine();
    let scalars = [Fq::from(8), Fq::from(7)];
    for bases in [[p, -p], [p, -two_p], [-p, p], [p, p], [p, two_p]] {
        let expected = naive(&scalars, &bases);
        assert_eq!(msm_with_window(&scalars, &bases, 10), expected, "{bases:?}");
    }
}

/// Sparse inputs (more zero scalars than non-zero) are compacted first: every
/// density around that threshold, with an identity base among the terms.
#[test]
fn test_sparse() {
    let check = |n: usize, seed: u64, oracle: &dyn Fn(&[Fq], &[G1Affine]) -> G1Projective| {
        let mut points = random_points::<G1Affine>(n, seed);
        points[5] = G1Affine::identity();
        let dense = random_scalars::<Fq>(n, seed + 1);
        let mut rng = rng(seed + 2);
        for nonzero in [0, 1, 2, 50, n / 2 - 1, n / 2, n / 2 + 1, n - 1, n] {
            // Non-zeros at random positions, then all at the end: chunks of
            // differing counts, and empty ones.
            for at_end in [false, true] {
                let mut scalars = vec![Fq::ZERO; n];
                let mut placed = 0;
                while placed < nonzero {
                    let i = if at_end {
                        n - 1 - placed
                    } else {
                        rng.next_u32() as usize % n
                    };
                    if scalars[i].is_zero_vartime() {
                        scalars[i] = dense[i];
                        placed += 1;
                    }
                }
                let expected = oracle(&scalars, &points);
                assert_eq!(
                    msm_pippenger(&scalars, &points),
                    expected,
                    "n {n}, nonzero {nonzero}, at_end {at_end}"
                );
            }
        }
    };
    check(1 << 12, 31, &naive::<G1Affine>);
    // Over the parallel compaction's threshold, with a partial last chunk.
    check((1 << 14) + 37, 34, &blst);
}

/// The largest sizes: run with `--ignored`.
#[test]
#[ignore]
fn test_large() {
    let max = 1 << 18;
    let points = random_points::<G1Affine>(max, 22);
    let scalars = random_scalars::<Fq>(max, 23);
    for k in 17..=18 {
        let (s, p) = (&scalars[..1 << k], &points[..1 << k]);
        assert_eq!(msm_pippenger(s, p), blst(s, p), "k {k}");
    }
}

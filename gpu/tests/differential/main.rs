// SPDX-License-Identifier: Apache-2.0

//! Differential checks through the midnight-proofs dispatch and stock fallback
//! paths.

mod corpus;
mod hooks;
mod max_k;

use std::sync::atomic::Ordering::Relaxed;

use ff::{Field, PrimeField};
use group::{Curve, Group, GroupEncoding, prime::PrimeCurveAffine};
use hooks::Expected::{self, Bypassed, Decline, Device};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::{
    gpu::{
        adapter, quotient_check_diffs, quotient_checks,
        test_switches::{QUOTIENT_CHECK, RandomCircuit, without_hooks},
    },
    poly::{EvaluationDomain, FftDomain, kzg::msm::msm_specific},
};
use proptest::{
    prelude::*,
    test_runner::{FileFailurePersistence, RngAlgorithm, RngSeed},
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

fn config() -> ProptestConfig {
    let mut config = ProptestConfig::default();
    if std::env::var_os("PROPTEST_CASES").is_none() {
        config.cases = 8;
    }
    config.rng_algorithm = RngAlgorithm::ChaCha;
    config.rng_seed = RngSeed::Fixed(0x5873_0d1a);
    config.failure_persistence = Some(Box::new(FileFailurePersistence::Direct(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/proptest-regressions/differential.txt"
    ))));
    config
}

fn values(n: usize, seed: u64) -> Vec<Fq> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    (0..n).map(|_| Fq::random(&mut rng)).collect()
}

// Compare every canonical field byte and identify the first wrong coefficient.
fn same_values(actual: &[Fq], stock: &[Fq], operation: &str) {
    assert_eq!(actual.len(), stock.len(), "{operation} length");
    for (i, (a, b)) in actual.iter().zip(stock).enumerate() {
        assert_eq!(a.to_repr(), b.to_repr(), "{operation} coefficient {i}");
    }
}

fn msm_case(s: &[Fq], p: &[G1Affine], expected: Expected) {
    let compute = || msm_specific(s, p).to_affine().to_bytes();
    let stock = without_hooks(compute);
    let actual = hooks::MSM.check(expected, compute);
    assert_eq!(actual.as_ref(), stock.as_ref(), "compressed G1 MSM");
}

fn bases(n: usize, seed: u64) -> Vec<G1Affine> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    (0..n).map(|_| G1Projective::random(&mut rng).to_affine()).collect()
}

fn transforms(k: u32, extra: u32, seed: u64, short: bool) {
    let domain = EvaluationDomain::new((1 << extra) + 1, k);
    let coeff = domain.coeff_from_vec(values(1 << k, seed));
    let eval = domain.lagrange_from_vec(values(1 << k, !seed));
    let fft_domain = FftDomain::new(&domain);

    let forward = || fft_domain.coeff_to_lagrange(coeff.clone());
    let inverse = || fft_domain.lagrange_to_coeff(eval.clone());

    // At k=1 the proofs adapter lacks twiddles[1] and bypasses the backend.
    let expected = if k == 1 {
        Bypassed
    } else if short {
        Decline("shape")
    } else {
        Device
    };
    let stock = without_hooks(forward);
    same_values(&hooks::FFT.check(expected, forward), &stock, "NTT");
    let stock = without_hooks(inverse);
    same_values(&hooks::IFFT.check(expected, inverse), &stock, "iNTT");
}

enum QuotientPath {
    CheckCoefficients,
    UseDeviceResult,
    BelowThreshold,
    NonprimitiveShift,
}

fn quotient_case(k: u32, seed: u64, satisfied: bool, path: QuotientPath) {
    let circuit = without_hooks(|| RandomCircuit::new(seed, satisfied, k));
    let (stock, verified) = without_hooks(|| circuit.prove());
    if satisfied {
        assert!(verified, "stock proof verification");
    }
    let shape = circuit.shape().expect("quotient job");
    assert!(shape.ext_k > k && shape.proof_polys > 0);
    assert!(shape.len < 1 << shape.ext_k);
    // Admit the extended-domain quotient while keeping base transforms on the CPU.
    let expected = if matches!(path, QuotientPath::BelowThreshold) {
        assert!(shape.ext_k < gpu::min_k());
        Decline("below-min-k")
    } else {
        gpu::set_min_k(shape.ext_k);
        if matches!(path, QuotientPath::NonprimitiveShift) {
            Decline("shape")
        } else {
            Device
        }
    };
    // The quotient checks its header (ABI, sizes, coset shift, minimum size)
    // before device availability, so a stub build declines a header it refuses
    // with the same reason as the device build; only a job that passes the
    // header declines as `no-device` there.
    let expected = if gpu::cuda_built() || !matches!(expected, Device) {
        expected
    } else {
        Decline("no-device")
    };
    hooks::NONPRIMITIVE_SHIFT.store(matches!(path, QuotientPath::NonprimitiveShift), Relaxed);
    let checks = quotient_checks();
    let before = quotient_check_diffs();
    QUOTIENT_CHECK.store(matches!(path, QuotientPath::CheckCoefficients), Relaxed);
    let (actual, ok) =
        hooks::QUOTIENT.check(expected, || hooks::check_base_declines(|| circuit.prove()));
    assert_eq!(
        quotient_checks() - checks,
        u64::from(gpu::cuda_built() && matches!(path, QuotientPath::CheckCoefficients)),
        "completed stock comparisons"
    );
    assert_eq!(
        quotient_check_diffs() - before,
        0,
        "quotient coefficient differences"
    );
    assert_eq!(ok, verified, "proof verification");
    assert_eq!(actual, stock, "seeded proof bytes");
}

proptest! {
    #![proptest_config(config())]
    #[test]
    fn random_msm(n in 2usize..192, seed in any::<u64>()) {
        hooks::run(0, false, || msm_case(&values(n, seed), &bases(n, !seed), Device));
    }

    #[test]
    fn random_transforms(k in 2u32..=11, extra in 0u32..=3, seed in any::<u64>()) {
        hooks::run(0, false, || transforms(k, extra, seed, false));
    }

    #[test]
    fn random_quotient(k in 6u32..=8, seed in any::<u64>(), satisfied in any::<bool>()) {
        hooks::run(6, false, || quotient_case(k, seed, satisfied, QuotientPath::CheckCoefficients));
    }
}

#[test]
fn prover_consumes_device_quotient_or_stock_fallback() {
    hooks::run(6, false, || {
        quotient_case(6, 3, true, QuotientPath::UseDeviceResult)
    });
}

#[test]
fn below_threshold_quotient_falls_back() {
    hooks::run(DEFAULT_MIN_K, false, || {
        quotient_case(6, 3, true, QuotientPath::BelowThreshold)
    });
}

#[test]
fn nonprimitive_quotient_shift_falls_back() {
    hooks::run(6, false, || {
        quotient_case(6, 3, true, QuotientPath::NonprimitiveShift)
    });
}

#[test]
fn k_one() {
    hooks::run(0, false, || {
        msm_case(&values(2, corpus::K_ONE), &bases(2, corpus::K_ONE), Device);
        midnight_proofs::gpu::reset_hook_declines();
        transforms(1, 1, corpus::K_ONE, false);
        assert_eq!(
            midnight_proofs::gpu::hook_declines(),
            [
                ("fft", "length-mismatch", 1),
                ("ifft", "length-mismatch", 1)
            ]
        );
        // The raw hooks accept two values even though the proofs adapter bypasses them.
        let d = EvaluationDomain::new(2, 1);
        let fd = FftDomain::new(&d);
        let a = values(2, corpus::K_ONE);
        let mut fwd = a.clone();
        let stock = without_hooks(|| fd.coeff_to_lagrange(d.coeff_from_vec(a.clone())));
        let accepted = hooks::FFT.check(Device, || {
            hooks::fft(
                adapter::scalars_mut(&mut fwd),
                adapter::scalar(d.get_omega()),
                1,
            )
        });
        assert_eq!(accepted, gpu::cuda_built());
        if !accepted {
            fwd = fd.coeff_to_lagrange(d.coeff_from_vec(fwd)).to_vec();
        }
        same_values(&fwd, &stock, "two-element NTT");
        let stock = without_hooks(|| fd.lagrange_to_coeff(d.lagrange_from_vec(a.clone())));
        let mut inv = a;
        let accepted = hooks::IFFT.check(Device, || {
            hooks::ifft(
                adapter::scalars_mut(&mut inv),
                adapter::scalar(d.get_omega_inv()),
                1,
                adapter::scalar(Fq::from(2).invert().unwrap()),
            )
        });
        assert_eq!(accepted, gpu::cuda_built());
        if !accepted {
            inv = fd.lagrange_to_coeff(d.lagrange_from_vec(inv)).to_vec();
        }
        same_values(&inv, &stock, "two-element iNTT");
    });
}

#[test]
fn k_zero() {
    hooks::run(0, false, || {
        let a = values(1, corpus::K_ZERO);
        msm_case(&a, &bases(1, corpus::K_ZERO), Device);
    });
}

#[test]
fn empty_input() {
    hooks::run(0, false, || {
        msm_case(&[], &[], Decline("shape"));
        let one = gpu::field::from_u64(1);
        assert!(!hooks::FFT.check(Decline("shape"), || hooks::fft(&mut [], one, 0)));
        assert!(!hooks::IFFT.check(Decline("shape"), || hooks::ifft(&mut [], one, 0, one)));
    });
}

#[test]
fn non_power_of_two_msm() {
    hooks::run(0, false, || {
        msm_case(&values(23, corpus::ODD), &bases(23, corpus::ODD), Device)
    });
}

#[test]
fn non_power_of_two_transforms_decline_and_fall_back() {
    // Shorten only the slices given to the device. The production caller retains a
    // valid domain and must transform its original input after each false return.
    hooks::run(0, true, || transforms(3, 1, corpus::SHORT, true));
}

// gpu/src/lib.rs::min_k defaults to 14; msm_g1 admits lengths >= 2^min_k.
const DEFAULT_MIN_K: u32 = 14;

fn threshold(offset: isize) {
    hooks::run(DEFAULT_MIN_K, false, || {
        let n = (1usize << DEFAULT_MIN_K).checked_add_signed(offset).unwrap();
        let step = G1Projective::random(ChaCha20Rng::seed_from_u64(corpus::THRESHOLD));
        let mut point = step;
        let points: Vec<_> = (0..n)
            .map(|_| {
                point += step;
                point
            })
            .collect();
        let mut affine = vec![G1Affine::identity(); n];
        G1Projective::batch_normalize(&points, &mut affine);
        msm_case(
            &values(n, corpus::THRESHOLD),
            &affine,
            if offset < 0 {
                Decline("below-min-k")
            } else {
                Device
            },
        );
    });
}

#[test]
fn msm_just_below_threshold() {
    threshold(-1);
}

#[test]
fn msm_at_threshold() {
    threshold(0);
}

#[test]
fn msm_just_above_threshold() {
    threshold(1);
}

#[test]
fn point_at_infinity() {
    hooks::run(0, false, || {
        let mut p = bases(7, corpus::INFINITY);
        p[3] = G1Affine::identity();
        msm_case(&values(7, corpus::INFINITY), &p, Device);
    });
}

#[test]
fn all_zero_scalars() {
    hooks::run(0, false, || {
        msm_case(&[Fq::ZERO; 7], &bases(7, corpus::ZEROS), Device)
    });
}

#[test]
fn scalars_equal_one() {
    hooks::run(0, false, || {
        msm_case(&[Fq::ONE; 7], &bases(7, corpus::ONES), Device)
    });
}

#[test]
fn scalars_equal_r_minus_one() {
    hooks::run(0, false, || {
        msm_case(&[-Fq::ONE; 7], &bases(7, corpus::MINUS_ONES), Device)
    });
}

#[test]
fn repeated_bases() {
    hooks::run(0, false, || {
        msm_case(
            &values(7, corpus::REPEATS),
            &[bases(1, corpus::REPEATS)[0]; 7],
            Device,
        )
    });
}

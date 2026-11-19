// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

//! Lean arithmetic vectors against the stock routines and the CUDA hook ABI.
//! A CUDA build requires a counted completion for each supported operation.

use std::{
    cell::RefCell,
    fs,
    path::{Path, PathBuf},
    sync::{
        Mutex, Once,
        atomic::{AtomicU64, Ordering::Relaxed},
    },
};

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::{
    gpu::{GpuHooks, adapter, install, test_switches::without_hooks},
    poly::{EvaluationDomain, FftDomain, kzg::msm::msm_specific},
};
use serde_json::Value;

#[path = "oracle/boundaries.rs"]
mod boundaries;
#[path = "oracle/quotient.rs"]
mod quotient;

const MODULUS: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";
static COUNTERS: Mutex<()> = Mutex::new(());
static FFT: AtomicU64 = AtomicU64::new(0);
static IFFT: AtomicU64 = AtomicU64::new(0);
static MSM: AtomicU64 = AtomicU64::new(0);

fn install_hooks() {
    static INSTALL: Once = Once::new();
    INSTALL.call_once(|| {
        assert!(install(GpuHooks {
            fft: Some(|a, w, k| {
                FFT.fetch_add(1, Relaxed);
                gpu::fft(a, w, k)
            }),
            ifft: Some(|a, w, k, d| {
                IFFT.fetch_add(1, Relaxed);
                gpu::ifft(a, w, k, d)
            }),
            msm_g1: Some(|s, p| {
                MSM.fetch_add(1, Relaxed);
                gpu::msm_g1(s, p)
            }),
            quotient: Some(gpu::quotient),
        }))
    });
}

// Count the prover forwarding a call separately from the backend completing it.
fn dispatched<T>(
    attempts: &AtomicU64,
    successes: fn() -> u64,
    offered: bool,
    value: bool,
    run: impl FnOnce() -> T,
) -> T {
    let before = attempts.load(Relaxed);
    let completed = successes();
    let result = run();
    assert_eq!(
        attempts.load(Relaxed) - before,
        u64::from(offered),
        "prover hook invocations"
    );
    assert_eq!(
        successes() - completed,
        u64::from(offered && value && require_device()),
        "device completions"
    );
    result
}

fn field(value: &Value) -> Fq {
    let s = value.as_str().expect("decimal field string");
    assert!(!s.is_empty() && s.bytes().all(|c| c.is_ascii_digit()));
    assert!(s == "0" || !s.starts_with('0'));
    assert!(s.len() < MODULUS.len() || (s.len() == MODULUS.len() && s < MODULUS));
    Fq::from_str_vartime(s).expect("canonical field element")
}

fn fields(value: &Value) -> Vec<Fq> {
    value.as_array().unwrap().iter().map(field).collect()
}

fn uint(value: &Value) -> u32 {
    value.as_u64().unwrap().try_into().unwrap()
}

fn equal<T: PartialEq + std::fmt::Debug>(actual: &[T], expected: &[T], label: &str) {
    assert_eq!(actual.len(), expected.len(), "{label} length");
    for (i, (a, e)) in actual.iter().zip(expected).enumerate() {
        assert_eq!(a, e, "{label} at index {i}");
    }
}

fn require_device() -> bool {
    gpu::cuda_built() || std::env::var("MIDNIGHT_GPU_REQUIRE_CUDA").as_deref() == Ok("1")
}

// A successful call must increment its own counter. The integration binary
// serializes cases so another test cannot supply that increment.
fn reason(case: &Value) -> Option<&str> {
    match case["expect"].as_str() {
        None | Some("value" | "run") => None,
        Some("decline") => {
            let r = case["reason"].as_str().expect("decline reason");
            assert!(matches!(
                r,
                "shape"
                    | "below-min-k"
                    | "no-device"
                    | "unreduced"
                    | "device-error"
                    | "memory"
                    | "fault"
            ));
            Some(r)
        }
        Some(other) => panic!("unknown expectation {other}"),
    }
}

thread_local! {
    static REASON_ERRORS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

fn check_hook(
    class: &str,
    successes: impl Fn() -> u64,
    expected: Option<&str>,
    run: impl FnOnce() -> bool,
) -> bool {
    // With no device, eligible values cannot run. Shape and size checks
    // precede device presence in the oracle.
    let expected = match expected {
        None | Some("unreduced") if !require_device() => Some("no-device"),
        other => other,
    };
    let before = successes();
    let before_reasons = gpu::declines();
    let taken = run();
    assert_eq!(taken, expected.is_none(), "{class}: expected {expected:?}");
    assert_eq!(
        successes() - before,
        u64::from(taken),
        "{class}: completions"
    );
    let changes: Vec<_> = gpu::declines()
        .into_iter()
        .filter_map(|(c, r, n)| {
            let old = before_reasons.iter().find(|(cc, rr, _)| *cc == c && *rr == r);
            let delta = n - old.map_or(0, |x| x.2);
            (delta > 0).then_some((c, r, delta))
        })
        .collect();
    if changes != expected.into_iter().map(|r| (class, r, 1)).collect::<Vec<_>>() {
        REASON_ERRORS.with_borrow_mut(|errors| {
            errors.push(format!(
                "{class} min_k={} expected {expected:?}, observed {changes:?}",
                gpu::min_k()
            ))
        });
    }
    taken
}

// The v2 README also specifies the outcome of each short case at the default
// threshold.
fn at_default_threshold(case: &Value, len: usize, check: impl FnOnce(&str)) {
    if case.get("expect").is_none() || len >= (1 << 14) || gpu::min_k() >= 14 {
        return;
    }
    let previous = gpu::min_k();
    gpu::set_min_k(14);
    check(reason(case).unwrap_or("below-min-k"));
    gpu::set_min_k(previous);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Lane {
    Cpu,
    Hook,
}

fn vectors(kind: &str, run: fn(&Value, Lane) -> bool) {
    let _guard = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    install_hooks();
    if require_device() {
        assert!(gpu::device(), "CUDA vector run requires a working device");
    }
    let dir = std::env::var_os("ORACLE_VECTOR_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../gpu-spec/vectors"));
    let mut paths: Vec<_> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|s| s == "json"))
        .collect();
    paths.sort();
    let mut count = 0;
    let mut v2_corpus = false;
    let mut failures = Vec::new();
    for path in paths {
        let file: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let v2 = match file["format"].as_str() {
            Some("midnight-gpu-vectors/1") => false,
            Some("midnight-gpu-vectors/2") => true,
            other => panic!("unknown format {other:?} in {}", path.display()),
        };
        v2_corpus |= v2;
        let tag = file["kind"].as_str().unwrap();
        assert!(
            matches!(tag, "ntt" | "msm" | "coset" | "quotient-numerator")
                || v2 && matches!(tag, "gate" | "threshold" | "datamove"),
            "unknown kind {tag}"
        );
        if tag != kind {
            continue;
        }
        assert_eq!(file["field"]["modulus"], MODULUS);
        assert_eq!(file["field"]["name"], "bls12-381-fr");
        assert_eq!(file["field"]["generator"], "7");
        let cases: Vec<&Value> = if kind == "threshold" {
            let mut cases = Vec::new();
            for op in ["msm", "ntt"] {
                let rows = file[op].as_array().unwrap();
                assert!(!rows.is_empty(), "empty threshold {op} set");
                cases.extend(rows);
            }
            cases
        } else {
            file["cases"].as_array().unwrap().iter().collect()
        };
        assert!(!cases.is_empty(), "no cases in {}", path.display());
        for case in cases {
            count += 1;
            let name = match case["name"].as_str() {
                Some(name) => name.to_owned(),
                None if tag == "gate" => format!("{} row {count}", case["op"]),
                None => panic!("missing case name in {}", path.display()),
            };
            let file_name = path.file_name().unwrap().to_string_lossy();
            for lane in [Lane::Cpu, Lane::Hook] {
                let label = match lane {
                    Lane::Cpu if kind == "gate" => "table",
                    Lane::Cpu => "cpu",
                    Lane::Hook if require_device() => "gpu",
                    Lane::Hook => "stub",
                };
                REASON_ERRORS.with_borrow_mut(Vec::clear);
                let result = std::panic::catch_unwind(|| {
                    if v2 {
                        match kind {
                            "gate" => {
                                assert!(matches!(case["expect"].as_str(), Some("run" | "decline")))
                            }
                            "quotient-numerator" if case.get("expect").is_none() => (),
                            _ => assert!(matches!(
                                case["expect"].as_str(),
                                Some("value" | "decline")
                            )),
                        }
                        if kind == "coset" {
                            assert!(case["shift"].is_string(), "missing v2 coset shift");
                        }
                    }
                    let default = if !v2 || kind == "quotient-numerator" {
                        0
                    } else {
                        14
                    };
                    gpu::set_min_k(case.get("min_k").map_or(default, uint));
                    let applicable = run(case, lane);
                    REASON_ERRORS.with_borrow(|errors| {
                        assert!(errors.is_empty(), "{name}: {errors:#?}");
                    });
                    applicable
                });
                let status = match result {
                    Ok(true) => "pass",
                    Ok(false) => "inapplicable",
                    Err(_) => {
                        failures.push(format!("{label} {file_name} / {name}"));
                        "fail"
                    }
                };
                eprintln!("vector {label} {status} {file_name} / {name}");
            }
        }
    }
    if count == 0 && !v2_corpus && matches!(kind, "gate" | "threshold") {
        eprintln!("{kind}: v2 fixtures pending");
        return;
    }
    if kind == "quotient-numerator" {
        assert_eq!(
            count,
            if v2_corpus { 8 } else { 2 },
            "incomplete quotient corpus"
        );
    }
    assert!(count > 0, "no {kind} vectors");
    assert!(gpu::end_request(), "device cleanup");
    eprintln!("{kind}: {count} cases, counters {:?}", gpu::stats());
    assert!(failures.is_empty(), "failed cases: {failures:#?}");
}

fn scale_powers(values: &mut [Fq], factor: Fq) {
    let mut power = Fq::ONE;
    for value in values {
        *value *= power;
        power *= factor;
    }
}

fn stock_transform(input: &[Fq], root: Fq, log_n: u32, divisor: Option<Fq>) -> Vec<Fq> {
    let mut result = input.to_vec();
    best_fft(&mut result, root, log_n);
    if let Some(d) = divisor {
        result.iter_mut().for_each(|x| *x *= d);
    }
    result
}

fn hook_transform(
    input: &[Fq],
    root: Fq,
    k: u32,
    divisor: Option<Fq>,
    reason: Option<&str>,
) -> Option<Vec<Fq>> {
    let mut out = input.to_vec();
    let taken = check_hook(
        "ntt",
        || gpu::stats().ntt,
        reason,
        || match divisor {
            Some(d) => gpu::ifft(
                adapter::scalars_mut(&mut out),
                adapter::scalar(root),
                k,
                adapter::scalar(d),
            ),
            None => gpu::fft(adapter::scalars_mut(&mut out), adapter::scalar(root), k),
        },
    );
    if !taken {
        equal(&out, input, "declined NTT input");
    }
    taken.then_some(out)
}

#[test]
fn ntt_vectors() {
    vectors("ntt", |case, lane| {
        let input = fields(&case["input"]);
        let k = uint(&case["log_n"]);
        let omega = field(&case["omega"]);
        let reason = reason(case);
        let valid_shape = Some(input.len()) == 1usize.checked_shl(k);
        let divisor = Fq::from(input.len() as u64).invert().unwrap_or(Fq::ONE);
        for (label, root, factor) in [
            ("ntt", omega, None),
            ("intt", omega.invert().unwrap(), Some(divisor)),
        ] {
            let expected = fields(&case[label]);
            if lane == Lane::Hook {
                if let Some(out) = hook_transform(&input, root, k, factor, reason) {
                    equal(&out, &expected, label);
                }
                at_default_threshold(case, input.len(), |why| {
                    assert!(hook_transform(&input, root, k, factor, Some(why)).is_none());
                });
            }
            if !valid_shape {
                assert_eq!(reason, Some("shape"));
                assert!(expected.is_empty());
                continue;
            }
            if k == 0 {
                // ORACLE-30: the singleton has a mathematical value, but the
                // stock transform is undefined here. Check the hook refusal only.
                assert_eq!(omega, Fq::ONE);
                assert_eq!(reason, Some("shape"));
                continue;
            }
            let domain = EvaluationDomain::new(2, k);
            let fft_domain = FftDomain::new(&domain);
            assert_eq!(omega, domain.get_omega());
            let transform = || {
                if factor.is_some() {
                    fft_domain.lagrange_to_coeff(domain.lagrange_from_vec(input.clone())).to_vec()
                } else {
                    fft_domain.coeff_to_lagrange(domain.coeff_from_vec(input.clone())).to_vec()
                }
            };
            if lane == Lane::Cpu {
                equal(&without_hooks(transform), &expected, "stock transform");
                continue;
            }
            // The twiddle table for k=1 has no index 1 from which to read a root.
            let attempts = if factor.is_some() { &IFFT } else { &FFT };
            equal(
                &dispatched(
                    attempts,
                    || gpu::stats().ntt,
                    k > 1,
                    reason.is_none(),
                    transform,
                ),
                &expected,
                "prover transform",
            );
        }
        lane == Lane::Hook || (valid_shape && k > 0)
    });
}

#[test]
fn coset_vectors() {
    vectors("coset", |case, lane| {
        let k = uint(&case["log_n"]);
        let ext = uint(&case["ext"]);
        assert!(ext.is_power_of_two());
        let d = EvaluationDomain::new(ext + 1, k);
        let fd = FftDomain::new(&d);
        let w = field(&case["omega_ext"]);
        assert_eq!(w, d.get_extended_omega());
        let z = field(&case["zeta"]);
        let coeffs = fields(&case["coeffs"]);
        let expected = fields(&case["extended"]);
        let back = fields(&case["back_to_coeffs"]);
        // The stock domain always shifts by ZETA. p((z/ZETA) X) on that
        // domain equals p(X) on the oracle's coset, including shift 7.
        let forward = || {
            let mut a = d.coeff_from_vec(coeffs.clone());
            scale_powers(&mut a, z * Fq::ZETA.invert().unwrap());
            fd.coeff_to_extended(a).to_vec()
        };
        let inverse = || {
            let mut poly = d.empty_extended();
            poly.copy_from_slice(&expected);
            let mut inv = fd.extended_to_coeff(poly);
            scale_powers(&mut inv, Fq::ZETA * z.invert().unwrap());
            inv.truncate(coeffs.len());
            inv
        };
        if lane == Lane::Cpu {
            equal(&without_hooks(forward), &expected, "stock coset");
            equal(&without_hooks(inverse), &back, "stock inverse coset");
            return true;
        }
        equal(
            &dispatched(&IFFT, || gpu::stats().ntt, false, false, inverse),
            &back,
            "prover inverse coset",
        );
        // v1 publishes only values. The resynced quotient takes a primitive cube root.
        let generic = z.cube() != Fq::ONE || z == Fq::ONE;
        let why = if let Some(shift) = case["shift"].as_str() {
            assert_eq!(shift, if generic { "generic" } else { "zeta3" });
            reason(case)
        } else {
            generic.then_some("shape")
        };
        quotient::coset(&d, &coeffs, &expected, z, why);
        at_default_threshold(case, expected.len(), |why| {
            quotient::coset(&d, &coeffs, &expected, z, Some(why));
        });
        true
    });
}

#[test]
fn msm_vectors() {
    vectors("msm", |case, lane| {
        let generator = G1Projective::generator();
        let bases: Vec<G1Affine> = fields(&case["bases"])
            .into_iter()
            .map(|b| (generator * b).to_affine())
            .collect();
        let scalars = fields(&case["scalars"]);
        let why = reason(case);
        let decline = |why: &str| {
            assert!(!check_hook(
                "msm",
                || gpu::stats().msm,
                Some(why),
                || gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_some(),
            ));
        };
        if lane == Lane::Hook {
            at_default_threshold(case, scalars.len(), decline);
        }
        if let Some(why) = why {
            if lane == Lane::Hook {
                decline(why);
                return true;
            }
            // The stock API requires equal lengths. The oracle's mismatch result is
            // the sum over the common prefix.
            let n = scalars.len().min(bases.len());
            assert_eq!(
                without_hooks(|| msm_specific(&scalars[..n], &bases[..n])),
                generator * field(&case["result"])
            );
            return true;
        }
        let mask = fields(&case["mask"]);
        let masked = fields(&case["masked_scalars"]);
        assert_eq!(scalars.len(), bases.len());
        assert_eq!(mask.len(), bases.len());
        let sum: Vec<_> = scalars.iter().zip(&mask).map(|(s, r)| *s + r).collect();
        equal(&sum, &masked, "masked scalars");
        let result = generator * field(&case["result"]);
        let mask_result = generator * field(&case["mask_result"]);
        let msm = |s: &[Fq], expected| {
            if lane == Lane::Cpu {
                let actual = without_hooks(|| msm_specific(s, &bases));
                assert_eq!(actual, expected, "stock MSM");
                return actual;
            }
            let point = || gpu::msm_g1(adapter::scalars(s), adapter::affine(&bases));
            check_hook(
                "msm",
                || gpu::stats().msm,
                None,
                || {
                    point().is_some_and(|p| {
                        assert_eq!(adapter::from_jacobian(p), expected);
                        true
                    })
                },
            );
            let actual = dispatched(
                &MSM,
                || gpu::stats().msm,
                true,
                true,
                || msm_specific(s, &bases),
            );
            assert_eq!(actual, expected, "hook MSM");
            actual
        };
        let direct = msm(&scalars, result);
        assert_eq!(
            msm(&masked, result + mask_result) - msm(&mask, mask_result),
            direct
        );
        true
    });
}

#[test]
fn quotient_vectors() {
    vectors("quotient-numerator", quotient::run);
}

#[test]
fn gate_vectors() {
    vectors("gate", boundaries::gate);
}

#[test]
fn threshold_vectors() {
    vectors("threshold", boundaries::threshold);
}

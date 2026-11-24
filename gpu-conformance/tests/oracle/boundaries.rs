// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

use ff::{Field, PrimeField};
use group::{Curve, Group};
use midnight_curves::{Fq, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::{gpu::adapter, poly::kzg::msm::msm_specific};
use serde_json::Value;

use super::{
    Lane, check_hook, equal, field, fields, hook_transform, reason, require_device,
    stock_transform, uint, without_hooks,
};

fn randoms(mut seed: u64, n: usize) -> Vec<Fq> {
    (0..n)
        .map(|_| {
            let words = std::array::from_fn(|_| {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                seed
            });
            Fq::from_raw(words)
        })
        .collect()
}

pub(super) fn threshold(case: &Value, lane: Lane) -> bool {
    assert_eq!(gpu::min_k(), 14, "default threshold");
    let why = reason(case);
    if let Some(seed) = case["input_seed"].as_u64() {
        let k = uint(&case["log_n"]);
        let root = field(&case["omega"]);
        let input = randoms(seed, 1 << k);
        let stock = stock_transform(&input, root, k, None);
        let first = fields(&case["first"]);
        let last = fields(&case["last"]);
        equal(&stock[..4], &first, "threshold NTT first");
        equal(&stock[stock.len() - 4..], &last, "threshold NTT last");
        let digest = stock.iter().rev().fold(Fq::ZERO, |acc, x| acc * Fq::from(7) + x);
        assert_eq!(digest, field(&case["digest"]), "threshold NTT digest");
        if lane == Lane::Cpu {
            return true;
        }
        if let Some(actual) = hook_transform(&input, root, k, None, why) {
            equal(&actual, &stock, "threshold NTT");
        }
    } else {
        let n = uint(&case["n"]) as usize;
        let scalars = randoms(case["scalars_seed"].as_u64().unwrap(), n);
        let g = G1Projective::generator();
        let bases: Vec<_> = randoms(case["bases_seed"].as_u64().unwrap(), n)
            .into_iter()
            .map(|b| (g * b).to_affine())
            .collect();
        let expected = g * field(&case["result"]);
        if lane == Lane::Cpu {
            assert_eq!(
                without_hooks(|| msm_specific(&scalars, &bases)),
                expected,
                "threshold stock MSM"
            );
            return true;
        }
        check_hook(
            "msm",
            || gpu::stats().msm,
            why,
            || {
                let point = gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases));
                if let Some(point) = point {
                    assert_eq!(
                        adapter::from_jacobian(point),
                        expected,
                        "threshold device MSM"
                    );
                }
                point.is_some()
            },
        );
    }
    true
}

pub(super) fn gate(case: &Value, lane: Lane) -> bool {
    let op = case["op"].as_str().unwrap();
    assert!(matches!(op, "fft" | "ifft" | "msm"));
    let len = uint(&case["len"]) as usize;
    let max = uint(&case["max_log"]);
    let min = uint(&case["min_k"]);
    let device = case["device"].as_bool().unwrap();
    let reduced = case["reduced"].as_bool().unwrap();
    let why = reason(case);
    let decision = if len == 0
        || len > (1usize << max)
        || (op != "msm" && (len < 2 || !len.is_power_of_two()))
    {
        Some("shape")
    } else if len < (1usize << min) {
        Some("below-min-k")
    } else if !device {
        Some("no-device")
    } else if !reduced {
        Some("unreduced")
    } else {
        None
    };
    if lane == Lane::Cpu {
        assert_eq!(decision, why, "pure gate table");
        return true;
    }

    // The gate table also covers hypothetical devices and lengths over 2^28.
    // Exercise the real entry when its configuration and input fit this run.
    // Shape and threshold precede the hardware probe, so an absent device can
    // exercise those same decisions even on a row that specifies a device.
    let independent = matches!(why, Some("shape" | "below-min-k"));
    if max != gpu::MAX_EXT_K || (!independent && device != require_device()) {
        return false;
    }
    if len > (1 << 15) {
        #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
        if !gpu::cuda_built() && len > (1usize << max) {
            oversized_stub_gate(op, len, reduced, why);
            return true;
        }
        return false;
    }
    let mut values = vec![adapter::scalar(Fq::ONE); len];
    if !reduced && !values.is_empty() {
        values[0] = gpu::field::MODULUS;
    }
    if op == "msm" {
        let base = G1Projective::generator().to_affine();
        let bases = vec![base; len];
        check_hook(
            "msm",
            || gpu::stats().msm,
            why,
            || gpu::msm_g1(&values, adapter::affine(&bases)).is_some(),
        );
    } else {
        let original = values.clone();
        let taken = transform_gate(op, &mut values, why);
        if !taken {
            assert_eq!(values, original, "gate decline changed caller buffer");
        }
    }
    true
}

fn transform_gate(op: &str, values: &mut [gpu::Scalar], why: Option<&str>) -> bool {
    let log = values.len().checked_ilog2().unwrap_or(0);
    let mut root = Fq::ROOT_OF_UNITY;
    for _ in log..Fq::S {
        root = root.square();
    }
    check_hook(
        "ntt",
        || gpu::stats().ntt,
        why,
        || match op {
            "fft" => gpu::fft(values, adapter::scalar(root), log),
            _ => gpu::ifft(
                values,
                adapter::scalar(root.invert().unwrap()),
                log,
                adapter::scalar(Fq::ONE),
            ),
        },
    )
}

// Real, initialized slices let the stub inspect a full-size gate request
// without committing tens of GiB. Restrict this probe to a build that cannot
// launch CUDA.
#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
fn oversized_stub_gate(op: &str, len: usize, reduced: bool, why: Option<&str>) {
    assert!(!gpu::cuda_built());
    let scalar_bytes = len.checked_mul(size_of::<gpu::Scalar>()).unwrap();
    let base_bytes = if op == "msm" {
        len.checked_mul(size_of::<gpu::G1AffineLimbs>()).unwrap()
    } else {
        0
    };
    let bytes = scalar_bytes.checked_add(base_bytes).unwrap();
    // SAFETY: anonymous private pages are zero initialized. MAP_NORESERVE leaves
    // the untouched pages uncommitted; the two disjoint arrays have integer limbs.
    let ptr = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            bytes,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_NORESERVE,
            -1,
            0,
        )
    };
    assert_ne!(ptr, libc::MAP_FAILED, "reserve gate input virtual memory");
    // SAFETY: mmap supplies page alignment, each slice fits in its own region
    // and both expire before munmap. No invalid field values are Rust niches.
    let got = unsafe {
        if !reduced {
            ptr.cast::<gpu::Scalar>().write(gpu::field::MODULUS);
        }
        let scalars = std::slice::from_raw_parts_mut(ptr.cast::<gpu::Scalar>(), len);
        if op == "msm" {
            let bases = std::slice::from_raw_parts(
                ptr.byte_add(scalar_bytes).cast::<gpu::G1AffineLimbs>(),
                len,
            );
            check_hook(
                "msm",
                || gpu::stats().msm,
                why,
                || gpu::msm_g1(scalars, bases).is_some(),
            )
        } else {
            let first = scalars[0];
            let taken = transform_gate(op, scalars, why);
            assert_eq!(scalars[0], first);
            assert_eq!(scalars[len - 1], [0; 4]);
            taken
        }
    };
    // SAFETY: this is the region returned by mmap and all borrows have expired.
    assert_eq!(unsafe { libc::munmap(ptr, bytes) }, 0);
    assert!(!got);
}

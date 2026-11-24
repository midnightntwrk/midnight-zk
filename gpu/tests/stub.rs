// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Exercise the actual stub hooks on the prover's inputs. Hook installation
//! lasts for the life of this test binary.

use midnight_gpu as gpu;
use midnight_proofs::gpu::{self as hooks, GpuHooks, test_switches::RandomCircuit};

#[test]
#[cfg_attr(midnight_gpu_cuda, ignore = "requires the CPU stub")]
fn stub_hooks_fall_back_to_cpu() {
    assert!(!gpu::cuda_built());
    assert!(!gpu::device());
    gpu::set_min_k(1);

    let c = RandomCircuit::new(5, true, 6);
    let (cpu, valid) = c.prove();
    assert!(valid);
    // This circuit does not need a separate forward FFT during proving.
    let domain = midnight_proofs::poly::EvaluationDomain::new(3, 3);
    let fft_domain = midnight_proofs::poly::FftDomain::new(&domain);
    let coeffs = domain.coeff_from_vec((0..8u64).map(midnight_curves::Fq::from).collect());
    let evaluations = fft_domain.coeff_to_lagrange(coeffs.clone());
    assert!(hooks::install(GpuHooks {
        msm_g1: Some(gpu::msm_g1),
        fft: Some(gpu::fft),
        ifft: Some(gpu::ifft),
        quotient: Some(gpu::quotient),
    }));

    // Both transforms report as ntt. Observe each call separately.
    assert!(gpu::declines().is_empty());
    let forward = fft_domain.coeff_to_lagrange(coeffs.clone());
    assert_eq!(gpu::declines(), [("ntt", "no-device", 1)]);
    assert_eq!(forward[..], evaluations[..]);
    assert_eq!(fft_domain.lagrange_to_coeff(forward)[..], coeffs[..]);
    assert_eq!(gpu::declines(), [("ntt", "no-device", 2)]);
    let (fallback, valid) = c.prove();
    assert!(valid);
    assert_eq!(cpu, fallback);
    let declines = gpu::declines();
    for class in ["msm", "quotient"] {
        assert!(
            declines
                .iter()
                .any(|&(c, reason, n)| c == class && reason == "no-device" && n > 0),
            "missing {class}/no-device in {declines:?}"
        );
    }
}

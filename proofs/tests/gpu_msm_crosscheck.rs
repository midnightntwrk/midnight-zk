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

//! The test-build cross-check of a hook-served commitment MSM (feature
//! `gpu-test`). In its own test binary: hooks are installed once per process.
#![cfg(feature = "gpu-test")]

use group::Group;
use midnight_curves::G1Projective;
use midnight_proofs::gpu::{
    self, GpuHooks,
    adapter::{self, G1AffineLimbs, G1JacobianLimbs, Scalar},
};

/// An MSM hook that serves every call with the generator: a wrong result for
/// almost every commitment.
fn wrong_msm(_: &[Scalar], _: &[G1AffineLimbs]) -> Option<G1JacobianLimbs> {
    Some(adapter::jacobian(&G1Projective::generator()))
}

/// A hook that returns a wrong MSM fails the cross-check against
/// `msm_pippenger` in a test build, at the first commitment.
#[test]
#[should_panic(expected = "the MSM hook disagrees with msm_pippenger")]
fn wrong_msm_hook_fails_the_cross_check() {
    assert!(gpu::install(GpuHooks {
        msm_g1: Some(wrong_msm),
        ..GpuHooks::default()
    }));
    let c = gpu::test_switches::RandomCircuit::new(5, true, 6);
    let _ = c.prove();
}

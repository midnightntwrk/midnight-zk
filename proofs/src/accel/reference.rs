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

//! A CPU implementation of every [`Accelerator`] method with the stock
//! prover's own algorithms: the conformance reference for accelerator
//! backends. A backend's output must equal this one's on every input it
//! serves.

use midnight_curves::{Fq, G1Affine, G1Projective, fft::best_fft, msm::msm_pippenger};

use super::{Accelerator, QuotientJob};

/// Serves every call on the CPU, with the stock algorithms.
#[derive(Clone, Copy, Debug, Default)]
pub struct CpuReference;

impl Accelerator for CpuReference {
    fn msm_g1(&self, scalars: &[Fq], bases: &[G1Affine]) -> Option<G1Projective> {
        Some(msm_pippenger(scalars, bases))
    }

    fn msm_g1_batch(&self, scalars: &[&[Fq]], bases: &[G1Affine]) -> Option<Vec<G1Projective>> {
        Some(scalars.iter().map(|s| msm_pippenger(s, bases)).collect())
    }

    fn fft(&self, a: &mut [Fq], omega: Fq, log_n: u32) -> bool {
        best_fft(a, omega, log_n);
        true
    }

    fn ifft(&self, a: &mut [Fq], omega_inv: Fq, log_n: u32, divisor: Fq) -> bool {
        best_fft(a, omega_inv, log_n);
        a.iter_mut().for_each(|x| *x *= divisor);
        true
    }

    fn quotient(&self, job: &QuotientJob<'_, Fq>, out: &mut [Fq]) -> bool {
        let h = job.divide_reference(job.numerator_reference());
        out.copy_from_slice(&h);
        true
    }
}

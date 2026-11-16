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

//! The polynomial commitment schemes of zk_stdlib.

use midnight_circuits::verifier::{AssignedAccumulator, CurveChip, InCircuitPCS};
use midnight_curves::{Bls12, Fq};
use midnight_proofs::poly::{
    commitment::PolynomialCommitmentScheme,
    fflonk::Fflonk,
    kzg::{
        KZGCommitmentScheme,
        commitment::KZGMultiCommitment,
        msm::DualMSM,
        params::{ParamsKZG, ParamsVerifierKZG},
    },
};

/// KZG over BLS12-381.
pub type KZG = KZGCommitmentScheme<Bls12>;

/// fflonk over [`KZG`], combining up to `2^LOG2_T_MAX` polynomials into each
/// commitment. [`MidnightPCS`] lists the values of `LOG2_T_MAX` it supports.
pub type FflonkKZG<const LOG2_T_MAX: u32> = Fflonk<KZG, LOG2_T_MAX>;

mod sealed {
    pub trait Sealed {}
}

/// The catalog of polynomial commitment schemes supported by zk_stdlib:
/// [`KZG`] and [`FflonkKZG`] with `LOG2_T_MAX` in `1..=4`. Their parameters
/// are a KZG SRS over BLS12-381. The catalog is closed: other schemes cannot
/// implement this trait.
pub trait MidnightPCS:
    sealed::Sealed
    + InCircuitPCS<
        Fq,
        CommitmentChip = CurveChip<Bls12>,
        AssignedVerificationGuard = AssignedAccumulator<Bls12>,
    > + PolynomialCommitmentScheme<
        Fq,
        Parameters = ParamsKZG<Bls12>,
        VerifierParameters = ParamsVerifierKZG<Bls12>,
        Commitment = KZGMultiCommitment<Bls12>,
        VerificationGuard = DualMSM<Bls12>,
    >
{
    /// Identifies the scheme in serialized keys: 0 for [`KZG`] and
    /// `LOG2_T_MAX` for [`FflonkKZG`].
    const ID: u8;

    /// The size of the SRS for circuits of size `2^k`, as the exponent `j`
    /// such that the SRS has `2^j` points. It is the inverse of
    /// [`PolynomialCommitmentScheme::max_k`].
    fn srs_k(k: u32) -> u32;
}

impl sealed::Sealed for KZG {}
impl sealed::Sealed for FflonkKZG<1> {}
impl sealed::Sealed for FflonkKZG<2> {}
impl sealed::Sealed for FflonkKZG<3> {}
impl sealed::Sealed for FflonkKZG<4> {}

impl MidnightPCS for KZG {
    const ID: u8 = 0;

    fn srs_k(k: u32) -> u32 {
        k
    }
}

impl<const LOG2_T_MAX: u32> MidnightPCS for FflonkKZG<LOG2_T_MAX>
where
    Self: sealed::Sealed,
{
    const ID: u8 = LOG2_T_MAX as u8;

    fn srs_k(k: u32) -> u32 {
        k + LOG2_T_MAX
    }
}

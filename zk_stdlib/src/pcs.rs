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

use midnight_curves::{Bls12, Fq};
use midnight_proofs::poly::{
    commitment::PolynomialCommitmentScheme,
    fflonk::Fflonk,
    kzg::{KZGCommitmentScheme, params::ParamsKZG},
};

/// The polynomial commitment scheme of zk_stdlib.
pub type DefaultPCS = KZGCommitmentScheme<Bls12>;

/// The catalog of polynomial commitment schemes supported by zk_stdlib: KZG
/// and fflonk over KZG, for any `LOG2_T_MAX`. Their parameters are a KZG SRS
/// over BLS12-381.
pub trait MidnightPCS: PolynomialCommitmentScheme<Fq, Parameters = ParamsKZG<Bls12>> {
    /// The size of the SRS for circuits of size `2^k`, as the exponent `j`
    /// such that the SRS has `2^j` points. It is the inverse of
    /// [`PolynomialCommitmentScheme::max_k`].
    fn srs_k(k: u32) -> u32;
}

impl MidnightPCS for KZGCommitmentScheme<Bls12> {
    fn srs_k(k: u32) -> u32 {
        k
    }
}

impl<const LOG2_T_MAX: u32> MidnightPCS for Fflonk<KZGCommitmentScheme<Bls12>, LOG2_T_MAX> {
    fn srs_k(k: u32) -> u32 {
        k + LOG2_T_MAX
    }
}

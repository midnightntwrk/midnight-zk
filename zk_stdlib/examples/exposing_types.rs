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

#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(unused_imports)]
//! Module file, to expose all example circuits to benchmarks to check
//! circuit cost model.

pub mod bitcoin_ecdsa_threshold;
pub mod bitcoin_signature;
pub mod ecc_ops;
pub mod ethereum_signature;
pub mod hybrid_mt;
pub mod identity;
pub mod membership;
pub mod native_gadget;
pub mod poseidon;
pub mod rsa_signature;
pub mod schnorr_sig;
pub mod sha_preimage;

// We are doing a bit of a hack to be able to reuse the circuits that are
// defined in the examples folder. To keep clippy happy, we need to define a
// main function at this level.
fn main() {
    ()
}

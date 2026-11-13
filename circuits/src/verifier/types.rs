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

//! Type aliases for the chips and assigned types of the in-circuit verifier.

use midnight_curves::pairing::Engine;

use crate::{
    ecc::foreign::weierstrass_chip::ForeignWeierstrassEccChip,
    field::{NativeChip, NativeGadget, decomposition::chip::P2RDecompositionChip},
    types::AssignedForeignPoint,
};

/// The chip implementing native field arithmetic in the in-circuit verifier.
pub type ScalarChip<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// The chip operating on the (emulated) G1 points of the pairing engine `E`.
pub type CurveChip<E> = ForeignWeierstrassEccChip<
    <E as Engine>::Fr,
    <E as Engine>::G1,
    <E as Engine>::G1,
    ScalarChip<<E as Engine>::Fr>,
    ScalarChip<<E as Engine>::Fr>,
>;

/// An assigned (emulated) G1 point of the pairing engine `E`.
pub type AssignedG1<E> =
    AssignedForeignPoint<<E as Engine>::Fr, <E as Engine>::G1, <E as Engine>::G1>;

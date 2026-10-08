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

use midnight_curves::Bls12;
use midnight_proofs::poly::kzg::KZGCommitmentScheme;

/// The polynomial commitment scheme of zk_stdlib.
pub type DefaultPCS = KZGCommitmentScheme<Bls12>;

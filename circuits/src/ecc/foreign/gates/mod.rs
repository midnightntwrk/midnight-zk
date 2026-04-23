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

//! Custom gates and geometric assertions for the foreign-field ECC chip.
//!
//! # Structure
//!
//! - [`unified`] — the single PLONK custom gate enforcing
//!   `cond · [a·A² + b·B + d·D + e·E + ca·(C·A) + cd·(C·D) − (u + k_min)·m] = 0`.
//!
//! - [`assert_add`] — point-addition assertion fusing three unified-gate
//!   instantiations into an 8-row region, sharing one row between the slope gates.
//!
//! - [`assert_double`] — point-doubling assertion fusing three unified-gate
//!   instantiations into a 7-row region, sharing two rows between consecutive gates.
//!
//! - [`utils`] — shared witness-assignment helpers used by the above.

pub(crate) mod assert_add;
pub(crate) mod assert_double;
pub(crate) mod unified;
pub(super) mod utils;

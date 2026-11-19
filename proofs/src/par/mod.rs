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

//! Parallel CPU paths of the prover (feature `prover-par`).
//!
//! Each function here computes exactly the values of the stock function it
//! replaces at its call site, bit for bit, whatever the thread count: no
//! random draw and no transcript operation happens in this module, so the
//! proof bytes do not depend on the feature.
#![allow(dead_code)]

pub(crate) mod columns;
pub(crate) mod invert;
pub(crate) mod open;
pub(crate) mod product;

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

//! Implementation of a Merkle Mountain Range (MMR).
//!
//! An MMR is an append-only structure consisting of an array of complete
//! binary Merkle trees (the *mountains*) of pairwise distinct heights. The
//! mountains mirror the binary decomposition of the number of appended
//! elements: the mountain of height `i` exists iff bit `i` of `size` is set,
//! and taller mountains contain the older elements.
//!
//! For example, an MMR with 11 = 0b1011 elements consists of mountains of
//! heights 3, 1 and 0:
//!
//! ```text
//!                    *
//!                  /   \
//!                 /     \
//!                *       *
//!               / \     / \
//!              *   *   *   *      *
//!             /\   /\  /\  /\    / \
//!    leaf:   0 1  2 3 4 5 6 7   8   9    10
//!            \_______________/  \____/   \_/
//!                 height 3     height 1  height 0
//!                (peaks[3])   (peaks[1]) (peaks[0])
//! ```
//!
//! Appending an element works like a binary increment: the new element forms
//! a mountain of height 0 and, while another mountain of the same height
//! exists, the two merge into a mountain of one more height (the older
//! mountain becoming the left child).
//!
//! Hashing is domain-separated by arity: a leaf is hashed as `H([elem])`
//! (arity 1) while internal nodes are hashed as `H([left, right])` (arity 2).
//! This distinction is load-bearing for soundness: mountains have
//! heterogeneous heights, so without it an internal node could be presented
//! as a leaf (and vice versa). The hash function `H` must therefore
//! domain-separate its input lengths, as Poseidon does.
//!
//! An MMR is succinctly represented by its [MmrState](cpu::MmrState): the
//! number of appended elements together with the array of mountain roots
//! (the *peaks*). This module provides, both off-circuit and in-circuit,
//! verification that the elements of an MMR are a prefix of the elements of
//! another MMR, given a witness of at most one node per height (a
//! [SummitPath](cpu::SummitPath)).

pub mod cpu;
pub mod mmr_gadget;

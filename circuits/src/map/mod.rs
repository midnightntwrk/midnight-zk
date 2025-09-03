// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

//! Succinct Key-Value Map Representation Using Merkle Trees
//!
//! This structure represents a key-value map, where each element (key) is
//! uniquely mapped to a path within a binary Merkle tree, and its associated
//! value is stored at the corresponding leaf. The entire map is compactly
//! represented by the Merkle root, enabling efficient verification of
//! individual elements.
//!
//! The Merkle tree is initialized with zeroes at all nodes, allowing only one
//! node per level to be stored in memory. The tree’s structure is as follows:
//! ```text
//!                     ROOT
//!                /              \
//!            node_n            node_n
//!               ...
//!            /      \
//!         node_2   node_2
//!         /    \
//!     node_1  node_1
//!      /    \
//!     0      0
//! ```
//! Each node is computed once and hashed with itself, maintaining a single
//! node per level in memory to optimize space.
//!
//! When adding or updating a key-value pair, the hash of the key determines
//! its path in the tree, leading to a specific leaf where the associated value
//! is stored. This leaf’s value can be set or retrieved by the caller. Any
//! updates propagate up the path to the root to reflect changes in the Merkle
//! root.
//!
//! This structure enables succinct in-circuit proofs of inclusion or exclusion
//! by updating the value at the relevant leaf. Verification requires only the
//! Merkle root, providing a compact and efficient means to prove the presence
//! or absence of any element within the map.
//!
//!
//! A non-empty tree consists of the initial zero nodes plus the updated paths
//! for added elements. For a tree of height 128, the storage size per element
//! is approximately `n * 56 * 128`, or around 7KB. Verification of map
//! or non-map only requires the root hash.
pub mod cpu;
pub mod map_gadget;

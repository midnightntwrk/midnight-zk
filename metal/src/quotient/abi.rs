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

//! The quotient job as `midnight_proofs::gpu` passes it: a copy of the
//! `repr(C)` layout of `midnight_proofs::gpu::abi`, version [`QUOTIENT_ABI`].
//! `tests/quotient.rs` compares the layouts field by field.
//!
//! Every pointer is a host pointer valid for the hook call. Proof polynomials
//! hold `2^k` coefficients, proving-key polynomials `2^ext_k` extended-coset
//! values; a fixed column the job does not read is null.

use crate::Scalar;

/// The layout version this crate reads; any other job is declined.
pub const QUOTIENT_ABI: u32 = 1;

/// Operand tag: a uniform value.
pub const TAG_UNIFORM: u32 = 0;
/// Operand tag: a column read.
pub const TAG_READ: u32 = 1;
/// Operand tag: a scratch slot.
pub const TAG_SLOT: u32 = 2;
/// The index bits of an operand (`(tag << 30) | index`).
pub const INDEX_MASK: u32 = (1 << 30) - 1;

/// Operation kind: `a + b`.
pub const OP_ADD: u32 = 0;
/// Operation kind: `a - b`.
pub const OP_SUB: u32 = 1;
/// Operation kind: `a * b`.
pub const OP_MUL: u32 = 2;
/// Operation kind: `a^2`.
pub const OP_SQUARE: u32 = 3;
/// Operation kind: `2a`.
pub const OP_DOUBLE: u32 = 4;
/// Operation kind: `-a`.
pub const OP_NEGATE: u32 = 5;
/// Operation kind: `a * b + c`.
pub const OP_MUL_ADD: u32 = 6;

/// Column kind: fixed.
pub const COLUMN_FIXED: u32 = 0;
/// Column kind: advice.
pub const COLUMN_ADVICE: u32 = 1;
/// Column kind: instance.
pub const COLUMN_INSTANCE: u32 = 2;

/// One operation: `dst` is a slot, `a`, `b`, `c` are operands.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeviceOp {
    /// One of the `OP_*` constants.
    pub kind: u32,
    /// The slot written.
    pub dst: u32,
    /// First operand.
    pub a: u32,
    /// Second operand.
    pub b: u32,
    /// Third operand (`OP_MUL_ADD` only).
    pub c: u32,
}

/// A column read at the current row rotated by `rotation` base-domain rows.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeviceRead {
    /// One of the `COLUMN_*` constants.
    pub kind: u32,
    /// Column index within its kind.
    pub column: u32,
    /// Rotation, in rows of the base domain.
    pub rotation: i32,
}

/// A program (a lowered flat evaluator).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct ProgramAbi {
    /// Operations.
    pub ops: *const DeviceOp,
    /// Their count.
    pub nops: usize,
    /// Column reads.
    pub reads: *const DeviceRead,
    /// Their count.
    pub nreads: usize,
    /// Uniform values.
    pub uniforms: *const Scalar,
    /// Their count.
    pub nuniforms: usize,
    /// Output operands.
    pub outputs: *const u32,
    /// Their count.
    pub noutputs: usize,
    /// Scratch slots per row.
    pub nslots: u32,
    /// Zero.
    pub pad: u32,
}

/// One LogUp argument: one helper and one program per chunk.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct LookupAbi {
    /// Aggregator coefficients.
    pub aggregator: *const Scalar,
    /// Multiplicities coefficients.
    pub multiplicities: *const Scalar,
    /// One helper per chunk, coefficients.
    pub helpers: *const *const Scalar,
    /// One program per chunk.
    pub programs: *const ProgramAbi,
    /// Chunks.
    pub nchunks: usize,
}

/// One trash argument.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct TrashAbi {
    /// Trash coefficients.
    pub trash: *const Scalar,
    /// The compressed constraints, one output.
    pub program: ProgramAbi,
    /// Fixed column of the selector.
    pub selector_column: u32,
    /// Zero.
    pub pad: u32,
}

/// The quotient job.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct QuotientJobAbi {
    /// The layout version, `QUOTIENT_ABI`.
    pub abi: u32,
    /// log2 of the domain.
    pub k: u32,
    /// log2 of the extended domain.
    pub ext_k: u32,
    /// The scratch slots one row needs (largest program).
    pub nslots: u32,
    /// `[g_coset, g_coset_inv]`: the factors into the coset.
    pub zeta: [Scalar; 2],
    /// The extended root.
    pub extended_omega: Scalar,
    /// Challenge `y`.
    pub y: Scalar,
    /// Challenge `beta`.
    pub beta: Scalar,
    /// Challenge `gamma`.
    pub gamma: Scalar,
    /// `beta * g_coset`.
    pub delta_start: Scalar,
    /// The field's `DELTA`.
    pub delta: Scalar,
    /// The advice columns, coefficients.
    pub advice: *const *const Scalar,
    /// Their count.
    pub nadvice: usize,
    /// The instance columns, coefficients.
    pub instance: *const *const Scalar,
    /// Their count.
    pub ninstance: usize,
    /// The fixed columns, extended cosets; null when not read.
    pub fixed: *const *const Scalar,
    /// Their count.
    pub nfixed: usize,
    /// `l_0`, extended coset.
    pub l0: *const Scalar,
    /// `l_last`, extended coset.
    pub l_last: *const Scalar,
    /// `l_active_row`, extended coset.
    pub l_active: *const Scalar,
    /// The custom gates, one output.
    pub gates: ProgramAbi,
    /// Permuted columns; 0: no permutation argument.
    pub perm_ncolumns: usize,
    /// `COLUMN_*` kind of each permuted column.
    pub perm_column_kind: *const u32,
    /// Index of each permuted column within its kind.
    pub perm_column_index: *const u32,
    /// The permutation polynomials of the key, extended cosets, one per column.
    pub perm_sigma: *const *const Scalar,
    /// The accumulator of each set, coefficients.
    pub perm_products: *const *const Scalar,
    /// Sets.
    pub perm_nsets: usize,
    /// Columns per set.
    pub perm_chunk_len: u32,
    /// The rotation of the last active row, `-(blinding_factors + 1)`.
    pub perm_last_rotation: i32,
    /// The flattened lookup arguments, in the prover's order.
    pub lookups: *const LookupAbi,
    /// Their count.
    pub nlookups: usize,
    /// The trash arguments, in the prover's order.
    pub trash: *const TrashAbi,
    /// Their count.
    pub ntrash: usize,
    /// `1 / t(zeta * extended_omega^i)` for `i < 2^(ext_k - k)`.
    pub t_inv: *const Scalar,
    /// Its length.
    pub nt_inv: usize,
    /// The inverse extended root.
    pub omega_inv: Scalar,
    /// `1 / 2^ext_k`.
    pub divisor: Scalar,
    /// `[g_coset_inv, g_coset]`.
    pub zeta_out: [Scalar; 2],
    /// Coefficients of `h(X)` the hook writes, `(n - 1) *
    /// quotient_poly_degree`.
    pub len: usize,
}

/// A slice from a pointer and a count (empty for a zero count).
///
/// # Safety
/// For a non-zero count, `p` is valid for `n` reads.
pub(crate) unsafe fn slice<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if n == 0 {
        &[]
    } else {
        // SAFETY: the caller's contract.
        unsafe { std::slice::from_raw_parts(p, n) }
    }
}

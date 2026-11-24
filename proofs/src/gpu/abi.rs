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

//! The C layout of a [`QuotientJob`] that the quotient
//! hook receives (version [`QUOTIENT_ABI`]).
//!
//! An accelerator crate keeps a copy of these `repr(C)` types (it does not
//! depend on this crate) and checks [`QuotientJobAbi::abi`] first. Every
//! pointer is a host pointer, valid for the duration of the hook call.
//! Scalars are [`Scalar`] limbs. Polynomials of the proof point to `2^k`
//! coefficients, polynomials of the proving key to `2^ext_k` values of the
//! extended coset. A fixed column the job does not read is a null pointer.
#![allow(unsafe_code)]

use std::ffi::c_void;

use midnight_curves::Fq;

use super::{
    DeviceOp, DeviceProgram, DeviceRead, QuotientJob,
    adapter::{Scalar, scalar, scalars},
};

/// Version of this layout.
pub const QUOTIENT_ABI: u32 = 1;

/// A [`DeviceProgram`].
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

/// A [`LookupJob`](super::LookupJob).
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

/// A [`TrashJob`](super::TrashJob).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct TrashAbi {
    /// Trash coefficients.
    pub trash: *const Scalar,
    /// The program.
    pub program: ProgramAbi,
    /// Fixed column of the selector.
    pub selector_column: u32,
    /// Zero.
    pub pad: u32,
}

/// A [`QuotientJob`].
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct QuotientJobAbi {
    /// [`QUOTIENT_ABI`].
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
    /// The fixed columns, extended cosets; null for a column the job does not
    /// read.
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
    /// Coefficients of `h(X)` the hook writes.
    pub len: usize,
}

/// A packed job: the [`QuotientJobAbi`] and the tables it points to. The
/// pointers stay valid while this value and the job it was built from live.
#[derive(Debug)]
pub struct PackedJob {
    job: Box<QuotientJobAbi>,
    _ptrs: Vec<Vec<*const Scalar>>,
    _u32s: Vec<Vec<u32>>,
    _programs: Vec<Vec<ProgramAbi>>,
    _lookups: Vec<LookupAbi>,
    _trash: Vec<TrashAbi>,
}

impl PackedJob {
    /// The job pointer the hook receives.
    pub fn as_ptr(&self) -> *const c_void {
        &*self.job as *const QuotientJobAbi as *const c_void
    }

    /// Packs `job`.
    pub fn new(job: &QuotientJob<'_, Fq>) -> Self {
        let mut ptrs: Vec<Vec<*const Scalar>> = Vec::new();
        let mut keep = |v: Vec<*const Scalar>| -> *const *const Scalar {
            let p = v.as_ptr();
            ptrs.push(v);
            p
        };
        let poly = |p: &[Fq]| scalars(p).as_ptr();
        let program = |p: &DeviceProgram<Fq>| ProgramAbi {
            ops: p.ops.as_ptr(),
            nops: p.ops.len(),
            reads: p.reads.as_ptr(),
            nreads: p.reads.len(),
            uniforms: scalars(&p.uniforms).as_ptr(),
            nuniforms: p.uniforms.len(),
            outputs: p.outputs.as_ptr(),
            noutputs: p.outputs.len(),
            nslots: p.nslots,
            pad: 0,
        };
        let advice = keep(job.advice.iter().map(|p| poly(p)).collect());
        let instance = keep(job.instance.iter().map(|p| poly(p)).collect());
        let fixed = keep(job.fixed.iter().map(|p| p.map_or(std::ptr::null(), poly)).collect());
        let mut u32s = Vec::new();
        let mut programs = Vec::new();
        let (mut perm_column_kind, mut perm_column_index) = (std::ptr::null(), std::ptr::null());
        let (mut perm_sigma, mut perm_products) = (std::ptr::null(), std::ptr::null());
        let (mut perm_ncolumns, mut perm_nsets, mut perm_chunk_len, mut perm_last_rotation) =
            (0, 0, 0, 0);
        if let Some(p) = &job.permutation {
            let kinds: Vec<u32> = p.columns.iter().map(|c| c.0).collect();
            let idx: Vec<u32> = p.columns.iter().map(|c| c.1).collect();
            perm_column_kind = kinds.as_ptr();
            perm_column_index = idx.as_ptr();
            u32s.push(kinds);
            u32s.push(idx);
            perm_sigma = keep(p.sigma.iter().map(|s| poly(s)).collect());
            perm_products = keep(p.products.iter().map(|s| poly(s)).collect());
            perm_ncolumns = p.columns.len();
            perm_nsets = p.products.len();
            perm_chunk_len = p.chunk_len;
            perm_last_rotation = p.last_rotation;
        }
        let mut lookups = Vec::with_capacity(job.lookups.len());
        for l in &job.lookups {
            let progs: Vec<ProgramAbi> = l.programs.iter().map(program).collect();
            let helpers = keep(l.helpers.iter().map(|h| poly(h)).collect());
            lookups.push(LookupAbi {
                aggregator: poly(l.aggregator),
                multiplicities: poly(l.multiplicities),
                helpers,
                programs: progs.as_ptr(),
                nchunks: l.helpers.len(),
            });
            programs.push(progs);
        }
        let trash: Vec<TrashAbi> = job
            .trash
            .iter()
            .map(|t| TrashAbi {
                trash: poly(t.trash),
                program: program(&t.program),
                selector_column: t.selector_column,
                pad: 0,
            })
            .collect();
        let d = &job.divide;
        let abi = QuotientJobAbi {
            abi: QUOTIENT_ABI,
            k: job.k,
            ext_k: job.ext_k,
            nslots: job.nslots(),
            zeta: [scalar(job.zeta[0]), scalar(job.zeta[1])],
            extended_omega: scalar(job.extended_omega),
            y: scalar(job.y),
            beta: scalar(job.beta),
            gamma: scalar(job.gamma),
            delta_start: scalar(job.delta_start),
            delta: scalar(job.delta),
            advice,
            nadvice: job.advice.len(),
            instance,
            ninstance: job.instance.len(),
            fixed,
            nfixed: job.fixed.len(),
            l0: poly(job.l0),
            l_last: poly(job.l_last),
            l_active: poly(job.l_active),
            gates: program(&job.gates),
            perm_ncolumns,
            perm_column_kind,
            perm_column_index,
            perm_sigma,
            perm_products,
            perm_nsets,
            perm_chunk_len,
            perm_last_rotation,
            lookups: lookups.as_ptr(),
            nlookups: lookups.len(),
            trash: trash.as_ptr(),
            ntrash: trash.len(),
            t_inv: scalars(&d.t_inv).as_ptr(),
            nt_inv: d.t_inv.len(),
            omega_inv: scalar(d.omega_inv),
            divisor: scalar(d.divisor),
            zeta_out: [scalar(d.zeta_out[0]), scalar(d.zeta_out[1])],
            len: d.len,
        };
        PackedJob {
            job: Box::new(abi),
            _ptrs: ptrs,
            _u32s: u32s,
            _programs: programs,
            _lookups: lookups,
            _trash: trash,
        }
    }
}

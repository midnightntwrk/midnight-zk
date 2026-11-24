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

//! The `repr(C)` job types of this crate equal those of
//! `midnight_proofs::gpu::abi`, field by field (offsets, sizes, alignment).

use std::mem::{align_of, offset_of, size_of};

use midnight_gpu::abi as g;
use midnight_proofs::gpu::{self as p, abi as pa};

macro_rules! same {
    ($a:ty, $b:ty, $($f:ident),*) => {
        assert_eq!(size_of::<$a>(), size_of::<$b>(), stringify!($a));
        assert_eq!(align_of::<$a>(), align_of::<$b>(), stringify!($a));
        $(assert_eq!(offset_of!($a, $f), offset_of!($b, $f), concat!(stringify!($a), ".", stringify!($f)));)*
    };
}

#[test]
fn layouts_match() {
    same!(g::DeviceOp, p::DeviceOp, kind, dst, a, b, c);
    same!(g::DeviceRead, p::DeviceRead, kind, column, rotation);
    same!(
        g::ProgramAbi,
        pa::ProgramAbi,
        ops,
        nops,
        reads,
        nreads,
        uniforms,
        nuniforms,
        outputs,
        noutputs,
        nslots
    );
    same!(
        g::LookupAbi,
        pa::LookupAbi,
        aggregator,
        multiplicities,
        helpers,
        programs,
        nchunks
    );
    same!(g::TrashAbi, pa::TrashAbi, trash, program, selector_column);
    same!(
        g::QuotientJobAbi,
        pa::QuotientJobAbi,
        abi,
        k,
        ext_k,
        nslots,
        zeta,
        extended_omega,
        y,
        beta,
        gamma,
        delta_start,
        delta,
        advice,
        nadvice,
        instance,
        ninstance,
        fixed,
        nfixed,
        l0,
        l_last,
        l_active,
        gates,
        perm_ncolumns,
        perm_column_kind,
        perm_column_index,
        perm_sigma,
        perm_products,
        perm_nsets,
        perm_chunk_len,
        perm_last_rotation,
        lookups,
        nlookups,
        trash,
        ntrash,
        t_inv,
        nt_inv,
        omega_inv,
        divisor,
        zeta_out,
        len
    );
    assert_eq!(g::QUOTIENT_ABI, pa::QUOTIENT_ABI);
    assert_eq!(
        [g::TAG_UNIFORM, g::TAG_READ, g::TAG_SLOT, g::INDEX_MASK],
        [p::TAG_UNIFORM, p::TAG_READ, p::TAG_SLOT, p::INDEX_MASK]
    );
    assert_eq!(
        [
            g::OP_ADD,
            g::OP_SUB,
            g::OP_MUL,
            g::OP_SQUARE,
            g::OP_DOUBLE,
            g::OP_NEGATE,
            g::OP_MUL_ADD
        ],
        [
            p::OP_ADD,
            p::OP_SUB,
            p::OP_MUL,
            p::OP_SQUARE,
            p::OP_DOUBLE,
            p::OP_NEGATE,
            p::OP_MUL_ADD
        ]
    );
    assert_eq!(
        [g::COLUMN_FIXED, g::COLUMN_ADVICE, g::COLUMN_INSTANCE],
        [p::COLUMN_FIXED, p::COLUMN_ADVICE, p::COLUMN_INSTANCE]
    );
    // the hook signatures take these functions as they are
    let _ = p::GpuHooks {
        msm_g1: Some(midnight_gpu::msm_g1),
        fft: Some(midnight_gpu::fft),
        ifft: Some(midnight_gpu::ifft),
        quotient: Some(midnight_gpu::quotient),
    };
}

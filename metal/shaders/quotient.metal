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

// The quotient numerator nu(X) on the extended coset (src/quotient.rs), a port
// of the CUDA kernel `mgpu_quotient_kernel` (gpu/cuda/quotient.cuh).
//
// The job is the one midnight-proofs builds from its flat evaluators
// (gpu::QuotientJob): the gates program, the permutation terms, the LogUp terms
// of each lookup, the trash terms, each step `value = value * y + term`, as
// `QuotientJob::numerator_reference` computes them. Field arithmetic is exact,
// so every value equals the CPU value bit for bit.
//
// Where the structure differs from CUDA:
// - No pointer tables. A polynomial is a "handle" `(bank << 30) | index`: the
//   extended coset `index` (2^ext_k values) of one of three flat buffers,
//   bank 0 the proof's cosets, bank 1 the resident proving-key copy, bank 2
//   the proving-key polynomials uploaded for the call.
// - The job's tables (programs, permutation columns, lookups, trash) are one
//   buffer of 32-bit words addressed by word offsets (`quotient.h`), the
//   programs' uniforms one buffer of field elements.
// - One dispatch covers the rows [row0, row_end) with `threads` threads, each
//   thread taking the rows row0 + tid, row0 + tid + threads, ...; the host
//   splits the domain over several command buffers. Program intermediates live
//   in a device buffer, slot-major: scratch[slot * threads + tid].

#include "fr.h"
#include "quotient.h"

namespace quotient {

struct Banks {
    device const Fr *proof;
    device const Fr *key_res;
    device const Fr *key_tmp;
    uint ext_k;
};

MONT_INLINE Fr column(thread const Banks &b, uint handle, uint row) {
    const uint bank = handle >> HANDLE_SHIFT;
    const ulong off = ((ulong)(handle & HANDLE_MASK) << b.ext_k) + row;
    device const Fr *base = bank == BANK_PROOF ? b.proof : (bank == BANK_KEY_RES ? b.key_res : b.key_tmp);
    return base[off];
}

// Row `idx` rotated by `rot` rows of the base domain (2^log_scale extended
// rows each), modulo the extended size: the wrap of a 32-bit sum is a multiple
// of 2^ext_k, so the mask gives the reference's `wrapping_add & (n - 1)`.
MONT_INLINE uint rotate(uint idx, int rot, constant Params &p) {
    return (idx + ((uint)rot << p.log_scale)) & p.mask;
}

struct Ctx {
    Banks banks;
    device const uint *w;
    device const Fr *uni;
    device Fr *scratch;
    uint threads;
    uint tid;
    uint idx;
};

MONT_INLINE Fr operand(thread const Ctx &c, constant Params &p, uint reads, uint unis, uint o) {
    const uint i = o & OPERAND_MASK;
    switch (o >> OPERAND_SHIFT) {
    case TAG_UNIFORM:
        return c.uni[unis + i];
    case TAG_READ: {
        const uint h = c.w[reads + 2u * i];
        const int rot = as_type<int>(c.w[reads + 2u * i + 1u]);
        return column(c.banks, h, rotate(c.idx, rot, p));
    }
    default:
        return c.scratch[(ulong)i * c.threads + c.tid];
    }
}

// Runs the program at word offset `pd` for the current row; writes its first
// noutputs (at most 4) outputs.
void program(thread const Ctx &c, constant Params &p, uint pd, thread Fr *out) {
    const uint ops = c.w[pd + PROG_OPS];
    const uint nops = c.w[pd + PROG_NOPS];
    const uint reads = c.w[pd + PROG_READS];
    const uint unis = c.w[pd + PROG_UNIFORMS];
    const uint outs = c.w[pd + PROG_OUTPUTS];
    const uint nouts = c.w[pd + PROG_NOUTPUTS];
    for (uint k = 0; k < nops; k++) {
        const uint o = ops + OP_WORDS * k;
        const uint kind = c.w[o];
        const uint dst = c.w[o + 1u];
        const Fr a = operand(c, p, reads, unis, c.w[o + 2u]);
        Fr v;
        switch (kind) {
        case OP_ADD: v = fr_add(a, operand(c, p, reads, unis, c.w[o + 3u])); break;
        case OP_SUB: v = fr_sub(a, operand(c, p, reads, unis, c.w[o + 3u])); break;
        case OP_MUL: v = fr_mul(a, operand(c, p, reads, unis, c.w[o + 3u])); break;
        case OP_SQUARE: v = fr_sqr(a); break;
        case OP_DOUBLE: v = fr_dbl(a); break;
        case OP_NEGATE: v = fr_neg(a); break;
        default:
            v = fr_add(fr_mul(a, operand(c, p, reads, unis, c.w[o + 3u])),
                       operand(c, p, reads, unis, c.w[o + 4u]));
            break;
        }
        c.scratch[(ulong)dst * c.threads + c.tid] = v;
    }
    for (uint k = 0; k < nouts && k < 4u; k++) out[k] = operand(c, p, reads, unis, c.w[outs + k]);
}

MONT_INLINE Fr pow_u32(Fr b, uint e) {
    Fr r = fr_one();
    while (e != 0u) {
        if (e & 1u) r = fr_mul(r, b);
        b = fr_sqr(b);
        e >>= 1;
    }
    return r;
}

} // namespace quotient

kernel void quotient_numerator(device const Fr *proof [[buffer(0)]],
                               device const Fr *key_res [[buffer(1)]],
                               device const Fr *key_tmp [[buffer(2)]],
                               device const uint *words [[buffer(3)]],
                               device const Fr *uniforms [[buffer(4)]],
                               device Fr *nu [[buffer(5)]],
                               device Fr *scratch [[buffer(6)]],
                               constant quotient::Params &p [[buffer(7)]],
                               uint tid [[thread_position_in_grid]]) {
    using namespace quotient;
    Ctx c;
    c.banks.proof = proof;
    c.banks.key_res = key_res;
    c.banks.key_tmp = key_tmp;
    c.banks.ext_k = p.ext_k;
    c.w = words;
    c.uni = uniforms;
    c.scratch = scratch;
    c.threads = p.threads;
    c.tid = tid;
    const Fr one = fr_one();
    const Fr y = p.y;
    Fr o[4];

    const uint first = p.row0 + tid;
    // omega^idx for the permutation's delta powers: one exponentiation per
    // thread, then one multiplication by omega^threads per row
    Fr omega_i = fr_one();
    if (p.perm_nsets != 0u && first < p.row_end) omega_i = pow_u32(p.omega, first);

    for (uint idx = first; idx < p.row_end; idx += p.threads) {
        c.idx = idx;
        program(c, p, p.gates, o);
        Fr value = o[0];
        const Fr l0 = column(c.banks, p.l0, idx);
        const Fr l_last = column(c.banks, p.l_last, idx);
        const Fr l_active = column(c.banks, p.l_active, idx);
        const uint r_next = rotate(idx, 1, p);

        // Permutation.
        if (p.perm_nsets != 0u) {
            const uint zs = p.perm;                    // handles of the accumulators
            const uint cols = zs + p.perm_nsets;       // handles of the permuted columns
            const uint sig = cols + p.perm_ncolumns;   // handles of the sigma cosets
            const uint r_last = rotate(idx, p.perm_last_rotation, p);
            const Fr z_first = column(c.banks, words[zs], idx);
            const Fr z_last = column(c.banks, words[zs + p.perm_nsets - 1u], idx);
            value = fr_add(fr_mul(value, y), fr_mul(fr_sub(one, z_first), l0));
            value = fr_add(fr_mul(value, y), fr_mul(fr_sub(fr_sqr(z_last), z_last), l_last));
            for (uint s = 1; s < p.perm_nsets; s++) {
                const Fr cur = column(c.banks, words[zs + s], idx);
                const Fr prev = column(c.banks, words[zs + s - 1u], r_last);
                value = fr_add(fr_mul(value, y), fr_mul(fr_sub(cur, prev), l0));
            }
            Fr current_delta = fr_mul(p.delta_start, omega_i);
            for (uint s = 0; s < p.perm_nsets; s++) {
                const uint z = words[zs + s];
                const uint c0 = s * p.perm_chunk_len;
                const uint c1 = metal::min(c0 + p.perm_chunk_len, p.perm_ncolumns);
                Fr left = column(c.banks, z, r_next);
                for (uint k = c0; k < c1; k++) {
                    const Fr x = column(c.banks, words[cols + k], idx);
                    const Fr sg = column(c.banks, words[sig + k], idx);
                    left = fr_mul(left, fr_add(fr_add(x, fr_mul(p.beta, sg)), p.gamma));
                }
                Fr right = column(c.banks, z, idx);
                for (uint k = c0; k < c1; k++) {
                    const Fr x = column(c.banks, words[cols + k], idx);
                    right = fr_mul(right, fr_add(fr_add(x, current_delta), p.gamma));
                    current_delta = fr_mul(current_delta, p.delta);
                }
                value = fr_add(fr_mul(value, y), fr_mul(fr_sub(left, right), l_active));
            }
            omega_i = fr_mul(omega_i, p.omega_step);
        }

        // Lookups (LogUp).
        for (uint li = 0; li < p.nlookups; li++) {
            const uint L = p.lookups + LOOKUP_WORDS * li;
            const uint agg = words[L + LOOKUP_AGGREGATOR];
            const uint mult = words[L + LOOKUP_MULTIPLICITIES];
            const uint nchunks = words[L + LOOKUP_NCHUNKS];
            const uint chunks = words[L + LOOKUP_CHUNKS];
            const Fr agg_i = column(c.banks, agg, idx);
            value = fr_add(fr_mul(value, y), fr_mul(agg_i, fr_add(l0, l_last)));
            Fr sum_helpers = fr_zero(), table = fr_zero(), selector = fr_zero();
            for (uint fi = 0; fi < nchunks; fi++) {
                const uint ch = chunks + CHUNK_WORDS * fi;
                program(c, p, words[ch + CHUNK_PROGRAM], o);
                if (fi == 0u) {
                    table = o[2];
                    selector = o[3];
                }
                const Fr h = column(c.banks, words[ch + CHUNK_HELPER], idx);
                value = fr_sub(fr_add(fr_mul(value, y), fr_mul(h, o[1])), o[0]);
                sum_helpers = fr_add(sum_helpers, h);
            }
            const Fr agg_next = column(c.banks, agg, r_next);
            const Fr m = column(c.banks, mult, idx);
            const Fr inner = fr_add(fr_mul(fr_sub(fr_sub(agg_next, agg_i), fr_mul(selector, sum_helpers)), table), m);
            value = fr_add(fr_mul(value, y), fr_mul(l_active, inner));
        }

        // Trash arguments.
        for (uint ti = 0; ti < p.ntrash; ti++) {
            const uint T = p.trash + TRASH_WORDS * ti;
            program(c, p, words[T + TRASH_PROGRAM], o);
            const Fr q = column(c.banks, words[T + TRASH_SELECTOR], idx);
            const Fr t = column(c.banks, words[T + TRASH_POLY], idx);
            value = fr_add(fr_mul(value, y), fr_sub(o[0], fr_mul(fr_sub(one, q), t)));
        }

        nu[idx] = value;
    }
}


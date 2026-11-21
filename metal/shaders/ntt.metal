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

// The scalar-field NTT (src/ntt.rs) and the elementwise kernels around it.
//
// The transform of n = 2^L elements is a Stockham radix-2^d transform: a
// sequence of passes, pass q of radix R_q = 2^d_q, with sum d_q = L. Natural
// order in, natural order out, no bit-reversal pass. Pass q, with p the
// product of the radices of the earlier passes, takes for every column
// j < n / R the R elements x[j + t n / R] (t < R), multiplies element t by
// w_{pR}^{(j mod p) t}, computes their R-point DFT V in threadgroup memory, and
// writes V[r] to y[(j - j mod p) R + j mod p + r p]. The last pass (p R = n)
// reads and writes the same positions, so it may run in place.
//
// A threadgroup takes G = 2^log_g consecutive columns (G R elements), so that
// the strided reads and writes move G consecutive elements at a time. The
// R-point DFT is a radix-2 decimation in frequency over the threadgroup
// memory (natural order in, bit-reversed order out, read back in natural
// order at the write), each thread doing E / (2 T) butterflies of a stage
// (E elements, T threads).
//
// Twiddles come from two tables per direction, with H = hi_bits:
//   hi[j] = w_{2^H}^j (j < 2^H)  and  lo[j] = w_{2^28}^j (j < 2^(28 - H)),
// times a constant c for lo (see below), w_{2^m} the standard 2^m-th root of
// unity (or its inverse). A local butterfly of a DFT of size 2^s <= 2^H reads
// hi[j 2^(H - s)]. The factor w_{pR}^e of a pass is w_{2^28}^x with
// x = e 2^(28 - log pR), = hi[x >> (28 - H)] lo[x mod 2^(28 - H)]; when
// pR <= 2^H the low part is zero and only hi is read. A pass that scales its
// output by c (the divisor of an inverse transform) reads a lo table
// pre-multiplied by c, always through both tables: the DFT is linear, so
// scaling its inputs scales its outputs.

#include "fr.h"

namespace ntt {

constant constexpr uint UNIVERSAL_LOG = 28;

// Pass flags.
constant constexpr uint F_TWIDDLE = 1u;   // multiply the inputs by the pass factors
constant constexpr uint F_TWO_LEVEL = 2u; // the factors read hi and lo
constant constexpr uint F_COSET = 4u;     // the input is coeff_to_extended's

// One pass (the host's `PassParams`, same layout).
struct PassParams {
    uint log_n;   // L
    uint log_r;   // d: this pass's radix is 2^d
    uint log_p;   // log2 of the product of the earlier passes' radices
    uint log_g;   // columns per threadgroup, log2
    uint flags;
    uint n_src;   // F_COSET: source elements (the rest reads as zero)
    uint hi_bits; // H: hi holds 2^H elements, lo 2^(28 - H)
    uint pad;
    Fr z1;        // F_COSET: factor of the elements with index 1 mod 3
    Fr z2;        // F_COSET: factor of the elements with index 2 mod 3
};

// Threadgroup memory holds E elements limb-major (limb c of element i at
// c E + i), so that consecutive threads touch consecutive words.
MONT_INLINE Fr sh_load(threadgroup const uint *sh, uint e, uint i) {
    Fr r;
#pragma unroll
    for (int c = 0; c < 8; c++) r.l[c] = sh[c * e + i];
    return r;
}

MONT_INLINE void sh_store(threadgroup uint *sh, uint e, uint i, Fr v) {
#pragma unroll
    for (int c = 0; c < 8; c++) sh[c * e + i] = v.l[c];
}

MONT_INLINE uint bitrev(uint v, uint bits) {
    return bits == 0 ? 0u : (metal::reverse_bits(v) >> (32u - bits));
}

} // namespace ntt

// One Stockham pass (see the file text), on threadgroups of any size; the
// threadgroup memory [[threadgroup(0)]] holds 2^(log_r + log_g) elements.
kernel void ntt_pass(device const Fr *x [[buffer(0)]],
                     device Fr *y [[buffer(1)]],
                     device const Fr *hi [[buffer(2)]],
                     device const Fr *lo [[buffer(3)]],
                     constant ntt::PassParams &pp [[buffer(4)]],
                     threadgroup uint *sh [[threadgroup(0)]],
                     uint gid [[threadgroup_position_in_grid]],
                     uint lid [[thread_position_in_threadgroup]],
                     uint tpg [[threads_per_threadgroup]]) {
    using namespace ntt;
    const uint d = pp.log_r;
    const uint lg = pp.log_g;
    const uint lp = pp.log_p;
    const uint hb = pp.hi_bits;
    const uint lo_bits = UNIVERSAL_LOG - hb;
    const uint lo_mask = (1u << lo_bits) - 1u;
    const uint gmask = (1u << lg) - 1u;
    const uint e = 1u << (d + lg);
    const uint stride_log = pp.log_n - d;
    const uint j0 = gid << lg;
    const uint pmask = (1u << lp) - 1u;
    const uint xshift = UNIVERSAL_LOG - (lp + d);
    const uint flags = pp.flags;

    // load, with the coset distribution and the pass factors
    for (uint l = lid; l < e; l += tpg) {
        const uint g = l & gmask;
        const uint t = l >> lg;
        const uint j = j0 + g;
        const uint idx = j + (t << stride_log);
        Fr v;
        if (flags & F_COSET) {
            if (idx < pp.n_src) {
                v = x[idx];
                const uint m = idx % 3u;
                if (m == 1u) v = fr_mul(v, pp.z1);
                else if (m == 2u) v = fr_mul(v, pp.z2);
            } else {
                v = fr_zero();
            }
        } else {
            v = x[idx];
        }
        if (flags & F_TWIDDLE) {
            const uint xi = ((j & pmask) * t) << xshift;
            Fr w = hi[xi >> lo_bits];
            if (flags & F_TWO_LEVEL) w = fr_mul(w, lo[xi & lo_mask]);
            v = fr_mul(v, w);
        }
        sh_store(sh, e, (t << lg) | g, v);
    }
    threadgroup_barrier(metal::mem_flags::mem_threadgroup);

    // radix-2 decimation in frequency over each column's R elements
    const uint half_e = e >> 1;
    for (uint s = d; s >= 1u; s--) {
        const uint h = 1u << (s - 1u);
        const uint tw_shift = hb - s;
        for (uint b = lid; b < half_e; b += tpg) {
            const uint g = b & gmask;
            const uint bb = b >> lg;
            const uint jj = bb & (h - 1u);
            const uint i0 = ((bb - jj) << 1) + jj;
            const uint a0 = (i0 << lg) | g;
            const uint a1 = ((i0 + h) << lg) | g;
            const Fr u0 = sh_load(sh, e, a0);
            const Fr u1 = sh_load(sh, e, a1);
            Fr dif = fr_sub(u0, u1);
            if (jj != 0u) dif = fr_mul(dif, hi[jj << tw_shift]);
            sh_store(sh, e, a0, fr_add(u0, u1));
            sh_store(sh, e, a1, dif);
        }
        threadgroup_barrier(metal::mem_flags::mem_threadgroup);
    }

    // write V[r] (at the bit-reversed position r in threadgroup memory)
    const bool by_row = lp < lg;
    for (uint l = lid; l < e; l += tpg) {
        uint g, r;
        if (by_row) {
            // p < G: a column's own outputs are the contiguous ones
            g = l >> d;
            r = l & ((1u << d) - 1u);
        } else {
            g = l & gmask;
            r = l >> lg;
        }
        const uint j = j0 + g;
        const uint k = j & pmask;
        const uint out = ((j - k) << d) + k + (r << lp);
        y[out] = sh_load(sh, e, (bitrev(r, d) << lg) | g);
    }
}

// The elementwise kernels run exactly n threads (`dispatchThreads`, the
// last threadgroup may be partial), so they take no length.

// a[i] *= c.
kernel void ntt_scale(device Fr *a [[buffer(0)]],
                      constant Fr &c [[buffer(1)]],
                      uint gid [[thread_position_in_grid]]) {
    a[gid] = fr_mul(a[gid], c);
}

// dst[i] = src[i] * c.
kernel void ntt_scale_copy(device const Fr *src [[buffer(0)]],
                           device Fr *dst [[buffer(1)]],
                           constant Fr &c [[buffer(2)]],
                           uint gid [[thread_position_in_grid]]) {
    dst[gid] = fr_mul(src[gid], c);
}

// a[i] *= [1, z1, z2][i mod 3].
kernel void ntt_distribute_zeta(device Fr *a [[buffer(0)]],
                                constant Fr &z1 [[buffer(1)]],
                                constant Fr &z2 [[buffer(2)]],
                                uint gid [[thread_position_in_grid]]) {
    const uint m = gid % 3u;
    if (m == 1u) a[gid] = fr_mul(a[gid], z1);
    else if (m == 2u) a[gid] = fr_mul(a[gid], z2);
}

// a[i] *= t[i & mask] (a period of mask + 1, a power of two).
kernel void ntt_mul_periodic(device Fr *a [[buffer(0)]],
                             device const Fr *t [[buffer(1)]],
                             constant uint &mask [[buffer(2)]],
                             uint gid [[thread_position_in_grid]]) {
    a[gid] = fr_mul(a[gid], t[gid & mask]);
}

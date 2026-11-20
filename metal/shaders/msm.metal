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

// The G1 MSM kernels, driven by `src/msm.rs`. Ported from sppark
// `msm/pippenger.cuh`, `msm/sort.cuh` and `msm/batch_addition.cuh`
// (Copyright Supranational LLC, Apache-2.0,
// https://github.com/supranational/sppark, commit
// 08033103c14ff3c742e710b9463dde42acc0f058).
//
// Layout (per batch of `len` points, `stride` the batch capacity):
// - digits: `nwins` rows of `stride` uint. `msm_digits` writes the signed
//   window digits (sppark's encoding: magnitude in the low bits, bit 31 the
//   sign); the sort replaces each row by the point indices sorted by bucket,
//   bit 31 the sign.
// - hist: `nwins` rows of `2^(wbits-1)` uint: after the sort, the inclusive
//   end offset of each bucket in its digits row.
// - buckets: `nwins` rows of `2^(wbits-1)` `g1::Xyzz`; after
//   `msm_integrate`, the first `2 * threads` records of each row hold the
//   partial sums the host combines.

#include "fr.h"
#include "fp.h"
#include "g1.h"
#include "msm.h"

namespace msm {

using namespace metal;

// ---------------------------------------------------------------------------
// Scalars to digits (sppark `breakdown`), with the skew mask (msm.h).

// Scalar modes of `msm_digits` (src/msm/pipeline.rs `MODE_*`).
enum : uint {
    MODE_MASKED = 1,  // s + r
    MODE_MASK = 2,    // r
};

struct DigitsParams {
    uint len;     // scalars in this batch
    uint offset;  // index of the batch's first scalar in the whole MSM
    uint nwins;
    uint wbits;
    uint stride;  // digits row length
    uint mode;
};

MONT_INLINE uint get_wval(thread const Fr &s, uint off) {
    const uint top_i = 7;  // (255 + 31) / 32 - 1
    uint i = off / 32;
    ulong ret = s.l[i];
    if (i < top_i) ret |= (ulong)s.l[i + 1] << 32;
    return (uint)(ret >> (off % 32));
}

MONT_INLINE uint booth_encode(uint wval, uint wmask, uint wbits) {
    uint sign = (wval >> wbits) & 1;
    wval = ((wval + 1) & wmask) >> 1;
    return sign ? 0 - wval : wval;
}

} // namespace msm

// Resets `hot` at the start of each chunk's command buffer. In the mask mode
// `scalars` is bound but not read.
kernel void msm_digits(device const Fr *scalars [[buffer(0)]],
                       device uint *digits [[buffer(1)]],
                       constant msm::DigitsParams &p [[buffer(2)]],
                       device uint *hot [[buffer(3)]],
                       uint i [[thread_position_in_grid]]) {
    using namespace msm;
    if (i == 0) *hot = 0;
    if (i >= p.len) return;

    Fr s;
    if (p.mode == MODE_MASK) {
        s = mask_elem((ulong)p.offset + i);
    } else {
        s = scalars[i];
        if (p.mode == MODE_MASKED) s = fr_add(s, mask_elem((ulong)p.offset + i));
    }

    // out of Montgomery form (sppark `s.from()`): s * 1 * 2^-256
    Fr raw_one = fr_zero();
    raw_one.l[0] = 1;
    s = fr_mul(s, raw_one);

    // sppark `abs()`: make the value "positive", keep the sign
    Fr t;
    uint borrow = 0;
#pragma unroll
    for (int j = 0; j < 8; j++) {
        ulong d = (ulong)FrParams::mod(j) - s.l[j] - borrow;
        t.l[j] = (uint)d;
        borrow = (uint)(d >> 63);
    }
    uint msb = t.l[7] < s.l[7] ? 1u : 0u;
    if (msb) s = t;
    msb <<= 31;

    const uint wbits = p.wbits;
    const uint wmask = 0xffffffffu >> (31 - wbits);  // (1 << (wbits+1)) - 1

    for (uint bit0 = p.nwins * wbits - 1, win = p.nwins; --win;) {
        bit0 -= wbits;
        uint wval = get_wval(s, bit0);
        wval = booth_encode(wval, wmask, wbits);
        if (wval) wval ^= msb;
        digits[(size_t)win * p.stride + i] = wval;
    }

    uint wval = s.l[0] << 1;
    wval = booth_encode(wval, wmask, wbits);
    if (wval) wval ^= msb;
    digits[i] = wval;
}

// ---------------------------------------------------------------------------
// The per-window sort (sppark `sort.cuh`, the two-level path of `sort_row`).
//
// Metal has no grid-wide barrier, so sppark's cooperative `upper_sort` and
// `lower_sort` become four kernels in one command buffer: `msm_sort_count`,
// `msm_sort_scan` (prefix sums across groups), `msm_sort_scatter` and
// `msm_sort_lower`. A pass sorts `pass` windows from `win0`; the group index
// is `window * G + group`.

namespace msm {

struct SortParams {
    uint len;       // digits per row in this batch
    uint stride;    // digits row length
    uint win0;      // first window of the pass
    uint nwins;     // windows in the MSM
    uint groups;    // G: groups per window of the upper sort
    uint top_bits;
    uint low_bits;
    uint bits;      // wbits - 1 = top_bits + low_bits
    uint top_lsbits;  // significant bits of (digit - 1) in the top window
};

// The largest top and low digit counts held in threadgroup memory.
constant uint MAX_TOP = 1u << 9;
constant uint MAX_LOW = 1u << 12;

// a & ~mask | mask & b (sppark `pack`, PTX lop3 0xb8).
MONT_INLINE uint pack(uint a, uint mask, uint b) { return (a & ~mask) | (mask & b); }

MONT_INLINE uint lsbits_of(constant SortParams &p, uint win) {
    return win == p.nwins - 1 ? p.top_lsbits : p.bits;
}

// The slice of `len` a group takes (sppark `upper_sort`).
MONT_INLINE void slice_of(uint len, uint groups, uint g, thread uint &base, thread uint &slice) {
    slice = len / groups;
    uint rem = len % groups;
    if (g < rem)
        base = ++slice * g;
    else
        base = slice * g + rem;
}

// Exclusive prefix sum over the threadgroup, one value per thread; `total` is
// the sum of all values. The threadgroup is whole SIMD-groups of 32 (the host
// checks the width), so the group totals fit one SIMD-group.
MONT_INLINE uint group_exclusive_sum(uint x, threadgroup uint *sg_tot, uint lane, uint sg, uint nsg,
                                     uint width, thread uint &total) {
    uint incl = simd_prefix_inclusive_sum(x);
    if (lane == width - 1) sg_tot[sg] = incl;
    threadgroup_barrier(mem_flags::mem_threadgroup);
    if (sg == 0) {
        uint v = lane < nsg ? sg_tot[lane] : 0;
        uint ex = simd_prefix_exclusive_sum(v);
        uint all = simd_sum(v);
        if (lane < nsg) sg_tot[lane] = ex;
        if (lane == 0) sg_tot[32] = all;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    total = sg_tot[32];
    uint r = incl - x + sg_tot[sg];
    threadgroup_barrier(mem_flags::mem_threadgroup);
    return r;
}

} // namespace msm

kernel void msm_sort_count(device const uint *digits [[buffer(0)]],
                           device uint *counts [[buffer(1)]],
                           constant msm::SortParams &p [[buffer(2)]],
                           uint gid [[threadgroup_position_in_grid]],
                           uint tid [[thread_index_in_threadgroup]],
                           uint tpg [[threads_per_threadgroup]]) {
    using namespace msm;
    threadgroup atomic_uint counters[MAX_TOP];

    const uint g = gid % p.groups, w = gid / p.groups, win = p.win0 + w;
    const uint ntop = 1u << p.top_bits;
    for (uint j = tid; j < ntop; j += tpg) atomic_store_explicit(&counters[j], 0u, memory_order_relaxed);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint base, slice;
    slice_of(p.len, p.groups, g, base, slice);
    const uint lshift = p.bits - lsbits_of(p, win);
    const uint pack_mask = 0xffffffffu << lshift;

    device const uint *src = digits + (size_t)win * p.stride + base;
    for (uint i = tid; i < slice; i += tpg) {
        uint val = src[i];
        uint pck = pack(base + i, pack_mask, (val - 1) << lshift);
        if (val) atomic_fetch_add_explicit(&counters[(pck >> p.low_bits) & (ntop - 1)], 1u,
                                           memory_order_relaxed);
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // counts[window][top digit][group]
    for (uint j = tid; j < ntop; j += tpg)
        counts[((size_t)w * ntop + j) * p.groups + g] =
            atomic_load_explicit(&counters[j], memory_order_relaxed);
}

// One threadgroup per window: the exclusive prefix sums of counts[window] in
// (top digit, group) order, in place, and each top digit's (start, length)
// in the histogram row at index `digit << low_bits` (where sppark's
// upper_sort leaves it for lower_sort).
kernel void msm_sort_scan(device uint *counts [[buffer(0)]],
                          device uint *hist [[buffer(1)]],
                          constant msm::SortParams &p [[buffer(2)]],
                          uint w [[threadgroup_position_in_grid]],
                          uint tid [[thread_index_in_threadgroup]],
                          uint tpg [[threads_per_threadgroup]],
                          uint lane [[thread_index_in_simdgroup]],
                          uint sg [[simdgroup_index_in_threadgroup]],
                          uint nsg [[simdgroups_per_threadgroup]],
                          uint width [[threads_per_simdgroup]]) {
    using namespace msm;
    threadgroup uint sg_tot[33];

    const uint ntop = 1u << p.top_bits;
    const uint m = ntop * p.groups;
    device uint *c = counts + (size_t)w * m;
    const uint chunk = (m + tpg - 1) / tpg;
    const uint lo = min(m, tid * chunk), hi = min(m, lo + chunk);

    uint sum = 0;
    for (uint j = lo; j < hi; j++) sum += c[j];
    uint total;
    uint run = group_exclusive_sum(sum, sg_tot, lane, sg, nsg, width, total);
    for (uint j = lo; j < hi; j++) {
        uint v = c[j];
        c[j] = run;
        run += v;
    }
    threadgroup_barrier(mem_flags::mem_device);

    device uint *row = hist + (size_t)(p.win0 + w) * (1u << p.bits);
    for (uint t = tid; t < ntop; t += tpg) {
        uint start = c[t * p.groups];
        uint end = t + 1 < ntop ? c[(t + 1) * p.groups] : total;
        row[t << p.low_bits] = start;
        row[(t << p.low_bits) + 1] = end - start;
    }
}

kernel void msm_sort_scatter(device const uint *digits [[buffer(0)]],
                             device const uint *counts [[buffer(1)]],
                             device uint2 *temps [[buffer(2)]],
                             constant msm::SortParams &p [[buffer(3)]],
                             uint gid [[threadgroup_position_in_grid]],
                             uint tid [[thread_index_in_threadgroup]],
                             uint tpg [[threads_per_threadgroup]]) {
    using namespace msm;
    threadgroup atomic_uint counters[MAX_TOP];

    const uint g = gid % p.groups, w = gid / p.groups, win = p.win0 + w;
    const uint ntop = 1u << p.top_bits;
    for (uint j = tid; j < ntop; j += tpg)
        atomic_store_explicit(&counters[j], counts[((size_t)w * ntop + j) * p.groups + g],
                              memory_order_relaxed);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    uint base, slice;
    slice_of(p.len, p.groups, g, base, slice);
    const uint lshift = p.bits - lsbits_of(p, win);
    const uint pack_mask = 0xffffffffu << lshift;

    device const uint *src = digits + (size_t)win * p.stride + base;
    device uint2 *dst = temps + (size_t)w * p.stride;
    for (uint i = tid; i < slice; i += tpg) {
        uint val = src[i];
        uint pck = pack(base + i, pack_mask, (val - 1) << lshift);
        if (val) {
            uint idx = atomic_fetch_add_explicit(&counters[(pck >> p.low_bits) & (ntop - 1)], 1u,
                                                 memory_order_relaxed);
            dst[idx] = uint2(pck, pack(base + i, 0x80000000u, val));
        }
    }
}

// One threadgroup per (window, top digit): sppark `lower_sort`.
kernel void msm_sort_lower(device uint *digits [[buffer(0)]],
                           device const uint2 *temps [[buffer(1)]],
                           device uint *hist [[buffer(2)]],
                           constant msm::SortParams &p [[buffer(3)]],
                           uint gid [[threadgroup_position_in_grid]],
                           uint tid [[thread_index_in_threadgroup]],
                           uint tpg [[threads_per_threadgroup]],
                           uint lane [[thread_index_in_simdgroup]],
                           uint sg [[simdgroup_index_in_threadgroup]],
                           uint nsg [[simdgroups_per_threadgroup]],
                           uint width [[threads_per_simdgroup]]) {
    using namespace msm;
    threadgroup atomic_uint counters[MAX_LOW];
    threadgroup uint sg_tot[33];

    const uint ntop = 1u << p.top_bits;
    const uint t = gid % ntop, w = gid / ntop, win = p.win0 + w;
    const uint nlow = 1u << p.low_bits;
    device uint *row = hist + (size_t)win * (1u << p.bits) + (t << p.low_bits);
    const uint base = row[0], len = row[1];

    for (uint j = tid; j < nlow; j += tpg) atomic_store_explicit(&counters[j], 0u, memory_order_relaxed);
    // every thread has read (base, len) before the row is written below
    threadgroup_barrier(mem_flags::mem_threadgroup | mem_flags::mem_device);

    device const uint2 *src = temps + (size_t)w * p.stride + base;
    for (uint i = tid; i < len; i += tpg)
        atomic_fetch_add_explicit(&counters[src[i].x & (nlow - 1)], 1u, memory_order_relaxed);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // inclusive prefix sums of the counters, plus base: the end of each bucket
    const uint chunk = (nlow + tpg - 1) / tpg;
    const uint lo = min(nlow, tid * chunk), hi = min(nlow, lo + chunk);
    uint sum = 0;
    for (uint j = lo; j < hi; j++) sum += atomic_load_explicit(&counters[j], memory_order_relaxed);
    uint total;
    uint run = group_exclusive_sum(sum, sg_tot, lane, sg, nsg, width, total) + base;
    for (uint j = lo; j < hi; j++) {
        run += atomic_load_explicit(&counters[j], memory_order_relaxed);
        atomic_store_explicit(&counters[j], run, memory_order_relaxed);
        row[j] = run;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    device uint *dst = digits + (size_t)win * p.stride;
    for (uint i = tid; i < len; i += tpg) {
        uint2 val = src[i];
        uint idx = atomic_fetch_sub_explicit(&counters[val.x & (nlow - 1)], 1u, memory_order_relaxed) - 1;
        dst[idx] = val.y;
    }
}

// ---------------------------------------------------------------------------
// sppark `batch_addition`: the bucket of digit 1 in window 0 (the first
// `hist[0]` sorted entries of row 0), summed by the whole grid, then reduced
// in runs of 32 lanes. The thread whose grid index is a multiple of 32 writes
// one partial sum, so every one of the `threads / 32` records is written at
// every run.

namespace msm {

MONT_INLINE Fp shuffle_down(Fp a, ushort delta) {
    Fp r;
#pragma unroll
    for (int i = 0; i < 12; i++) r.l[i] = simd_shuffle_down(a.l[i], delta);
    return r;
}

MONT_INLINE g1::Xyzz shuffle_down(g1::Xyzz a, ushort delta) {
    g1::Xyzz r;
    r.X = shuffle_down(a.X, delta);
    r.Y = shuffle_down(a.Y, delta);
    r.ZZZ = shuffle_down(a.ZZZ, delta);
    r.ZZ = shuffle_down(a.ZZ, delta);
    return r;
}

} // namespace msm

kernel void msm_ones(device g1::Xyzz *ones [[buffer(0)]],
                     device const g1::Affine *points [[buffer(1)]],
                     device const uint *digits [[buffer(2)]],
                     device const uint *hist [[buffer(3)]],
                     uint tid [[thread_position_in_grid]],
                     uint nthreads [[threads_per_grid]],
                     uint lane [[thread_index_in_simdgroup]]) {
    using namespace msm;
    const uint ndigits = hist[0];

    g1::Xyzz acc = g1::inf();
    for (uint i = tid; i < ndigits; i += nthreads) {
        uint digit = digits[i];
        g1::add(acc, points[digit & 0x7fffffff], (digit >> 31) != 0);
    }

    // reduce each run of 32 lanes into its first lane
    for (uint off = 1; off < 32;) {
        g1::Xyzz down = shuffle_down(acc, (ushort)off);
        off <<= 1;
        if ((lane & (off - 1)) == 0) g1::add(acc, down);
    }

    if ((tid & 31) == 0) ones[tid / 32] = acc;
}

// ---------------------------------------------------------------------------
// sppark `accumulate`: one thread per bucket (window y, bucket x) sums its
// sorted points with mixed additions into XYZZ. The bucket of digit 1 in
// window 0 is left to `msm_ones`.

namespace msm {
struct AccParams {
    uint nwins;
    uint bits;       // wbits - 1
    uint stride;     // digits row length
    uint hot_limit;  // the most points of one bucket (`HOT_BUCKET_LIMIT`)
};
// Threads of an `msm_accumulate` group (src/msm/pipeline.rs `ACC_GROUP`).
constant uint ACC_GROUP = 256;
} // namespace msm

using msm::ACC_GROUP;

// The length of bucket `t` (0 for the bucket left to `msm_ones`) and its
// first sorted entry.
MONT_INLINE uint bucket_len(device const uint *hist, constant msm::AccParams &p, uint t,
                            thread uint &idx) {
    const uint y = t >> p.bits, x = t & ((1u << p.bits) - 1);
    device const uint *h = hist + ((size_t)y << p.bits);
    idx = x ? h[x - 1] : 0;
    return (x == 0 && y == 0) ? 0 : h[x] - idx;
}

// The hot-bucket bound (src/msm/pipeline.rs `HOT_BUCKET_LIMIT`): one thread
// per bucket; `hot` is set when a bucket (the bucket of `msm_ones` excepted)
// holds more than `hot_limit` points. Then `msm_accumulate` writes infinity
// to every bucket without reading any point, and the host declines the call
// (it reads `hot` after the command buffer).
kernel void msm_bucket_guard(device const uint *hist [[buffer(0)]],
                             device metal::atomic_uint *hot [[buffer(1)]],
                             constant msm::AccParams &p [[buffer(2)]],
                             uint t [[thread_position_in_grid]]) {
    if (t >= (p.nwins << p.bits)) return;
    uint idx;
    if (bucket_len(hist, p, t, idx) > p.hot_limit)
        metal::atomic_store_explicit(hot, 1u, metal::memory_order_relaxed);
}

kernel void msm_accumulate(device g1::Xyzz *buckets [[buffer(0)]],
                           device const g1::Affine *points [[buffer(1)]],
                           device const uint *digits [[buffer(2)]],
                           device const uint *hist [[buffer(3)]],
                           constant msm::AccParams &p [[buffer(4)]],
                           device const uint *hot [[buffer(5)]],
                           uint g [[thread_position_in_grid]],
                           uint tid [[thread_index_in_threadgroup]],
                           uint tpg [[threads_per_threadgroup]]) {
    threadgroup uint lens[ACC_GROUP];
    threadgroup uint slot[ACC_GROUP];
    const uint total = p.nwins << p.bits;
    // the same value for every thread: the whole grid returns here, before
    // any barrier
    if (*hot != 0) {
        if (g < total) buckets[g] = g1::inf();
        return;
    }
    uint idx;
    const uint mine = g < total ? bucket_len(hist, p, g, idx) : 0;
    // the group's buckets by load, longest first: each SIMD-group takes 32
    // buckets of similar length
    lens[tid] = mine;
    metal::threadgroup_barrier(metal::mem_flags::mem_threadgroup);
    uint rank = 0;
    for (uint j = 0; j < tpg; j++) {
        uint l = lens[j];
        rank += (l > mine || (l == mine && j < tid)) ? 1u : 0u;
    }
    slot[rank] = tid;
    metal::threadgroup_barrier(metal::mem_flags::mem_threadgroup);
    const uint t = g - tid + slot[tid];
    if (t >= total) return;
    const uint y = t >> p.bits;
    uint len = bucket_len(hist, p, t, idx);

    g1::Xyzz bucket;
    if (len) {
        device const uint *digs = digits + (size_t)y * p.stride + idx;
        uint digit = *digs++;
        bucket = g1::from_affine(points[digit & 0x7fffffff]);
        g1::cneg(bucket, (digit >> 31) != 0);
        while (--len) {
            digit = *digs++;
            g1::add(bucket, points[digit & 0x7fffffff], (digit >> 31) != 0);
        }
    } else {
        bucket = g1::inf();
    }
    buckets[t] = bucket;
}

// ---------------------------------------------------------------------------
// sppark `integrate`: one threadgroup per window, each thread a contiguous
// run of `2^(wbits-1) / threads` buckets: the weighted running sum `p` and
// the plain sum `acc` of its run, written over the start of the row (records
// 2 tid and 2 tid + 1) after every thread has read its run. In the top
// window, whose digits have fewer bits, a bucket of the sort is a sub-bucket
// of `2^(wbits - lsbits)` adjacent ones and the running sum takes only whole
// buckets (`mask`). The threadgroup size is a power of two below
// `2^(wbits-1)`.

namespace msm {
struct IntParams {
    uint nwins;
    uint wbits;
    uint nbits;  // scalar bits: 255
};
} // namespace msm

kernel void msm_integrate(device g1::Xyzz *buckets [[buffer(0)]],
                          constant msm::IntParams &p [[buffer(1)]],
                          uint bid [[threadgroup_position_in_grid]],
                          uint tid [[thread_index_in_threadgroup]],
                          uint tpg [[threads_per_threadgroup]]) {
    const uint nthrbits = metal::ctz(tpg);
    device g1::Xyzz *row = buckets + ((size_t)bid << (p.wbits - 1));
    uint i = 1u << (p.wbits - 1 - nthrbits);
    device const g1::Xyzz *run = row + tid * i;

    uint mask = 0;
    if ((bid + 1) * p.wbits > p.nbits) {
        uint lsbits = p.nbits - bid * p.wbits;
        mask = (1u << (p.wbits - lsbits)) - 1;
    }

    g1::Xyzz res, acc = run[--i];
    if (i & mask)
        res = g1::inf();
    else
        res = acc;

    g1::Xyzz q = res;
    while (i--) {
        q = run[i];
        uint pc = (i & mask) ? 2 : 0;
        do {
            g1::add(q, acc);
            if (pc == 1) {
                res = q;
            } else {
                acc = q;
                if (pc == 0) q = res;
            }
        } while (++pc < 2);
    }

    metal::threadgroup_barrier(metal::mem_flags::mem_device);

    row[2 * tid] = q;
    row[2 * tid + 1] = acc;
}

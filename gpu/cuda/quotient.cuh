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

// The quotient numerator nu(X) on the extended coset, one thread per point (grid stride),
// and the element-wise kernels of the coset transforms and the division.
//
// The job is the one midnight-proofs builds from its flat evaluators (gpu::QuotientJob):
// the gates program, the permutation terms, the LogUp terms of each lookup, the trash
// terms, each step `value = value * y + term`. Field arithmetic is exact, so every output
// element equals the CPU value bit for bit. Program intermediates live in a global scratch
// area, slot-major: scratch[slot * stride + thread]. Every pointer of a job is a device
// pointer (the host packs the tables into one device arena).
#pragma once

// Loads with 16-byte alignment.
#ifdef __CUDA_ARCH__
__device__ __forceinline__ fr_t ldf(const fr_t* p)
{
    const uint4* q = reinterpret_cast<const uint4*>(p);
    uint4 a = q[0], b = q[1];
    fr_t r;
    r[0] = a.x; r[1] = a.y; r[2] = a.z; r[3] = a.w;
    r[4] = b.x; r[5] = b.y; r[6] = b.z; r[7] = b.w;
    return r;
}
#endif

#ifdef __CUDA_ARCH__
__device__ __forceinline__ void stf(fr_t* p, const fr_t& v)
{
    uint4* q = reinterpret_cast<uint4*>(p);
    q[0] = make_uint4(v[0], v[1], v[2], v[3]);
    q[1] = make_uint4(v[4], v[5], v[6], v[7]);
}
#endif

// A field element passed by value to a kernel (host and device fr_t differ in alignment).
struct F8 { uint32_t v[8]; };
#ifdef __CUDA_ARCH__
__device__ __forceinline__ fr_t f8(const F8& a)
{
    fr_t r;
    for (int i = 0; i < 8; i++) r[i] = a.v[i];
    return r;
}
#endif

__global__ void mgpu_distribute_zeta(fr_t* a, size_t n, F8 z1_, F8 z2_)
{
#ifdef __CUDA_ARCH__
    const fr_t z1 = f8(z1_), z2 = f8(z2_);
    for (size_t i = blockIdx.x * (size_t)blockDim.x + threadIdx.x; i < n;
         i += (size_t)gridDim.x * blockDim.x) {
        uint32_t r = i % 3;
        if (r == 1) stf(&a[i], ldf(&a[i]) * z1);
        else if (r == 2) stf(&a[i], ldf(&a[i]) * z2);
    }
#endif
}

__global__ void mgpu_scale(fr_t* a, size_t n, F8 c_)
{
#ifdef __CUDA_ARCH__
    const fr_t c = f8(c_);
    for (size_t i = blockIdx.x * (size_t)blockDim.x + threadIdx.x; i < n;
         i += (size_t)gridDim.x * blockDim.x)
        stf(&a[i], ldf(&a[i]) * c);
#endif
}

__global__ void mgpu_mul_periodic(fr_t* a, size_t n, const fr_t* t, size_t tn)
{
#ifdef __CUDA_ARCH__
    for (size_t i = blockIdx.x * (size_t)blockDim.x + threadIdx.x; i < n;
         i += (size_t)gridDim.x * blockDim.x)
        stf(&a[i], ldf(&a[i]) * ldf(&t[i % tn]));
#endif
}

// Program operands: (tag << 30) | index (midnight_proofs::gpu::operand).
#define MGPU_TAG_UNIFORM 0u
#define MGPU_TAG_READ 1u
#define MGPU_INDEX_MASK ((1u << 30) - 1)
// Column kinds (midnight_proofs::gpu::COLUMN_*).
#define MGPU_COL_FIXED 0u
#define MGPU_COL_ADVICE 1u

struct DOp { uint32_t kind, dst, a, b, c; };
struct DRead { uint32_t kind, column; int32_t rotation; };

// A program: every pointer is a device pointer.
struct DProgram {
    uint64_t ops, reads, uniforms, outputs;
    uint32_t nops, nreads, noutputs, pad;
};

struct DLookup {
    uint64_t aggregator, multiplicities, helpers, programs;  // helpers: nchunks pointers
    uint32_t nchunks, pad;
};

struct DTrash {
    uint64_t trash;
    DProgram program;
    uint32_t selector, pad;
};

// The kernel argument (by value). Polynomials are extended cosets of n = 2^ext_k values.
struct DJob {
    uint64_t out, n, stride, scratch;
    uint64_t fixed, advice, instance;              // pointer tables
    uint64_t l0, l_last, l_active;
    uint64_t perm_sigma, perm_products, perm_kind, perm_index;
    uint64_t lookups, trash;
    uint32_t perm_ncolumns, perm_nsets, perm_chunk_len;
    int32_t perm_last_rotation;
    uint32_t nlookups, ntrash, log_scale, pad;
    DProgram gates;
    F8 y, beta, gamma, delta_start, delta, extended_omega;
};

#ifdef __CUDA_ARCH__
template <class T> __device__ __forceinline__ const T* dp(uint64_t p) { return reinterpret_cast<const T*>(p); }

__device__ __forceinline__ size_t q_rot(size_t idx, int32_t rot, uint32_t log_scale, uint64_t n)
{
    int64_t r = (int64_t)idx + ((int64_t)rot << log_scale);
    r %= (int64_t)n;
    if (r < 0) r += n;
    return (size_t)r;
}

__device__ __forceinline__ const fr_t* q_column(const DJob& J, uint32_t kind, uint32_t c)
{
    const uint64_t* t = dp<uint64_t>(kind == MGPU_COL_FIXED ? J.fixed
                                     : kind == MGPU_COL_ADVICE ? J.advice : J.instance);
    return dp<fr_t>(t[c]);
}

__device__ __forceinline__ fr_t q_operand(const DJob& J, const DProgram& p, uint32_t o, size_t idx,
                                          size_t tid)
{
    const uint32_t i = o & MGPU_INDEX_MASK;
    switch (o >> 30) {
    case MGPU_TAG_UNIFORM: return ldf(&dp<fr_t>(p.uniforms)[i]);
    case MGPU_TAG_READ: {
        const DRead r = dp<DRead>(p.reads)[i];
        return ldf(&q_column(J, r.kind, r.column)[q_rot(idx, r.rotation, J.log_scale, J.n)]);
    }
    default: return ldf(&dp<fr_t>(J.scratch)[(size_t)i * J.stride + tid]);
    }
}

// Runs a program for row idx; writes its first noutputs (at most 4) outputs.
__device__ void q_program(const DJob& J, const DProgram& p, size_t idx, size_t tid, fr_t* out)
{
    fr_t* scratch = reinterpret_cast<fr_t*>(J.scratch);
    const DOp* ops = dp<DOp>(p.ops);
    for (uint32_t k = 0; k < p.nops; k++) {
        const DOp op = ops[k];
        fr_t a = q_operand(J, p, op.a, idx, tid);
        fr_t v;
        switch (op.kind) {
        case 0: v = a + q_operand(J, p, op.b, idx, tid); break;
        case 1: v = a - q_operand(J, p, op.b, idx, tid); break;
        case 2: v = a * q_operand(J, p, op.b, idx, tid); break;
        case 3: v = a * a; break;
        case 4: v = a + a; break;
        case 5: v = -a; break;
        default: v = a * q_operand(J, p, op.b, idx, tid) + q_operand(J, p, op.c, idx, tid); break;
        }
        stf(&scratch[(size_t)op.dst * J.stride + tid], v);
    }
    const uint32_t* outs = dp<uint32_t>(p.outputs);
    for (uint32_t k = 0; k < p.noutputs && k < 4; k++) out[k] = q_operand(J, p, outs[k], idx, tid);
}

__device__ fr_t q_pow(fr_t b, uint64_t e)
{
    fr_t r = fr_t::one();
    while (e) {
        if (e & 1) r = r * b;
        b = b * b;
        e >>= 1;
    }
    return r;
}
#endif

__global__ void mgpu_quotient_kernel(const DJob J)
{
#ifdef __CUDA_ARCH__
    const size_t tid = blockIdx.x * (size_t)blockDim.x + threadIdx.x;
    const fr_t one = fr_t::one();
    const fr_t y = f8(J.y), beta = f8(J.beta), gamma = f8(J.gamma);
    const fr_t delta_start = f8(J.delta_start), delta = f8(J.delta), ext_omega = f8(J.extended_omega);
    const fr_t* l0p = dp<fr_t>(J.l0);
    const fr_t* llp = dp<fr_t>(J.l_last);
    const fr_t* lap = dp<fr_t>(J.l_active);
    fr_t* out = reinterpret_cast<fr_t*>(J.out);
    fr_t o[4];
    for (size_t idx = tid; idx < J.n; idx += J.stride) {
        q_program(J, J.gates, idx, tid, o);
        fr_t value = o[0];
        const fr_t l0 = ldf(&l0p[idx]), l_last = ldf(&llp[idx]), l_active = ldf(&lap[idx]);
        const size_t r_next = q_rot(idx, 1, J.log_scale, J.n);

        // Permutation.
        if (J.perm_nsets) {
            const uint64_t* zs = dp<uint64_t>(J.perm_products);
            const uint64_t* sig = dp<uint64_t>(J.perm_sigma);
            const uint32_t* kind = dp<uint32_t>(J.perm_kind);
            const uint32_t* col = dp<uint32_t>(J.perm_index);
            const size_t r_last = q_rot(idx, J.perm_last_rotation, J.log_scale, J.n);
            const fr_t* first = dp<fr_t>(zs[0]);
            const fr_t* last = dp<fr_t>(zs[J.perm_nsets - 1]);
            value = value * y + ((one - ldf(&first[idx])) * l0);
            const fr_t zl = ldf(&last[idx]);
            value = value * y + ((zl * zl - zl) * l_last);
            for (uint32_t s = 1; s < J.perm_nsets; s++)
                value = value * y + ((ldf(&dp<fr_t>(zs[s])[idx]) - ldf(&dp<fr_t>(zs[s - 1])[r_last])) * l0);
            fr_t current_delta = delta_start * q_pow(ext_omega, idx);
            for (uint32_t s = 0; s < J.perm_nsets; s++) {
                const fr_t* z = dp<fr_t>(zs[s]);
                const uint32_t c0 = s * J.perm_chunk_len;
                const uint32_t c1 = min(c0 + J.perm_chunk_len, J.perm_ncolumns);
                fr_t left = ldf(&z[r_next]);
                for (uint32_t c = c0; c < c1; c++)
                    left = left * (ldf(&q_column(J, kind[c], col[c])[idx]) + beta * ldf(&dp<fr_t>(sig[c])[idx]) + gamma);
                fr_t right = ldf(&z[idx]);
                for (uint32_t c = c0; c < c1; c++) {
                    right = right * (ldf(&q_column(J, kind[c], col[c])[idx]) + current_delta + gamma);
                    current_delta = current_delta * delta;
                }
                value = value * y + ((left - right) * l_active);
            }
        }

        // Lookups (LogUp).
        const DLookup* lks = dp<DLookup>(J.lookups);
        for (uint32_t li = 0; li < J.nlookups; li++) {
            const DLookup L = lks[li];
            const fr_t* agg = dp<fr_t>(L.aggregator);
            const uint64_t* helpers = dp<uint64_t>(L.helpers);
            const DProgram* progs = dp<DProgram>(L.programs);
            value = value * y + ldf(&agg[idx]) * (l0 + l_last);
            fr_t sum_helpers = fr_t::one(1), table = fr_t::one(1), selector = fr_t::one(1);
            for (uint32_t fi = 0; fi < L.nchunks; fi++) {
                q_program(J, progs[fi], idx, tid, o);
                if (fi == 0) {
                    table = o[2];
                    selector = o[3];
                }
                const fr_t h = ldf(&dp<fr_t>(helpers[fi])[idx]);
                value = value * y + h * o[1] - o[0];
                sum_helpers = sum_helpers + h;
            }
            value = value * y
                    + l_active * ((ldf(&agg[r_next]) - ldf(&agg[idx]) - selector * sum_helpers) * table
                                  + ldf(&dp<fr_t>(L.multiplicities)[idx]));
        }

        // Trash arguments.
        const DTrash* ts = dp<DTrash>(J.trash);
        for (uint32_t ti = 0; ti < J.ntrash; ti++) {
            const DTrash T = ts[ti];
            q_program(J, T.program, idx, tid, o);
            const fr_t q = ldf(&q_column(J, MGPU_COL_FIXED, T.selector)[idx]);
            value = value * y + (o[0] - (one - q) * ldf(&dp<fr_t>(T.trash)[idx]));
        }

        stf(&out[idx], value);
    }
#endif
}

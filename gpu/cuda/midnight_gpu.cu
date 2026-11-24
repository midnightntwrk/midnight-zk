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

// midnight-gpu CUDA core: BLS12-381 G1 MSM and scalar-field NTT through the sppark
// templates (third_party/sppark, VENDORED.txt), the coset kernels and the quotient
// kernel (quotient.cuh). Host types follow blst: Fr is 4 x u64 Montgomery (R = 2^256),
// a G1 Jacobian point is blst_p1 (X, Y, Z in Fp Montgomery, R = 2^384), an affine
// point is blst_p1_affine.
#include <cuda.h>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <mutex>
#include <map>
#include <stdexcept>

#include <cuda_runtime.h>
#include <atomic>
#include <mutex>
#include <unordered_map>
#include <vector>
#include <chrono>
#include <thread>

// ------------------------------------------------------------- zero before free
// sppark allocates and frees its own device buffers: the per-call MSM buffer (scalars,
// digits, sort temporaries) and the blob of an MSM context (bucket sums and digit
// histograms of the last MSM, then the base points). Both hold witness-dependent values.
// In this translation unit the four CUDA allocation calls are therefore names of the
// wrappers below: an allocation records its size; a free zeroes the block, confirms the
// zeroing is complete (device or stream synchronisation, and in check mode a count of its
// non-zero words on the device), and only then frees it and confirms the free. A block whose
// zeroing, check or free fails is not freed: it is kept in the quarantine below with its record
// and its live bytes, an erasure failure is counted (g_erase_fail, sticky), and
// mgpu_quarantine_retry (end of a request) zeroes and frees it later. The wrappers never return
// an error to sppark, whose CUDA_OK would throw (inside a destructor: terminate). sppark is
// compiled with these names and the small patches listed in third_party/sppark/PATCHES.md. The
// buffers the Rust side owns (mgpu_dev_alloc) use the plain calls; the Rust side zeroes those
// that held witness values.
static inline cudaError_t raw_malloc(void** p, size_t n) { return cudaMalloc(p, n); }
static inline cudaError_t raw_malloc_async(void** p, size_t n, cudaStream_t s) { return cudaMallocAsync(p, n, s); }
static inline cudaError_t raw_free(void* p) { return cudaFree(p); }
static inline cudaError_t raw_free_async(void* p, cudaStream_t s) { return cudaFreeAsync(p, s); }

static std::mutex g_wipe_mu;
static std::unordered_map<void*, size_t> g_wipe_sizes;
// sppark blocks whose zeroing, check or free failed: kept, never handed back with their values,
// until mgpu_quarantine_retry zeroes and frees them. Under g_wipe_mu. Each entry says whether its
// zeroing was confirmed: an unconfirmed entry may still hold witness-dependent values (pending,
// mgpu_quarantine_pending); a confirmed one only waits for its free.
struct quar_t { void* p; size_t n; bool erased; };
static std::vector<quar_t> g_quar;
// Zeroings whose pre-zeroing device synchronisation failed (the memset was still attempted; the
// block was not counted as erased). Sticky, never reset.
static std::atomic<uint64_t> g_wipe_presync_fail{0};
// The allocations of the calling thread while it builds an MSM context, so a constructor that
// throws after its blob allocation frees (and uncounts) what it made.
static thread_local std::vector<void*>* g_track = nullptr;

// Live device bytes of this translation unit, counted at every allocation and at every free
// once the free has completed (a stream-ordered free is counted after the stream synchronised
// past it): sppark's own buffers (through the wrappers below), the Rust side's buffers
// (mgpu_dev_alloc / mgpu_dev_free) and the helpers here. Host memory only, no CUDA call.
static std::unordered_map<void*, size_t> g_live_sizes;
static std::atomic<uint64_t> g_dev_live{0};
static std::atomic<uint64_t> g_dev_peak{0};

static void live_note(void* p, size_t n)
{
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        g_live_sizes[p] = n;
    }
    uint64_t c = g_dev_live.fetch_add(n) + n;
    uint64_t pk = g_dev_peak.load();
    while (c > pk && !g_dev_peak.compare_exchange_weak(pk, c)) {}
}

static void live_take(void* p)
{
    size_t n = 0;
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        auto it = g_live_sizes.find(p);
        if (it == g_live_sizes.end()) return;
        n = it->second;
        g_live_sizes.erase(it);
    }
    g_dev_live.fetch_sub(n);
}

// Erasure or release failures since process start (never reset): a failed zeroing, a
// zeroed region with a non-zero word in check mode, a failed cudaFree or cudaFreeHost.
static std::atomic<uint64_t> g_erase_fail{0};
// blocks zeroed, their bytes, blocks checked on the device, blocks with a non-zero word, failed calls
static std::atomic<uint64_t> g_wipe[5];
static std::atomic<int> g_wipe_check{0};
// page-locked bounce buffers (staging, below) zeroed, their bytes, of them read back, of them
// with a non-zero byte
#ifndef __CUDA_ARCH__
static std::atomic<uint64_t> g_stage_wipe[4];
#endif

static void wipe_note(void* p, size_t n)
{
    std::lock_guard<std::mutex> g(g_wipe_mu);
    g_wipe_sizes[p] = n;
}

// The recorded size of a block (0: not one of the wrappers' blocks). The record stays until the
// block is freed.
static size_t wipe_peek(void* p)
{
    std::lock_guard<std::mutex> g(g_wipe_mu);
    auto it = g_wipe_sizes.find(p);
    return it == g_wipe_sizes.end() ? 0 : it->second;
}

static void wipe_forget(void* p)
{
    std::lock_guard<std::mutex> g(g_wipe_mu);
    g_wipe_sizes.erase(p);
}

// Zeroes host memory; the write stays (the compiler must assume the memory is read here).
static void host_zero(void* p, size_t n)
{
    if (!p || !n) return;
    memset(p, 0, n);
    __asm__ __volatile__("" : : "r"(p) : "memory");
}

// Counts the non-zero 64-bit words (and tail bytes) of a device region into *out. A thread
// adds to *out only when its share has a non-zero word, so a zeroed region costs no atomics.
__global__ void mgpu_count_nonzero(const unsigned char* p, size_t n, unsigned long long* out)
{
    size_t stride = (size_t)gridDim.x * blockDim.x;
    size_t i0 = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    unsigned long long c = 0;
    size_t head = 0;
    if (((uintptr_t)p & 7) == 0) {
        const unsigned long long* w = (const unsigned long long*)p;
        size_t words = n / 8;
        for (size_t i = i0; i < words; i += stride) c += w[i] != 0;
        head = words * 8;
    }
    for (size_t i = head + i0; i < n; i += stride) c += p[i] != 0;
    if (c) atomicAdd(out, c);
}

__device__ unsigned long long g_nonzero_count;
static std::mutex g_nonzero_mu;

// Counts the non-zero words of n bytes at device pointer p on the device; only the count
// comes back to the host. 0 on success, -1 on a CUDA error.
static int dev_count_nonzero(const void* p, size_t n, unsigned long long* count)
{
    std::lock_guard<std::mutex> g(g_nonzero_mu);
    const unsigned long long zero = 0;
    *count = 0;
    if (cudaMemcpyToSymbol(g_nonzero_count, &zero, sizeof zero) != cudaSuccess) {
        (void)cudaGetLastError();
        return -1;
    }
    if (!n) return 0;
    unsigned long long* d = nullptr;
    if (cudaGetSymbolAddress((void**)&d, g_nonzero_count) != cudaSuccess) {
        (void)cudaGetLastError();
        return -1;
    }
    size_t words = (n + 7) / 8;
    size_t want = (words + 255) / 256;
    unsigned blocks = (unsigned)(want < 4096 ? want : 4096);
    mgpu_count_nonzero<<<blocks, 256>>>((const unsigned char*)p, n, d);
    if (cudaGetLastError() != cudaSuccess || cudaDeviceSynchronize() != cudaSuccess ||
        cudaMemcpyFromSymbol(count, g_nonzero_count, sizeof *count) != cudaSuccess) {
        (void)cudaGetLastError();
        return -1;
    }
    return 0;
}

// Counts the non-zero words of a device region on the device (see dev_count_nonzero).
extern "C" int mgpu_dev_nonzero(const void* p, size_t bytes, uint64_t* count)
{
    unsigned long long c = 0;
    int rc = dev_count_nonzero(p, bytes, &c);
    *count = c;
    return rc;
}

// 1 when n bytes at device pointer p are zero, 0 when not, -1 on a CUDA error.
static int wipe_reads_zero(const void* p, size_t n)
{
    unsigned long long c;
    if (dev_count_nonzero(p, n, &c) != 0) return -1;
    return c == 0 ? 1 : 0;
}

#ifdef MGPU_TEST_FAULT
// Test only (feature test-fault, Rust `fault::fail_lib_wipes`): the next N zeroings of sppark
// blocks fail, as a failed memset would. Not compiled into other builds.
static std::atomic<int> g_fail_lib_wipes{0};
extern "C" void mgpu_test_fail_lib_wipes(int n) { g_fail_lib_wipes = n; }
// Test only (feature test-fault, Rust `fault::fail_dev_frees`): the next N frees of the
// Rust side's buffers in mgpu_dev_free fail without freeing (and without uncounting the
// live bytes), as a failed cudaFree would.
static std::atomic<int> g_fail_dev_frees{0};
extern "C" void mgpu_test_fail_dev_frees(int n) { g_fail_dev_frees = n; }
// Test only (feature test-fault, Rust `fault::fail_wipe_presync`): the next N pre-zeroing
// device synchronisations in wipe_block count as failed. The synchronisation itself still
// runs; only its result is treated as failed.
static std::atomic<int> g_fail_wipe_presync{0};
extern "C" void mgpu_test_fail_wipe_presync(int n) { g_fail_wipe_presync = n; }
// Test only (feature test-fault, Rust `fault::fail_lib_frees`): the next N frees in
// wipe_release after a confirmed zeroing count as failed without freeing, as a failed
// cudaFree would.
static std::atomic<int> g_fail_lib_frees{0};
extern "C" void mgpu_test_fail_lib_frees(int n) { g_fail_lib_frees = n; }
#endif

// Zeroes n bytes at p and confirms it: on stream s (async) or on the device (sync), then a
// synchronisation, then in check mode a count of the non-zero words on the device. Counted.
// false: the zeroing, the synchronisation or the check failed (the block must not be freed).
static bool wipe_block(void* p, size_t n, cudaStream_t s, bool async)
{
#ifdef MGPU_TEST_FAULT
    if (g_fail_lib_wipes.load() > 0) {
        g_fail_lib_wipes--;
        g_wipe[4]++;
        return false;
    }
#endif
    // the block may still be in use by work on any stream (sppark's error path frees its
    // per-call buffer while unwinding, before it synchronises): wait for all of it, then zero.
    // A failed wait does not skip the zeroing: the memset is still attempted (it can succeed
    // after an error that is not sticky), but the block is not reported erased (work still in
    // flight may write it after the memset), so the caller keeps it as pending.
    cudaError_t pre = cudaDeviceSynchronize();
#ifdef MGPU_TEST_FAULT
    // Test only: the synchronisation above ran; only its result counts as failed, so
    // the memset below is still attempted and the block stays unconfirmed.
    if (pre == cudaSuccess && g_fail_wipe_presync.load() > 0) {
        g_fail_wipe_presync--;
        pre = cudaErrorInvalidValue;
    }
#endif
    if (pre != cudaSuccess) {
        (void)cudaGetLastError();
        g_wipe_presync_fail++;
    }
    cudaError_t e = async ? cudaMemsetAsync(p, 0, n, s) : cudaMemset(p, 0, n);
    if (e == cudaSuccess) e = async ? cudaStreamSynchronize(s) : cudaDeviceSynchronize();
    if (e != cudaSuccess || pre != cudaSuccess) {
        (void)cudaGetLastError();
        g_wipe[4]++;
        return false;
    }
    g_wipe[0]++;
    g_wipe[1] += n;
    if (g_wipe_check.load()) {
        int z = wipe_reads_zero(p, n);
        if (z < 0) {
            g_wipe[4]++;
            return false;
        }
        g_wipe[2]++;
        if (!z) {
            g_wipe[3]++;
            return false;
        }
    }
    return true;
}

// Keeps a block whose erasure or release failed (record and live bytes stay); counts the failure.
// Idempotent: a block already in quarantine is neither added nor counted again (a failed wipe
// in wipe_release followed by a throwing teardown reaches here twice for one block; a second
// entry would let mgpu_quarantine_retry zero and free a reused address). true: newly kept.
// A block already held loses its confirmed zeroing (a later failure may follow a confirmed one).
static bool quarantine_block(void* p, size_t n)
{
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        for (auto& b : g_quar)
            if (b.p == p) {
                b.erased = false;
                return false;
            }
        g_quar.push_back(quar_t{p, n, false});
    }
    g_erase_fail++;
    return true;
}

// A block whose zeroing was confirmed but whose free failed: kept for the free only, not pending
// (unless it is also held unerased). Idempotent as quarantine_block.
static bool quarantine_erased(void* p, size_t n)
{
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        for (auto& b : g_quar)
            if (b.p == p) return false;
        g_quar.push_back(quar_t{p, n, true});
    }
    g_erase_fail++;
    return true;
}

static bool quarantined_block(void* p)
{
    std::lock_guard<std::mutex> g(g_wipe_mu);
    for (auto& b : g_quar)
        if (b.p == p) return true;
    return false;
}

static inline cudaError_t wipe_malloc(void** p, size_t n)
{
    cudaError_t e = raw_malloc(p, n);
    if (e == cudaSuccess) {
        wipe_note(*p, n);
        live_note(*p, n);
        if (g_track) g_track->push_back(*p);
    }
    return e;
}

static inline cudaError_t wipe_malloc_async(void** p, size_t n, cudaStream_t s)
{
    cudaError_t e = raw_malloc_async(p, n, s);
    if (e == cudaSuccess) {
        wipe_note(*p, n);
        live_note(*p, n);
        if (g_track) g_track->push_back(*p);
    }
    return e;
}

// The free of both wrappers: zero, confirm, free, confirm the free, then forget the record and
// the live bytes. Any failure keeps the block (quarantine) and counts an erasure failure; the
// return is cudaSuccess either way (see the section comment). A pointer the wrappers did not
// allocate is freed as before.
static cudaError_t wipe_release(void* p, cudaStream_t s, bool async)
{
    if (!p) return cudaSuccess;
    size_t n = wipe_peek(p);
    if (!n) return async ? raw_free_async(p, s) : raw_free(p);
    if (!wipe_block(p, n, s, async)) {
        quarantine_block(p, n);
        return cudaSuccess;
    }
#ifdef MGPU_TEST_FAULT
    // Test only: count the free as failed without freeing (the zeroing above was
    // confirmed, so the branch below keeps the block as zeroed but unfreed).
    bool fail_free = g_fail_lib_frees.load() > 0;
    if (fail_free) g_fail_lib_frees--;
    cudaError_t e = fail_free ? cudaErrorInvalidValue
                              : (async ? raw_free_async(p, s) : raw_free(p));
#else
    cudaError_t e = async ? raw_free_async(p, s) : raw_free(p);
#endif
    if (e != cudaSuccess) {
        // zeroed but not released: kept for a retry of the release
        (void)cudaGetLastError();
        g_wipe[4]++;
        quarantine_erased(p, n);
        return cudaSuccess;
    }
    if (async && cudaStreamSynchronize(s) != cudaSuccess) {
        // zeroed and the free is enqueued, but its completion is not confirmed: the bytes stay
        // counted as live and an erasure failure is counted
        (void)cudaGetLastError();
        g_wipe[4]++;
        g_erase_fail++;
        wipe_forget(p);
        return cudaSuccess;
    }
    wipe_forget(p);
    live_take(p);
    return cudaSuccess;
}

static inline cudaError_t wipe_free(void* p) { return wipe_release(p, nullptr, false); }

static inline cudaError_t wipe_free_async(void* p, cudaStream_t s) { return wipe_release(p, s, true); }

// sppark patch hook (pippenger.cuh, ~msm_t): the teardown of an MSM context threw before its
// blob was released; the blob is kept in quarantine.
static void mgpu_msm_teardown_failed(void* p)
{
    (void)cudaGetLastError();
    // the release may already have kept it (a failed wipe, then a throwing sync)
    if (quarantined_block(p)) return;
    size_t n = wipe_peek(p);
    if (n) quarantine_block(p, n);
    else g_erase_fail++;
}
#define SPPARK_MSM_TEARDOWN_FAILED(p) mgpu_msm_teardown_failed((void*)(p))
// sppark patch hook (pippenger.cuh, msm_t::invoke): a host copy of bucket rows read back from
// the device, counted as a device-to-host copy.
static void mgpu_note_lib_dtoh(size_t n);
#define SPPARK_NOTE_DTOH(n) mgpu_note_lib_dtoh(n)
// sppark patch hook (pippenger.cuh, msm_t::invoke): an error arm could not confirm every stream;
// the patch keeps (leaks) the host vectors a copy may still target, and it is counted as an
// unconfirmed drain (mgpu_drain_counters).
static void mgpu_msm_undrained();
#define SPPARK_MSM_UNDRAINED() mgpu_msm_undrained()
#ifdef MGPU_TEST_FAULT
// Test only (Rust `fault::msm_throw_next`): the next pass through invoke's test point throws a
// non-CUDA exception with the bucket-row copies still enqueued.
static std::atomic<int> g_test_msm_throw{0};
extern "C" void mgpu_test_msm_throw(int n) { g_test_msm_throw = n; }
static void mgpu_msm_test_point()
{
    int n = g_test_msm_throw.load();
    while (n > 0 && !g_test_msm_throw.compare_exchange_weak(n, n - 1)) {}
    if (n > 0) throw std::runtime_error("injected msm exception (test)");
}
#define SPPARK_MSM_TEST_POINT() mgpu_msm_test_point()
// Test only (Rust `fault::msm_worker_throw_next`): the next pass of a collect worker throws.
static std::atomic<int> g_test_worker_throw{0};
extern "C" void mgpu_test_msm_worker_throw(int n) { g_test_worker_throw = n; }
static void mgpu_msm_test_worker()
{
    int n = g_test_worker_throw.load();
    while (n > 0 && !g_test_worker_throw.compare_exchange_weak(n, n - 1)) {}
    if (n > 0) throw std::runtime_error("injected collect worker exception (test)");
}
#define SPPARK_MSM_TEST_WORKER() mgpu_msm_test_worker()
#endif

#define cudaMalloc(p, n) wipe_malloc((void**)(p), (n))
#define cudaMallocAsync(p, n, s) wipe_malloc_async((void**)(p), (n), (s))
#define cudaFree(p) wipe_free((void*)(p))
#define cudaFreeAsync(p, s) wipe_free_async((void*)(p), (s))

#include <ff/bls12-381.hpp>
#include <ec/jacobian_t.hpp>
#include <ec/xyzz_t.hpp>

typedef jacobian_t<fp_t> point_t;
typedef xyzz_t<fp_t> bucket_t;
typedef bucket_t::affine_t affine_t;
typedef fr_t scalar_t;

#include <util/all_gpus.cpp>
#include <msm/pippenger.cuh>
#include <ntt/ntt.cuh>

#include "quotient.cuh"

#ifdef MGPU_TEST_FAULT
// Test only: spins for `cycles` clock cycles, so work stays queued on a stream while an error
// arm runs (see test_fail_arm).
__global__ void mgpu_test_spin(long long cycles)
{
    long long t0 = clock64();
    while (clock64() - t0 < cycles) {}
}

// Test only (actor probes): a cooperative kernel that stays resident by
// grid-syncing in a loop. `ready` is set after the first grid sync, so
// every block of the grid is resident when the host sees it. Start and
// end clock64 stamps land in stamps[2*slot], stamps[2*slot+1].
#include <cooperative_groups.h>
__global__ void mgpu_probe_coop_kernel(volatile int* ready, long long* stamps, int slot,
                                       int rounds, long long cycles)
{
    cooperative_groups::grid_group g = cooperative_groups::this_grid();
    g.sync();
    if (blockIdx.x == 0 && threadIdx.x == 0) {
        stamps[2 * slot] = clock64();
        if (ready) *ready = 1;
    }
    for (int r = 0; r < rounds; r++) {
        long long t0 = clock64();
        while (clock64() - t0 < cycles) {}
        g.sync();
    }
    if (blockIdx.x == 0 && threadIdx.x == 0) stamps[2 * slot + 1] = clock64();
}

// Test only (actor probes): touches `p` strided while spinning, so the
// block is in use for the whole spin.
__global__ void mgpu_probe_touch(char* p, size_t n, long long cycles)
{
    size_t stride = (size_t)gridDim.x * blockDim.x * 4096;
    size_t at = ((size_t)blockIdx.x * blockDim.x + threadIdx.x) * 4096 % n;
    long long t0 = clock64();
    unsigned int v = (unsigned int)p[at];
    while (clock64() - t0 < cycles) {
        p[at] = (char)(v + 1);
        at = (at + stride) % n;
        v = (unsigned int)p[at];
    }
    p[at] = (char)v;
}
#endif

#ifndef __CUDA_ARCH__
// A 32-byte value as an F8 kernel argument, copied byte for byte (no pointer cast: strict
// aliasing).
static_assert(sizeof(F8) == sizeof(fr_t), "F8 is the size of fr_t");
static inline F8 f8_of(const void* p)
{
    F8 v;
    memcpy(&v, p, sizeof v);
    return v;
}
#endif

#ifndef __CUDA_ARCH__

static thread_local char g_err[256];

static int fail(const char* what, int code)
{
    snprintf(g_err, sizeof g_err, "%s: code %d", what, code);
    return code ? code : -1;
}

// A failed RustError from sppark (built with TAKE_RESPONSIBILITY_FOR_ERROR_MESSAGE) carries a
// strdup'd message that no Rust code receives: it is copied into the last-error text and freed.
static int rust_fail(const char* what, RustError& r)
{
    if (r.message) {
        snprintf(g_err, sizeof g_err, "%s: code %d: %s", what, r.code, r.message);
        free(r.message);
        r.message = nullptr;
    } else {
        snprintf(g_err, sizeof g_err, "%s: code %d", what, r.code);
    }
    return r.code ? r.code : -1;
}

extern "C" const char* mgpu_last_error() { return g_err; }

// Error drains: [run, of them not confirmed]. Host memory only.
static std::atomic<uint64_t> g_drain[2];

// The error exit of a call that enqueued copies or kernels on stream s waits for them before it
// returns, so the caller never frees or reuses a host slice (or reads a buffer) that a transfer
// may still read or write. A stream that does not confirm is followed by a device-wide
// synchronisation; if that fails too, the drain is counted as not confirmed (mgpu_drain_counters):
// a transfer may still target the caller's memory. Never throws. true: the stream is drained.
#ifdef MGPU_TEST_FAULT
// Test only (Rust `fault`, the stage-path driver): the next N drains report "not confirmed"
// after they synchronised, as a drain whose synchronisations failed would.
static std::atomic<int> g_test_unconfirm{0};
static bool test_unconfirm()
{
    int n = g_test_unconfirm.load();
    while (n > 0 && !g_test_unconfirm.compare_exchange_weak(n, n - 1)) {}
    return n > 0;
}
// Test only: the next `n` error drains report "not confirmed" (after
// they synchronised), so a public device call whose error arm drains
// sees an unconfirmed drain.
extern "C" void mgpu_test_unconfirm_drains(int n) { g_test_unconfirm = n; }
#else
static inline bool test_unconfirm() { return false; }
#endif

static bool drain_stream(cudaStream_t s)
{
    g_drain[0]++;
    cudaError_t e = cudaStreamSynchronize(s);
    if (e != cudaSuccess) {
        (void)cudaGetLastError();
        e = cudaDeviceSynchronize();
    }
    (void)cudaGetLastError();
    if (e == cudaSuccess && test_unconfirm()) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        g_drain[1]++;
        return false;
    }
    return true;
}

// The device-wide drain of an MSM error arm (sppark's copies may be on any of its streams),
// counted as drain_stream does.
static bool drain_device()
{
    g_drain[0]++;
    cudaError_t e = cudaDeviceSynchronize();
    (void)cudaGetLastError();
    if (e == cudaSuccess && test_unconfirm()) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        g_drain[1]++;
        return false;
    }
    return true;
}

static void mgpu_msm_undrained()
{
    g_drain[0]++;
    g_drain[1]++;
}

extern "C" void mgpu_drain_counters(uint64_t out[2])
{
    out[0] = g_drain[0].load();
    out[1] = g_drain[1].load();
}

// The error arms a test can fail on purpose (test_fail_arm).
enum test_arm_t { ARM_COPY = 1, ARM_READBACK, ARM_ZETA, ARM_SCALE, ARM_PERIODIC_COPY,
                  ARM_PERIODIC_KERNEL, ARM_MSM, ARM_MSM_CTX, ARM_STAGED_COPY };
#ifdef MGPU_TEST_FAULT
// Test only: the next pass through arm `id` queues a spinning kernel on stream s (about a quarter
// of a second) and then fails as an error after async work would, so the arm's error exit runs
// with work still queued.
static std::atomic<int> g_test_arm{0};
static bool test_fail_arm(int id, cudaStream_t s)
{
    int want = id;
    if (!g_test_arm.compare_exchange_strong(want, 0)) return false;
    mgpu_test_spin<<<1, 1, 0, s>>>(1LL << 29);
    return true;
}
#else
static inline bool test_fail_arm(int, cudaStream_t) { return false; }
#endif

// Device count with cooperative launch (what sppark needs); 0 when no usable device.
extern "C" int mgpu_device_count(char* name, size_t name_len, int* sm_count,
                                     int* major, int* minor)
{
    int n = 0;
    if (cudaGetDeviceCount(&n) != cudaSuccess || n == 0)
        return 0;
    cudaDeviceProp prop;
    if (cudaGetDeviceProperties(&prop, 0) != cudaSuccess)
        return 0;
    if (name && name_len) {
        strncpy(name, prop.name, name_len - 1);
        name[name_len - 1] = 0;
    }
    if (sm_count) *sm_count = prop.multiProcessorCount;
    if (major) *major = prop.major;
    if (minor) *minor = prop.minor;
    try {
        (void)select_gpu(0);
    } catch (const cuda_error& e) {
        return 0;
    }
    return n;
}

// device 0 from its properties only, with the filter of sppark's gpus_t (compute
// capability 7.0 or more, cooperative launch). No cudaSetDevice, stream, event or allocation,
// so no CUDA context; mgpu_device_count (select_gpu) makes it at the first device operation.
// Returns the device count, 0 when device 0 is absent or not usable.
// Devices visible to the runtime (cudaGetDeviceCount only: no context is made).
extern "C" int mgpu_device_count_only()
{
    int n = 0;
    if (cudaGetDeviceCount(&n) != cudaSuccess) {
        (void)cudaGetLastError();
        return 0;
    }
    return n;
}

// Whether the primary context of device 0 is active (1), not (0), or unknown (-1), through
// the driver's cuDevicePrimaryCtxGetState, which neither makes nor retains a context. For the
// test that device detection makes no context.
extern "C" int mgpu_primary_ctx_active()
{
    typedef int (*get_state_t)(int, unsigned int*, int*);
    void* f = nullptr;
    cudaDriverEntryPointQueryResult q;
#if CUDART_VERSION >= 12050
    cudaError_t e = cudaGetDriverEntryPointByVersion("cuDevicePrimaryCtxGetState", &f, 12000,
                                                     cudaEnableDefault, &q);
#else
    cudaError_t e = cudaGetDriverEntryPoint("cuDevicePrimaryCtxGetState", &f, cudaEnableDefault, &q);
#endif
    if (e != cudaSuccess || q != cudaDriverEntryPointSuccess || !f) {
        (void)cudaGetLastError();
        return -1;
    }
    unsigned int flags = 0;
    int active = 0;
    if (((get_state_t)f)(0, &flags, &active) != 0) return -1;
    return active ? 1 : 0;
}

extern "C" void mgpu_versions(int* runtime, int* driver)
{
    // neither call makes a CUDA context
    if (cudaRuntimeGetVersion(runtime) != cudaSuccess) {
        (void)cudaGetLastError();
        *runtime = 0;
    }
    if (cudaDriverGetVersion(driver) != cudaSuccess) {
        (void)cudaGetLastError();
        *driver = 0;
    }
}

extern "C" int mgpu_probe(char* name, size_t name_len, int* sm_count, int* major,
                              int* minor, int* integrated, size_t* total)
{
    int n = 0;
    if (cudaGetDeviceCount(&n) != cudaSuccess || n == 0) {
        (void)cudaGetLastError();
        return 0;
    }
    cudaDeviceProp prop;
    if (cudaGetDeviceProperties(&prop, 0) != cudaSuccess) {
        (void)cudaGetLastError();
        return 0;
    }
    if (prop.major < 7 || !prop.cooperativeLaunch)
        return 0;
    if (name && name_len) {
        strncpy(name, prop.name, name_len - 1);
        name[name_len - 1] = 0;
    }
    if (sm_count) *sm_count = prop.multiProcessorCount;
    if (major) *major = prop.major;
    if (minor) *minor = prop.minor;
    if (integrated) *integrated = prop.integrated;
    if (total) *total = prop.totalGlobalMem;
    return n;
}

extern "C" int mgpu_mem_info(size_t* free_b, size_t* total_b)
{
    return cudaMemGetInfo(free_b, total_b) == cudaSuccess ? 0 : -1;
}

// 1 when kernels on device 0 may read pageable host memory in place at full speed: an
// integrated part with pageable access (GB10 unified memory). 0 on a discrete card, even
// with HMM (pageable access over PCIe works there but is bus-bound), and on any error.
extern "C" int mgpu_host_readable()
{
    int pageable = 0, integrated = 0;
    if (cudaDeviceGetAttribute(&pageable, cudaDevAttrPageableMemoryAccess, 0) != cudaSuccess)
        return 0;
    if (cudaDeviceGetAttribute(&integrated, cudaDevAttrIntegrated, 0) != cudaSuccess)
        return 0;
    return (pageable && integrated) ? 1 : 0;
}

// ---------------------------------------------------------------- MSM
// One-shot MSM: affine bases on the host (copied per call), Montgomery scalars.
extern "C" int mgpu_msm_g1(point_t* out, const affine_t* points, size_t npoints,
                           const scalar_t* scalars)
{
    try {
        RustError r = mult_pippenger<bucket_t>(out, points, npoints, scalars, true);
        if (r.code == cudaSuccess && test_fail_arm(ARM_MSM, select_gpu(0)))
            r.code = cudaErrorUnknown;
        if (r.code != cudaSuccess) {
            // mult_pippenger's catch returns without a sync when the context constructor threw
            // after its copy of the caller's points
            drain_device();
            return rust_fail("msm", r);
        }
    } catch (...) {
        // no exception crosses into Rust (mult_pippenger catches only cuda_error)
        drain_device();
        return fail("msm", -1);
    }
    return 0;
}

// Cached base table: the affine bases are uploaded once (SRS g or g_lagrange).
typedef msm_t<bucket_t, point_t, affine_t, scalar_t> msm_ctx_t;

// A context whose construction throws (the blob was allocated, the upload of the points failed)
// frees what it allocated (zeroed and uncounted through the wrappers), so the live bytes stay
// right. The upload is confirmed (synchronised) before the context is handed out; a failed
// confirmation deletes it.
extern "C" void* mgpu_msm_ctx_new(const affine_t* points, size_t npoints)
{
    std::vector<void*> made;
    g_track = &made;
    msm_ctx_t* c = nullptr;
    try {
        c = new msm_ctx_t(points, npoints);
    } catch (const cuda_error& e) {
        g_track = nullptr;
        // the constructor's copy of the caller's points may still run
        drain_device();
        for (void* p : made) (void)cudaFree(p);
        fail("msm_ctx_new", e.code());
        return nullptr;
    } catch (...) {
        g_track = nullptr;
        drain_device();
        for (void* p : made) (void)cudaFree(p);
        fail("msm_ctx_new", -1);
        return nullptr;
    }
    g_track = nullptr;
    try {
        select_gpu(0).sync();
    } catch (const cuda_error& e) {
        delete c;
        fail("msm_ctx_new: upload", e.code());
        return nullptr;
    }
    return c;
}

#ifdef MGPU_TEST_FAULT
// Test only: read the bucket records of an MSM context. msm_t keeps its bucket blob, window
// count and window width private; an explicit instantiation may name private members, so the
// test reads them without a change to sppark.
template<class Tag, typename Tag::type M> struct mgpu_member_t {
    friend typename Tag::type mgpu_member(Tag) { return M; }
};
struct mgpu_buckets_tag {
    typedef bucket_t::mem_t* msm_ctx_t::*type;
    friend type mgpu_member(mgpu_buckets_tag);
};
struct mgpu_wbits_tag {
    typedef uint32_t msm_ctx_t::*type;
    friend type mgpu_member(mgpu_wbits_tag);
};
struct mgpu_nwins_tag {
    typedef uint32_t msm_ctx_t::*type;
    friend type mgpu_member(mgpu_nwins_tag);
};
template struct mgpu_member_t<mgpu_buckets_tag, &msm_ctx_t::d_buckets>;
template struct mgpu_member_t<mgpu_wbits_tag, &msm_ctx_t::wbits>;
template struct mgpu_member_t<mgpu_nwins_tag, &msm_ctx_t::nwins>;

// The bucket records of ctx (the window rows, then the batch-addition results), as 64-bit
// words: with out null, returns the record count and sets *words to the words per record;
// else copies them to out (max_words words) and returns the count, -1 on an error.
extern "C" int64_t mgpu_test_ctx_buckets(void* ctx, uint64_t* out, size_t max_words,
                                         uint32_t* words)
{
    auto* m = reinterpret_cast<msm_ctx_t*>(ctx);
    size_t row = (size_t)1 << (m->*mgpu_member(mgpu_wbits_tag()) - 1);
    size_t n = (size_t)(m->*mgpu_member(mgpu_nwins_tag())) * row
             + select_gpu(0).sm_count() * BATCH_ADD_BLOCK_SIZE / WARP_SZ;
    size_t w = sizeof(bucket_t::mem_t) / sizeof(uint64_t);
    *words = (uint32_t)w;
    if (!out) return (int64_t)n;
    if (n * w > max_words) return -1;
    if (cudaDeviceSynchronize() != cudaSuccess ||
        cudaMemcpy(out, m->*mgpu_member(mgpu_buckets_tag()), n * w * sizeof(uint64_t),
                   cudaMemcpyDeviceToHost) != cudaSuccess) {
        (void)cudaGetLastError();
        return fail("test_ctx_buckets", -1);
    }
    return (int64_t)n;
}
#endif

// Deletes an MSM context. Never throws (the patched ~msm_t and the free wrappers keep a block
// whose zeroing or release failed, in quarantine). 0: the blob was zeroed, confirmed and freed;
// -1: an erasure or release failed during the teardown (counted, sticky).
extern "C" int mgpu_msm_ctx_free(void* ctx)
{
    if (!ctx) return 0;
    uint64_t before = g_erase_fail.load();
    delete reinterpret_cast<msm_ctx_t*>(ctx);
    return g_erase_fail.load() == before ? 0 : fail("msm_ctx_free: erasure", -1);
}

// Zeroes and frees the quarantined sppark blocks (end of a request; the caller holds the device
// lock). 0: none is left; -1: a block is still held.
extern "C" int mgpu_quarantine_retry()
{
    std::vector<quar_t> q;
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        q.swap(g_quar);
    }
    std::vector<quar_t> left;
    for (auto& b : q) {
        // a block keeps its erased state across a failed retry (zeroed now, or before)
        bool zeroed = wipe_block(b.p, b.n, nullptr, false);
        if (zeroed && raw_free(b.p) == cudaSuccess) {
            wipe_forget(b.p);
            live_take(b.p);
        } else {
            (void)cudaGetLastError();
            left.push_back(quar_t{b.p, b.n, b.erased || zeroed});
        }
    }
    std::lock_guard<std::mutex> g(g_wipe_mu);
    for (auto& b : left) {
        bool held = false;
        for (auto& c : g_quar)
            if (c.p == b.p) { c.erased = c.erased && b.erased; held = true; }
        if (!held) g_quar.push_back(b);
    }
    return g_quar.empty() ? 0 : -1;
}

// What is still unerased, for a retirement decision. out[0] sppark blocks in quarantine whose
// zeroing is not confirmed (may hold witness-dependent values), out[1] their bytes, out[2] blocks
// zeroed but not freed, out[3] zeroings whose pre-zeroing synchronisation failed (sticky).
// Host memory only, no CUDA call.
extern "C" void mgpu_quarantine_pending(uint64_t out[4])
{
    uint64_t blocks = 0, bytes = 0, erased = 0;
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        for (auto& b : g_quar) {
            if (b.erased) erased++;
            else { blocks++; bytes += b.n; }
        }
    }
    out[0] = blocks;
    out[1] = bytes;
    out[2] = erased;
    out[3] = g_wipe_presync_fail.load();
}

#ifdef MGPU_TEST_FAULT
// Test only: one block whose wipe fails in its release and whose teardown then throws (the
// sppark hook is called for it). out: quarantined blocks, erasure failures added. The block
// stays in quarantine for mgpu_quarantine_retry.
extern "C" int mgpu_test_double_quarantine(uint64_t out[2])
{
    void* p = nullptr;
    if (wipe_malloc(&p, 4096) != cudaSuccess) return fail("cudaMalloc", 4096);
    uint64_t f0 = g_erase_fail.load();
    g_fail_lib_wipes = 1;
    (void)wipe_free(p);
    mgpu_msm_teardown_failed(p);
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        out[0] = 0;
        for (auto& b : g_quar)
            if (b.p == p) out[0]++;
    }
    out[1] = g_erase_fail.load() - f0;
    return 0;
}
#endif

// sppark blocks in quarantine now.
extern "C" uint64_t mgpu_quarantined()
{
    std::lock_guard<std::mutex> g(g_wipe_mu);
    return g_quar.size();
}

// The bucket-row copies of sppark's MSM to the host (SPPARK_NOTE_DTOH): copies, bytes.
static std::atomic<uint64_t> g_lib_dtoh[2];
static void mgpu_note_lib_dtoh(size_t n)
{
    g_lib_dtoh[0]++;
    g_lib_dtoh[1] += n;
}
extern "C" void mgpu_lib_dtoh(uint64_t out[2])
{
    out[0] = g_lib_dtoh[0].load();
    out[1] = g_lib_dtoh[1].load();
}
extern "C" void mgpu_lib_dtoh_reset() { g_lib_dtoh[0] = 0; g_lib_dtoh[1] = 0; }

extern "C" int mgpu_msm_ctx_run(void* ctx, point_t* out, const scalar_t* scalars,
                                size_t nscalars)
{
    auto* m = reinterpret_cast<msm_ctx_t*>(ctx);
    try {
        RustError r = m->invoke(*out, (const affine_t*)nullptr, nscalars, scalars, true);
        if (r.code == cudaSuccess && test_fail_arm(ARM_MSM_CTX, select_gpu(0)))
            r.code = cudaErrorUnknown;
        if (r.code != cudaSuccess) {
            drain_device();
            return rust_fail("msm_ctx_run", r);
        }
    } catch (const cuda_error& e) {
        // a synchronisation threw: copies may still run
        drain_device();
        return fail("msm_ctx_run", e.code());
    } catch (...) {
        // no exception crosses into Rust
        drain_device();
        return fail("msm_ctx_run", -1);
    }
    return 0;
}

// Counters of the wrappers above: blocks zeroed, bytes, checked, non-zero, errors.
extern "C" void mgpu_wipe_counters(uint64_t out[5])
{
    for (int i = 0; i < 5; i++) out[i] = g_wipe[i].load();
}

// Sets the check mode of the free wrappers without touching the counters.
extern "C" void mgpu_wipe_set_check(int check) { g_wipe_check = check; }

extern "C" void mgpu_wipe_reset(int check)
{
    for (int i = 0; i < 5; i++) g_wipe[i] = 0;
    for (int i = 0; i < 4; i++) g_stage_wipe[i] = 0;
    g_wipe_check = check;
}

// ---------------------------------------------------------------- NTT
// sppark keeps NTT_internal protected; this subclass runs it on a device buffer.
struct DevNTT : public NTT {
    static void run(fr_t* d, uint32_t lg, bool inverse, stream_t& s)
    {
        // NTT_internal has no singleton case (its launchers shift by lg - 1)
        if (lg < 1 || lg > 28) CUDA_OK(cudaErrorInvalidValue);
        NTT_internal(d, lg, InputOutputOrder::NN,
                     inverse ? Direction::inverse : Direction::forward,
                     Type::standard, s);
    }
};

// Host-to-host transform in natural order. Forward: no scaling (best_fft with the
// standard 2^lg root). Inverse: omega^-1 and the 1/n scaling (EvaluationDomain::ifft).
extern "C" int mgpu_ntt(fr_t* inout, uint32_t lg, int inverse)
{
    if (lg < 1 || lg > 28) return fail("ntt: size", (int)lg);
    try {
        RustError r = NTT::Base(select_gpu(0), inout, lg, NTT::InputOutputOrder::NN,
                                inverse ? NTT::Direction::inverse : NTT::Direction::forward,
                                NTT::Type::standard);
        if (r.code != cudaSuccess)
            return rust_fail("ntt", r);
    } catch (...) {
        // select_gpu and the table build may throw outside NTT::Base's own catch; no
        // exception crosses into Rust
        drain_device();
        return fail("ntt", -1);
    }
    return 0;
}

// ------------------------------------------------- device buffers (resident polys)
extern "C" void* mgpu_dev_alloc(size_t bytes)
{
    void* p = nullptr;
    if (raw_malloc(&p, bytes) != cudaSuccess) {
        (void)cudaGetLastError();
        fail("cudaMalloc", (int)bytes);
        return nullptr;
    }
    live_note(p, bytes);
    return p;
}

// 0 when freed (or null). On a failed free the caller keeps the pointer and counts the
// failure (the Rust side's count; not counted here as well).
extern "C" int mgpu_dev_free(void* p)
{
    if (!p) return 0;
#ifdef MGPU_TEST_FAULT
    // Test only: fail without freeing and without uncounting the live bytes.
    if (g_fail_dev_frees.load() > 0) {
        g_fail_dev_frees--;
        return fail("cudaFree", (int)cudaErrorInvalidValue);
    }
#endif
    cudaError_t e = raw_free(p);
    if (e != cudaSuccess) {
        (void)cudaGetLastError();
        return fail("cudaFree", e);
    }
    live_take(p);
    return 0;
}

// Live device bytes of this translation unit now and their peak since the last reset.
extern "C" void mgpu_dev_bytes(uint64_t out[2])
{
    out[0] = g_dev_live.load();
    out[1] = g_dev_peak.load();
}

extern "C" void mgpu_dev_bytes_reset_peak() { g_dev_peak = g_dev_live.load(); }

// Erasure and release failures since process start (; never reset).
extern "C" uint64_t mgpu_erase_failures() { return g_erase_fail.load(); }

// zero a device buffer (before it is freed).
extern "C" int mgpu_dev_zero(void* p, size_t bytes)
{
    if (!p || !bytes) return 0;
    auto& gpu = select_gpu(0);
    cudaError_t e = cudaMemsetAsync(p, 0, bytes, gpu);
    if (e == cudaSuccess) e = cudaStreamSynchronize(gpu);
    return e == cudaSuccess ? 0 : fail("dev_zero", e);
}

// ------------------------------------------- page-locked staging of large copies
// The driver copies from pageable host memory through its own small page-locked buffers, at a
// third or a quarter of the rate of a copy from page-locked memory on a full-width link. A copy
// of STAGE_MIN bytes or more therefore goes through one page-locked bounce buffer of this
// translation unit: host -> (parallel memcpy) -> bounce slot -> device, or the reverse, in a
// ring of STAGE_SLOTS slots so that the memcpy of one slot runs while the bus copies another.
// The bytes that reach the device (or the host) are the bytes of the source: only the route
// changes. The buffer is allocated at the first large copy of a request and zeroed and freed by
// mgpu_stage_end (the end of the request), so nothing page-locked outlives a request.
// Witness-dependent values pass through it. Direct pageable copies are kept when the buffer
// cannot be allocated (WSL limits page-locked memory), on an integrated part (one memory: the
// bounce is a second memcpy), with MIDNIGHT_GPU_STAGE=off, and for the rest of a request when the
// first staged upload of STAGE_PROBE bytes or more measured under STAGE_SLOW_GIB_S (a bus-bound
// link: page-locked memory gains nothing there and the memcpy costs host bandwidth).
// Every staging call runs under the Rust side's GPU lock, so the state below needs no lock.
static const size_t STAGE_MIN = (size_t)16 << 20;
static const size_t STAGE_BYTES = (size_t)256 << 20;
static const size_t STAGE_SLOTS = 4;
static const size_t STAGE_PROBE = (size_t)64 << 20;
static const double STAGE_SLOW_GIB_S = 6.0;

struct Stage {
    char* buf = nullptr;
    // read without the GPU lock by mgpu_stage_counters (the stats call)
    std::atomic<size_t> bytes{0};
    cudaEvent_t ev[STAGE_SLOTS] = {};
    bool failed = false;  // the allocation failed in this request
    bool slow = false;    // this request measured a bus-bound link
    bool probed = false;  // this request's probe copy ran
    bool events = false;  // ev[] are created
    bool dead = false;    // its cudaFreeHost failed: kept for a retry, never used again
    // the unconfirmed-drain count (g_drain[1]) when the buffer was allocated; a larger count
    // means a transfer may still target the buffer (see stage_free, stage_get)
    uint64_t undrained_at = 0;
    bool held = false;    // kept after an unconfirmed drain: never wiped, freed or used again
};
static Stage g_stage;
// staged copies, their bytes, direct large copies, their bytes, failed allocations,
// allocations, bus-bound requests
static std::atomic<uint64_t> g_stage_ctr[7];
// route of this thread's last copy: 0 small (direct), 1 staged, 2 large and direct
static thread_local int g_last_route = 0;

static int stage_enabled()
{
    static int v = -1;
    if (v < 0) {
        const char* e = getenv("MIDNIGHT_GPU_STAGE");
        int integrated = 0;
        if (cudaDeviceGetAttribute(&integrated, cudaDevAttrIntegrated, 0) != cudaSuccess) {
            (void)cudaGetLastError();
            integrated = 1;
        }
        bool off = e && (!strcmp(e, "off") || !strcmp(e, "0"));
        v = (off || integrated) ? 0 : 1;
    }
    return v;
}

static size_t stage_threads()
{
    static size_t t = 0;
    if (!t) {
        const char* e = getenv("MIDNIGHT_GPU_STAGE_THREADS");
        long v = e ? atol(e) : 0;
        if (v <= 0) {
            unsigned hw = std::thread::hardware_concurrency();
            v = hw ? (hw < 8 ? hw : 8) : 4;
        }
        t = v > 64 ? 64 : (size_t)v;
    }
    return t;
}

// memcpy split over up to stage_threads() threads (parts of 4 MiB or more).
static void par_memcpy(void* d, const void* s, size_t n)
{
    size_t t = stage_threads();
    const size_t MIN_PART = (size_t)4 << 20;
    if (t > n / MIN_PART) t = n / MIN_PART;
    if (t <= 1) {
        memcpy(d, s, n);
        return;
    }
    size_t part = ((n + t - 1) / t + 63) & ~(size_t)63;
    std::vector<std::thread> th;
    th.reserve(t - 1);
    for (size_t i = 1; i < t; i++) {
        size_t off = i * part;
        if (off >= n) break;
        size_t m = n - off < part ? n - off : part;
        char* dd = (char*)d + off;
        const char* ss = (const char*)s + off;
        try {
            th.emplace_back([dd, ss, m] { memcpy(dd, ss, m); });
        } catch (...) {
            memcpy(dd, ss, m);
        }
    }
    memcpy(d, s, part < n ? part : n);
    for (auto& x : th) x.join();
}

// The bounce buffer of this request: allocated at the first call, false when staging is off.
// Whether a drain could not be confirmed since `at` (a transfer may still target a buffer that
// existed then).
static bool undrained_since(uint64_t at) { return g_drain[1].load() > at; }
// The unconfirmed-drain count that a successful context reset settled (mgpu_teardown_context:
// the reset ended every transfer). While the count is above it, a transfer may still be in
// flight, so no host buffer is handed out, a fresh one included: a buffer allocated after the
// failed drain would take the grown count as its snapshot and could be wiped or freed under
// that transfer.
static std::atomic<uint64_t> g_drain_settled{0};
static bool undrained_now() { return g_drain[1].load() > g_drain_settled.load(); }

// Keeps the bounce buffer after an unconfirmed drain: never wiped, freed or used again (a
// transfer may still read or write it); counted once as an erasure failure.
static void stage_hold()
{
    if (!g_stage.held) {
        g_stage.held = true;
        g_stage.dead = true;
        g_erase_fail++;
    }
}

static bool stage_get()
{
    if (g_stage.held) return false;
    if (g_stage.buf && undrained_since(g_stage.undrained_at)) {
        // a failed drain since the buffer was allocated: the copy takes the direct path
        stage_hold();
        return false;
    }
    if (undrained_now()) return false;
    if (g_stage.dead) return false;
    if (g_stage.buf) return true;
    if (g_stage.failed || g_stage.slow || !stage_enabled()) return false;
    void* p = nullptr;
    size_t n = STAGE_BYTES;
    cudaError_t e = cudaHostAlloc(&p, n, cudaHostAllocDefault);
    if (e != cudaSuccess) {
        (void)cudaGetLastError();
        n = STAGE_BYTES / 4;
        e = cudaHostAlloc(&p, n, cudaHostAllocDefault);
    }
    if (e != cudaSuccess) {
        (void)cudaGetLastError();
        g_stage.failed = true;
        g_stage_ctr[4]++;
        return false;
    }
    for (size_t k = 0; k < STAGE_SLOTS; k++) {
        if (cudaEventCreateWithFlags(&g_stage.ev[k], cudaEventDisableTiming) != cudaSuccess) {
            (void)cudaGetLastError();
            for (size_t j = 0; j < k; j++) cudaEventDestroy(g_stage.ev[j]);
            g_stage.failed = true;
            g_stage_ctr[4]++;
            // the fresh buffer (no witness byte yet) goes back now; if its free fails it is
            // kept as a dead buffer (never used, released by the next mgpu_stage_end) and an
            // erasure failure is counted, so the page-locked budget never loses track of it
            if (cudaFreeHost(p) != cudaSuccess) {
                (void)cudaGetLastError();
                g_wipe[4]++;
                g_erase_fail++;
                g_stage.buf = (char*)p;
                g_stage.bytes = n;
                g_stage.events = false;
                g_stage.dead = true;
            }
            return false;
        }
    }
    g_stage.buf = (char*)p;
    g_stage.bytes = n;
    g_stage.events = true;
    g_stage.undrained_at = g_drain[1].load();
    g_stage_ctr[5]++;
    return true;
}

// Zeroes a host buffer of this translation unit (the bounce buffer, the private read-back
// buffer) and counts it; in check mode reads it back. false: a byte read back non-zero.
static bool host_wipe(char* p, size_t n)
{
    memset(p, 0, n);
    // the zeroing stays: the compiler must assume the memory is read here
    __asm__ __volatile__("" : : "r"(p) : "memory");
    g_stage_wipe[0]++;
    g_stage_wipe[1] += n;
    if (g_wipe_check.load()) {
        const volatile unsigned char* q = (const volatile unsigned char*)p;
        bool nz = false;
        for (size_t i = 0; i < n && !nz; i++) nz = q[i] != 0;
        g_stage_wipe[2]++;
        if (nz) {
            g_stage_wipe[3]++;
            return false;
        }
    }
    return true;
}

// Zeroes and frees the bounce buffer. Every staged copy synchronised its stream
// before it returned, so no transfer reads or writes the buffer now. 0: freed (or none). A failed
// cudaFreeHost keeps the pointer and length (the next call retries the release) and marks the
// buffer dead (no copy uses it again); a failed check-mode read-back or free is an erasure
// failure (g_erase_fail).
static int stage_free()
{
    if (!g_stage.buf) return 0;
    // after an unconfirmed drain a transfer may still target the buffer: it is kept (no wipe,
    // no free) before anything else touches it
    if (g_stage.held || undrained_since(g_stage.undrained_at)) {
        stage_hold();
        return -1;
    }
    char* p = g_stage.buf;
    size_t n = g_stage.bytes;
    int rc = 0;
    if (!host_wipe(p, n)) {
        // the zeroing is not confirmed: the buffer is kept (dead, never used again, retried by
        // the next call), not handed back with its bytes
        g_erase_fail++;
        g_stage.dead = true;
        return -1;
    }
    if (g_stage.events) {
        for (size_t k = 0; k < STAGE_SLOTS; k++) cudaEventDestroy(g_stage.ev[k]);
        g_stage.events = false;
    }
    if (cudaFreeHost(p) != cudaSuccess) {
        (void)cudaGetLastError();
        g_wipe[4]++;
        g_erase_fail++;
        g_stage.dead = true;
        return -1;
    }
    g_stage.buf = nullptr;
    g_stage.bytes = 0;
    g_stage.dead = false;
    return rc;
}

// the private read-back buffer of a device-to-host copy whose destination the caller
// may retry on the CPU (the in-place NTT): pageable host memory owned by this translation unit,
// grow-only within a request, zeroed and freed by mgpu_stage_end. Holds witness values.
static char* g_rb = nullptr;
static size_t g_rb_bytes = 0;

static bool g_rb_dead = false;  // its zeroing check failed: kept, never used again
static uint64_t g_rb_undrained_at = 0;  // g_drain[1] when the buffer was allocated
static bool g_rb_held = false;  // kept after an unconfirmed drain: never wiped, freed or reused

// Keeps the read-back buffer after an unconfirmed drain (as stage_hold).
static void rb_hold()
{
    if (!g_rb_held) {
        g_rb_held = true;
        g_rb_dead = true;
        g_erase_fail++;
    }
}

// Zeroes and frees the private read-back buffer. A check that finds a non-zero byte keeps the
// buffer (not freed, never used again, retried by the next call) and counts an erasure failure.
static int rb_free()
{
    if (!g_rb) return 0;
    if (g_rb_held || undrained_since(g_rb_undrained_at)) {
        rb_hold();
        return -1;
    }
    if (!host_wipe(g_rb, g_rb_bytes)) {
        g_erase_fail++;
        g_rb_dead = true;
        return -1;
    }
    free(g_rb);
    g_rb = nullptr;
    g_rb_bytes = 0;
    g_rb_dead = false;
    return 0;
}

static char* rb_get(size_t n)
{
    if (g_rb_dead) return nullptr;
    if (g_rb && undrained_since(g_rb_undrained_at)) {
        rb_hold();
        return nullptr;
    }
    if (undrained_now()) return nullptr;
    if (g_rb_bytes >= n) return g_rb;
    if (rb_free() != 0) return nullptr;
    g_rb = (char*)malloc(n);
    if (!g_rb) return nullptr;
    g_rb_bytes = n;
    g_rb_undrained_at = g_drain[1].load();
    return g_rb;
}

static cudaError_t staged_htod(void* dst, const void* src, size_t bytes, cudaStream_t s)
{
    const size_t slot = g_stage.bytes / STAGE_SLOTS;
    const size_t nch = (bytes + slot - 1) / slot;
    cudaError_t e = cudaSuccess;
    for (size_t i = 0; i < nch && e == cudaSuccess; i++) {
        size_t k = i % STAGE_SLOTS, off = i * slot;
        size_t m = bytes - off < slot ? bytes - off : slot;
        char* b = g_stage.buf + k * slot;
        // the slot's previous copy has left the buffer
        if (i >= STAGE_SLOTS && (e = cudaEventSynchronize(g_stage.ev[k])) != cudaSuccess) break;
        par_memcpy(b, (const char*)src + off, m);
        e = cudaMemcpyAsync((char*)dst + off, b, m, cudaMemcpyHostToDevice, s);
        if (e == cudaSuccess) e = cudaEventRecord(g_stage.ev[k], s);
    }
    cudaError_t e2 = cudaStreamSynchronize(s);
    return e != cudaSuccess ? e : e2;
}

static cudaError_t staged_dtoh(void* dst, const void* src, size_t bytes, cudaStream_t s)
{
    const size_t slot = g_stage.bytes / STAGE_SLOTS;
    const size_t nch = (bytes + slot - 1) / slot;
    cudaError_t e = cudaSuccess;
    auto issue = [&](size_t i) {
        size_t k = i % STAGE_SLOTS, off = i * slot;
        size_t m = bytes - off < slot ? bytes - off : slot;
        e = cudaMemcpyAsync(g_stage.buf + k * slot, (const char*)src + off, m,
                            cudaMemcpyDeviceToHost, s);
        if (e == cudaSuccess) e = cudaEventRecord(g_stage.ev[k], s);
    };
    size_t issued = 0;
    for (; issued < nch && issued < STAGE_SLOTS && e == cudaSuccess; issued++) issue(issued);
    for (size_t i = 0; i < nch && e == cudaSuccess; i++) {
        size_t k = i % STAGE_SLOTS, off = i * slot;
        size_t m = bytes - off < slot ? bytes - off : slot;
        if ((e = cudaEventSynchronize(g_stage.ev[k])) != cudaSuccess) break;
        par_memcpy((char*)dst + off, g_stage.buf + k * slot, m);
        // the slot is free again: the copy STAGE_SLOTS chunks ahead goes into it
        if (issued < nch) issue(issued++);
    }
    cudaError_t e2 = cudaStreamSynchronize(s);
    return e != cudaSuccess ? e : e2;
}

// A synchronous copy between pageable host memory and the device on stream s: through the
// bounce buffer when it is large and staging is on, else as before.
static cudaError_t copy_sync(void* dst, const void* src, size_t bytes, cudaMemcpyKind kind,
                             cudaStream_t s)
{
    if (bytes >= STAGE_MIN && stage_get()) {
        auto t0 = std::chrono::steady_clock::now();
        cudaError_t e = kind == cudaMemcpyHostToDevice ? staged_htod(dst, src, bytes, s)
                                                       : staged_dtoh(dst, src, bytes, s);
        if (e == cudaSuccess && test_fail_arm(ARM_STAGED_COPY, s)) e = cudaErrorUnknown;
        if (e != cudaSuccess) {
            // a failed chunk or final synchronisation returns only after the stream drained,
            // as the direct copy does: an unconfirmed drain holds the bounce buffer
            drain_stream(s);
            return e;
        }
        g_last_route = 1;
        g_stage_ctr[0]++;
        g_stage_ctr[1] += bytes;
        if (kind == cudaMemcpyHostToDevice && !g_stage.probed && bytes >= STAGE_PROBE) {
            g_stage.probed = true;
            double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            if (sec > 0 && (double)bytes / sec < STAGE_SLOW_GIB_S * (double)(1u << 30)) {
                g_stage.slow = true;
                g_stage_ctr[6]++;
                (void)stage_free();
            }
        }
        return cudaSuccess;
    }
    g_last_route = bytes >= STAGE_MIN ? 2 : 0;
    if (bytes >= STAGE_MIN) {
        g_stage_ctr[2]++;
        g_stage_ctr[3] += bytes;
    }
    cudaError_t e = cudaMemcpyAsync(dst, src, bytes, kind, s);
    if (e == cudaSuccess && test_fail_arm(ARM_COPY, s)) e = cudaErrorUnknown;
    if (e == cudaSuccess) e = cudaStreamSynchronize(s);
    if (e != cudaSuccess) {
        // a failed enqueue or synchronisation returns only after the stream drained
        drain_stream(s);
        return e;
    }
    return cudaSuccess;
}

// Staging counters (host memory only: no CUDA call): staged copies, staged bytes, direct large
// copies, direct bytes, failed allocations, allocations, bus-bound requests, bounce bytes held.
extern "C" void mgpu_stage_counters(uint64_t out[8])
{
    for (int i = 0; i < 7; i++) out[i] = g_stage_ctr[i].load();
    out[7] = g_stage.bytes.load();
}

extern "C" void mgpu_stage_reset()
{
    for (int i = 0; i < 7; i++) g_stage_ctr[i] = 0;
}

// Bounce buffers zeroed, their bytes, read back, non-zero (reset with mgpu_wipe_reset).
extern "C" void mgpu_stage_wipe_counters(uint64_t out[4])
{
    for (int i = 0; i < 4; i++) out[i] = g_stage_wipe[i].load();
}

// Route of the calling thread's last mgpu_htod / mgpu_dtoh: 0 small, 1 staged, 2 large direct.
extern "C" int mgpu_stage_last_route() { return g_last_route; }

// End of a request: zeroes and frees the bounce buffer and the private read-back buffer and
// forgets this request's decisions (failed allocation, bus-bound link). 0: both erased and
// released; -1: an erasure or release failed (counted in mgpu_erase_failures; a bounce buffer
// whose free failed is kept and released by the next call).
extern "C" int mgpu_stage_end()
{
    int rc = stage_free();
    if (rb_free() != 0) rc = -1;
    g_stage.failed = false;
    g_stage.slow = false;
    g_stage.probed = false;
    return rc;
}

// a device-to-host copy into a private host buffer, never into the caller's. On
// success returns the private buffer, which holds all `bytes` (the caller copies them out with
// mgpu_host_copy and only then publishes them); on any error (a copy, the synchronisation, or the
// test fault) returns null and the caller's buffer was not touched. Route: a copy that fits the
// bounce buffer goes into it in one page-locked transfer; any other goes into the private
// read-back buffer (through the bounce ring when staging is on). `fault_after_first_chunk`
// (test-fault builds only pass 1) copies the first chunk into the private buffer, synchronises,
// and then fails as a later chunk would.
extern "C" const void* mgpu_dtoh_private(const void* src, size_t bytes, int fault_after_first_chunk)
{
    auto& gpu = select_gpu(0);
    char* priv;
    bool bounce = bytes >= STAGE_MIN && stage_get() && bytes <= g_stage.bytes;
    if (bounce) {
        priv = g_stage.buf;
    } else {
        priv = rb_get(bytes ? bytes : 1);
        if (!priv) {
            fail("dtoh_private: host allocation", (int)(bytes >> 20));
            return nullptr;
        }
    }
    cudaError_t e;
#ifndef MGPU_TEST_FAULT
    // the injected failure exists only in a test-fault build
    fault_after_first_chunk = 0;
#endif
    if (fault_after_first_chunk) {
        size_t first = bytes < ((size_t)4 << 20) ? bytes : ((size_t)4 << 20);
        e = cudaMemcpyAsync(priv, src, first, cudaMemcpyDeviceToHost, gpu);
        if (e == cudaSuccess) e = cudaStreamSynchronize(gpu);
        if (e == cudaSuccess) e = cudaErrorUnknown;
    } else if (bounce) {
        e = cudaMemcpyAsync(priv, src, bytes, cudaMemcpyDeviceToHost, gpu);
        if (e == cudaSuccess) e = cudaStreamSynchronize(gpu);
        if (e == cudaSuccess) {
            g_last_route = 1;
            g_stage_ctr[0]++;
            g_stage_ctr[1] += bytes;
        }
    } else {
        e = copy_sync(priv, src, bytes, cudaMemcpyDeviceToHost, gpu);
    }
    if (e == cudaSuccess) e = cudaGetLastError();
    if (e == cudaSuccess && test_fail_arm(ARM_READBACK, gpu)) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        // no copy into the private buffer runs on after this exit
        drain_stream(gpu);
        fail("dtoh_private", e);
        return nullptr;
    }
    return priv;
}

// Host memcpy on up to MIDNIGHT_GPU_STAGE_THREADS threads (the publication of a private read-back).
extern "C" void mgpu_host_copy(void* dst, const void* src, size_t bytes) { par_memcpy(dst, src, bytes); }

extern "C" int mgpu_htod(void* dst, const void* src, size_t bytes)
{
    auto& gpu = select_gpu(0);
    cudaError_t e = copy_sync(dst, src, bytes, cudaMemcpyHostToDevice, gpu);
    return e == cudaSuccess ? 0 : fail("htod", e);
}

extern "C" int mgpu_dtoh(void* dst, const void* src, size_t bytes)
{
    auto& gpu = select_gpu(0);
    cudaError_t e = copy_sync(dst, src, bytes, cudaMemcpyDeviceToHost, gpu);
    return e == cudaSuccess ? 0 : fail("dtoh", e);
}

// Whether p is ordinary (pageable) host memory, which the staging path may read.
static bool pageable_host(const void* p)
{
    cudaPointerAttributes a;
    if (cudaPointerGetAttributes(&a, p) != cudaSuccess) {
        (void)cudaGetLastError();
        return false;
    }
    return a.type == cudaMemoryTypeUnregistered;
}

extern "C" int mgpu_dev_sync()
{
    auto& gpu = select_gpu(0);
    cudaError_t e = cudaStreamSynchronize(gpu);
    if (e == cudaSuccess) e = cudaGetLastError();
    return e == cudaSuccess ? 0 : fail("sync", e);
}

// NTT in place on a device buffer (no copies).
// Drains `s` after a failed call, so no enqueued copy or kernel still reads a host source or
// writes a device buffer when the caller releases them.
static void drain(cudaStream_t s) { (void)drain_stream(s); }

extern "C" int mgpu_ntt_dev(fr_t* d, uint32_t lg, int inverse)
{
    // no singleton or oversize transform reaches NTT_internal
    if (lg < 1 || lg > 28) return fail("ntt_dev: size", (int)lg);
    auto& gpu = select_gpu(0);
    try {
        DevNTT::run(d, lg, inverse != 0, gpu);
        CUDA_OK(cudaGetLastError());
    } catch (const cuda_error& e) {
        drain(gpu);
        return fail("ntt_dev", e.code());
    }
    return 0;
}

// coeff_to_extended on device: dst (2^ext_k) = FFT_ext(zeta-distribute(src (2^k)) || 0).
// src and dst may be host (unified) or device pointers; dst must be a device buffer.
extern "C" int mgpu_coeff_to_extended_dev(fr_t* d_dst, const fr_t* src, uint32_t k,
                                          uint32_t ext_k, const fr_t* zeta2)
{
    // the dimensions again at the boundary, before any shift, copy or kernel: no singleton
    // input (k = 0, also (0, 0)), k <= ext_k <= 28
    if (k < 1 || k > ext_k || ext_k > 28) return fail("coeff_to_extended_dev: dimensions", (int)ext_k);
    auto& gpu = select_gpu(0);
    size_t n = (size_t)1 << k, en = (size_t)1 << ext_k;
    try {
        // pageable host coefficients of 16 MiB or more go through the bounce buffer
        // (synchronous); device or registered memory as before
        if (n * sizeof(fr_t) >= STAGE_MIN && pageable_host(src))
            CUDA_OK(copy_sync(d_dst, src, n * sizeof(fr_t), cudaMemcpyHostToDevice, gpu));
        else
            CUDA_OK(cudaMemcpyAsync(d_dst, src, n * sizeof(fr_t), cudaMemcpyDefault, gpu));
        CUDA_OK(cudaMemsetAsync(d_dst + n, 0, (en - n) * sizeof(fr_t), gpu));
        mgpu_distribute_zeta<<<(n + 255) / 256, 256, 0, gpu>>>(d_dst, n, f8_of(zeta2), f8_of((const char*)zeta2 + sizeof(F8)));
        CUDA_OK(cudaGetLastError());
        DevNTT::run(d_dst, ext_k, false, gpu);
        CUDA_OK(cudaGetLastError());
    } catch (const cuda_error& e) {
        // the copy from the caller's host coefficients may still be in flight
        drain(gpu);
        return fail("coeff_to_extended_dev", e.code());
    }
    return 0;
}

// Elementwise helpers on device buffers.
extern "C" int mgpu_distribute_zeta_dev(fr_t* d, size_t n, const fr_t* zeta2)
{
    auto& gpu = select_gpu(0);
    mgpu_distribute_zeta<<<(n + 255) / 256, 256, 0, gpu>>>(d, n, f8_of(zeta2), f8_of((const char*)zeta2 + sizeof(F8)));
    cudaError_t e = cudaGetLastError();
    if (e == cudaSuccess && test_fail_arm(ARM_ZETA, gpu)) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        drain_stream(gpu);
        return fail("distribute_zeta", e);
    }
    return 0;
}

extern "C" int mgpu_scale_dev(fr_t* d, size_t n, const fr_t* c)
{
    auto& gpu = select_gpu(0);
    mgpu_scale<<<(n + 255) / 256, 256, 0, gpu>>>(d, n, f8_of(c));
    cudaError_t e = cudaGetLastError();
    if (e == cudaSuccess && test_fail_arm(ARM_SCALE, gpu)) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        drain_stream(gpu);
        return fail("scale", e);
    }
    return 0;
}

// h[i] *= t[i % tn] (divide_by_vanishing_poly with precomputed inverse evaluations)
extern "C" int mgpu_mul_periodic_dev(fr_t* d, size_t n, const fr_t* t, size_t tn)
{
    auto& gpu = select_gpu(0);
    fr_t* dt = nullptr;
    cudaError_t e = cudaMallocAsync(&dt, tn * sizeof(fr_t), gpu);
    if (e == cudaSuccess) e = cudaMemcpyAsync(dt, t, tn * sizeof(fr_t), cudaMemcpyDefault, gpu);
    if (e == cudaSuccess && test_fail_arm(ARM_PERIODIC_COPY, gpu)) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        // the copy from the caller's table may still run
        drain_stream(gpu);
        // the table is released on this path too (through the wrapper, confirmed)
        if (dt) cudaFreeAsync(dt, gpu);
        return fail("mul_periodic", e);
    }
    mgpu_mul_periodic<<<(n + 255) / 256, 256, 0, gpu>>>(d, n, dt, tn);
    e = cudaGetLastError();
    if (e == cudaSuccess && test_fail_arm(ARM_PERIODIC_KERNEL, gpu)) e = cudaErrorUnknown;
    if (e != cudaSuccess) {
        drain_stream(gpu);
        cudaFreeAsync(dt, gpu);
        return fail("mul_periodic", e);
    }
    cudaFreeAsync(dt, gpu);
    return 0;
}


// The quotient numerator of a packed job (quotient.cuh). The job's pointers are device
// pointers; the scratch holds nslots * stride elements. stride is the grid size: a
// multiple of 256, at most 2^31 blocks.
extern "C" int mgpu_quotient_run(const DJob* job)
{
    if (job->stride == 0 || job->stride % 256 != 0 || job->stride / 256 > 0x7fffffffu)
        return fail("quotient: stride", (int)(job->stride & 0x7fffffff));
    auto& gpu = select_gpu(0);
    try {
        mgpu_quotient_kernel<<<(uint32_t)(job->stride / 256), 256, 0, gpu>>>(*job);
        CUDA_OK(cudaGetLastError());
    } catch (const cuda_error& e) {
        drain(gpu);
        return fail("quotient", e.code());
    }
    return 0;
}

// Size of the kernel argument, for the layout check of the Rust mirror.
extern "C" size_t mgpu_job_size() { return sizeof(DJob); }

#ifdef MGPU_TEST_FAULT
// Test only: the three host-buffer paths after an unconfirmed drain (a drain made to report
// "not confirmed"). out[0] stage_get: 1 when it refuses the existing bounce buffer. out[1]
// stage_free: 1 when the buffer is kept unwiped (pointer and witness pattern intact). out[2]
// rb_free: 1 when the read-back buffer is kept unwiped. Returns 0, or -1 when staging is off
// on this device (out[0], out[1] are then 2).
extern "C" int mgpu_test_stage_paths(uint64_t out[3])
{
    auto& gpu = select_gpu(0);
    const unsigned char pat = 0x5A;
    auto unconfirmed_drain = [&] {
        g_test_unconfirm = 1;
        (void)drain_stream(gpu);
        g_test_unconfirm = 0;
    };
    auto intact = [&](const char* p, size_t n) {
        for (size_t i = 0; i < n; i += 4096)
            if ((unsigned char)p[i] != pat) return false;
        return true;
    };
    // the read-back buffer is taken before the first drain: after an unconfirmed drain no
    // host buffer is handed out
    char* r = rb_get(1 << 20);
    if (!r) return -1;
    memset(r, pat, g_rb_bytes);
    size_t rn = g_rb_bytes;
    int rc = 0;
    if (stage_get()) {
        memset(g_stage.buf, pat, g_stage.bytes);
        unconfirmed_drain();
        out[0] = !stage_get();
        char* p = g_stage.buf;
        size_t n = g_stage.bytes;
        bool freed = stage_free() == 0 && g_stage.buf == nullptr;
        out[1] = !freed && g_stage.buf == p && intact(p, n);
    } else {
        out[0] = out[1] = 2;
        rc = -1;
    }
    unconfirmed_drain();
    bool rfreed = rb_free() == 0 && g_rb == nullptr;
    out[2] = !rfreed && g_rb == r && intact(r, rn);
    return rc;
}

// Test only: fails each error arm once (test_fail_arm) and records, per arm, whether the call
// returned an error and whether the stream was idle when it returned (out[2 * i], out[2 * i + 1]
// for arm i + 1). Returns the number of arms, -1 when the buffers could not be made.
extern "C" int mgpu_test_error_arms(uint64_t* out)
{
    auto& gpu = select_gpu(0);
    const size_t n = 1 << 12;
    std::vector<fr_t> host(n);
    memset((void*)host.data(), 0, n * sizeof(fr_t));
    fr_t* d = nullptr;
    if (raw_malloc((void**)&d, n * sizeof(fr_t)) != cudaSuccess) {
        (void)cudaGetLastError();
        return -1;
    }
    (void)cudaMemset(d, 0, n * sizeof(fr_t));
    std::vector<affine_t> pts(n);
    memset((void*)pts.data(), 0, n * sizeof(affine_t));
    point_t res;
    int nargs = ARM_MSM_CTX;
    for (int id = 1; id <= nargs; id++) {
        (void)cudaDeviceSynchronize();
        g_test_arm = id;
        int rc = 0;
        switch (id) {
        case ARM_COPY: rc = mgpu_htod(d, host.data(), n * sizeof(fr_t)); break;
        case ARM_READBACK: rc = mgpu_dtoh_private(d, n * sizeof(fr_t), 0) ? 0 : -1; break;
        case ARM_ZETA: rc = mgpu_distribute_zeta_dev(d, n, host.data()); break;
        case ARM_SCALE: rc = mgpu_scale_dev(d, n, host.data()); break;
        case ARM_PERIODIC_COPY:
        case ARM_PERIODIC_KERNEL: rc = mgpu_mul_periodic_dev(d, n, host.data(), 4); break;
        case ARM_MSM: rc = mgpu_msm_g1(&res, pts.data(), n, host.data()); break;
        case ARM_MSM_CTX: {
            void* c = mgpu_msm_ctx_new(pts.data(), n);
            if (!c) { rc = 0; break; }
            rc = mgpu_msm_ctx_run(c, &res, host.data(), n);
            (void)mgpu_msm_ctx_free(c);
            break;
        }
        }
        // MSM arms: idle means no work left on the device
        bool idle = cudaStreamQuery(gpu) == cudaSuccess;
        (void)cudaGetLastError();
        out[2 * (id - 1)] = rc != 0;
        out[2 * (id - 1) + 1] = idle;
        g_test_arm = 0;
        (void)cudaDeviceSynchronize();
        (void)cudaGetLastError();
    }
    (void)raw_free(d);
    return nargs;
}
#endif

#ifdef MGPU_TEST_FAULT
// Test only: with no host buffer allocated yet, one drain is made to report "not confirmed";
// out[0] is 1 when stage_get then refuses to allocate a bounce buffer (2 when this device does
// not stage copies), out[1] is 1 when rb_get refuses to allocate a read-back buffer. -1 when a
// buffer already existed (the probe needs a process that has not staged or read back yet).
extern "C" int mgpu_test_get_after_unconfirmed_drain(uint64_t out[2])
{
    auto& gpu = select_gpu(0);
    if (g_stage.buf || g_rb) return -1;
    g_test_unconfirm = 1;
    (void)drain_stream(gpu);
    g_test_unconfirm = 0;
    bool staging = stage_enabled() && !g_stage.failed && !g_stage.slow;
    out[0] = staging ? (stage_get() ? 0 : 1) : 2;
    out[1] = rb_get(1 << 20) ? 0 : 1;
    return 0;
}
#endif

#ifdef MGPU_TEST_FAULT
// Test only: one staged host-to-device copy whose final synchronisation fails with work still
// queued on the stream (a spinning kernel), and whose error drain is made to report "not
// confirmed". out[0] the copy returned an error, out[1] the stream was idle when it returned,
// out[2] drains run by the call, out[3] of them not confirmed, out[4] stage_get then refuses the
// bounce buffer and holds it, out[5] erasure failures added. Returns 0, -1 when the buffers could
// not be made, -2 when staging is off on this device (every out word is then 2). Run it in its
// own process: the bounce buffer stays held.
extern "C" int mgpu_test_staged_sync_fail(uint64_t out[6])
{
    auto& gpu = select_gpu(0);
    const size_t bytes = STAGE_MIN * 2;
    if (!stage_get()) {
        for (int i = 0; i < 6; i++) out[i] = 2;
        return -2;
    }
    std::vector<char> host(bytes, 0);
    void* d = nullptr;
    if (raw_malloc(&d, bytes) != cudaSuccess) {
        (void)cudaGetLastError();
        return -1;
    }
    (void)cudaDeviceSynchronize();
    uint64_t run0 = g_drain[0].load(), bad0 = g_drain[1].load(), ef0 = g_erase_fail.load();
    g_test_arm = ARM_STAGED_COPY;
    g_test_unconfirm = 1;
    int rc = mgpu_htod(d, host.data(), bytes);
    bool idle = cudaStreamQuery(gpu) == cudaSuccess;
    (void)cudaGetLastError();
    g_test_arm = 0;
    g_test_unconfirm = 0;
    out[0] = rc != 0;
    out[1] = idle;
    out[2] = g_drain[0].load() - run0;
    out[3] = g_drain[1].load() - bad0;
    (void)cudaDeviceSynchronize();
    (void)cudaGetLastError();
    out[4] = !stage_get() && g_stage.held;
    out[5] = g_erase_fail.load() - ef0;
    (void)raw_free(d);
    return 0;
}

// Test only (actor probe a): one cooperative kernel resident on stream
// A, then a second cooperative launch on stream B. out (int64):
// [second launch cudaError_t code, queued (code == 0), sequential
// (B's kernel start stamp at or after A's end stamp), A duration in
// microseconds, B start offset from A start in microseconds, B
// duration in microseconds, B launch host call in microseconds].
// Durations come from the kernels' clock64 stamps and the device
// clock rate. Returns 0 when the probe ran, -1 otherwise.
extern "C" int mgpu_test_probe_cooperative(int64_t out[7])
{
    for (int i = 0; i < 7; i++) out[i] = 0;
    try {
        (void)select_gpu(0);
    } catch (...) {
        return -1;
    }
    cudaDeviceProp prop;
    if (cudaGetDeviceProperties(&prop, 0) != cudaSuccess || !prop.cooperativeLaunch)
        return -1;
    int blocks_per_sm = 0;
    if (cudaOccupancyMaxActiveBlocksPerMultiprocessor(
            &blocks_per_sm, (void*)mgpu_probe_coop_kernel, 128, 0) != cudaSuccess ||
        blocks_per_sm <= 0)
        return -1;
    int grid = blocks_per_sm * prop.multiProcessorCount;
    cudaStream_t sa = nullptr, sb = nullptr;
    volatile int* ready = nullptr;
    void* ready_dev = nullptr;
    long long* stamps = nullptr;
    auto fail_out = [&]() {
        (void)cudaGetLastError();
        if (stamps) (void)raw_free(stamps);
        if (ready) (void)cudaFreeHost((void*)ready);
        if (sa) (void)cudaStreamDestroy(sa);
        if (sb) (void)cudaStreamDestroy(sb);
        return -1;
    };
    if (cudaStreamCreateWithFlags(&sa, cudaStreamNonBlocking) != cudaSuccess ||
        cudaStreamCreateWithFlags(&sb, cudaStreamNonBlocking) != cudaSuccess ||
        cudaHostAlloc((void**)&ready, sizeof(int), cudaHostAllocMapped) != cudaSuccess ||
        cudaHostGetDevicePointer(&ready_dev, (void*)ready, 0) != cudaSuccess ||
        raw_malloc((void**)&stamps, 4 * sizeof(long long)) != cudaSuccess)
        return fail_out();
    *ready = 0;
    (void)cudaMemset(stamps, 0, 4 * sizeof(long long));
    int slot_a = 0, slot_b = 1;
    int rounds_a = 60, rounds_b = 2;
    long long cycles = 2000000;
    void* args_a[] = {(void*)&ready_dev, (void*)&stamps, (void*)&slot_a,
                      (void*)&rounds_a, (void*)&cycles};
    // cudaHostGetDevicePointer gives the device view of the flag; the
    // kernel argument must carry that address by value.
    volatile int* ready_arg = (volatile int*)ready_dev;
    args_a[0] = (void*)&ready_arg;
    cudaError_t first = cudaLaunchCooperativeKernel((void*)mgpu_probe_coop_kernel,
                                                    dim3(grid), dim3(128), args_a, 0, sa);
    if (first != cudaSuccess) return fail_out();
    auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(10);
    while (*ready == 0) {
        if (std::chrono::steady_clock::now() > deadline) {
            (void)cudaStreamSynchronize(sa);
            return fail_out();
        }
        std::this_thread::sleep_for(std::chrono::microseconds(50));
    }
    void* null_ready = nullptr;
    void* args_b[] = {(void*)&null_ready, (void*)&stamps, (void*)&slot_b,
                      (void*)&rounds_b, (void*)&cycles};
    auto t0 = std::chrono::steady_clock::now();
    cudaError_t second = cudaLaunchCooperativeKernel((void*)mgpu_probe_coop_kernel,
                                                     dim3(grid), dim3(128), args_b, 0, sb);
    auto t1 = std::chrono::steady_clock::now();
    out[0] = (int64_t)second;
    out[1] = second == cudaSuccess;
    out[6] = (int64_t)std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count();
    (void)cudaGetLastError();
    (void)cudaStreamSynchronize(sa);
    if (second == cudaSuccess) (void)cudaStreamSynchronize(sb);
    (void)cudaGetLastError();
    long long h[4] = {0, 0, 0, 0};
    (void)cudaMemcpy(h, stamps, sizeof h, cudaMemcpyDeviceToHost);
    int clock_khz = 0;
    (void)cudaDeviceGetAttribute(&clock_khz, cudaDevAttrClockRate, 0);
    double us_per_cycle = clock_khz > 0 ? 1000.0 / (double)clock_khz : 0.0;
    out[2] = second == cudaSuccess && h[2] >= h[1];
    out[3] = (int64_t)((double)(h[1] - h[0]) * us_per_cycle);
    out[4] = (int64_t)((double)(h[2] - h[0]) * us_per_cycle);
    out[5] = (int64_t)((double)(h[3] - h[2]) * us_per_cycle);
    (void)raw_free(stamps);
    (void)cudaFreeHost((void*)ready);
    (void)cudaStreamDestroy(sa);
    (void)cudaStreamDestroy(sb);
    return 0;
}

// Test only (actor probe b): the stream-ordered allocator across
// streams, with the raw async calls (the wipe wrappers would device-
// synchronise and hide the answer). A long kernel on stream A uses a
// block allocated on A; the block is freed async on A; at once the
// same size is allocated async on B and first used on B. out (int64):
// [B malloc host call in microseconds, first use on B from malloc to
// completion in microseconds, A kernel time remaining after B's first
// use completed in microseconds, 1 when B's first use completed only
// once A was done, 1 when B got A's address]. 0 when the probe ran.
extern "C" int mgpu_test_probe_async_alloc(int64_t out[5])
{
    for (int i = 0; i < 5; i++) out[i] = 0;
    try {
        (void)select_gpu(0);
    } catch (...) {
        return -1;
    }
    cudaStream_t sa = nullptr, sb = nullptr;
    if (cudaStreamCreateWithFlags(&sa, cudaStreamNonBlocking) != cudaSuccess ||
        cudaStreamCreateWithFlags(&sb, cudaStreamNonBlocking) != cudaSuccess)
        return -1;
    const size_t bytes = (size_t)64 << 20;
    char* pa = nullptr;
    char* pb = nullptr;
    int rc = -1;
    if (raw_malloc_async((void**)&pa, bytes, sa) == cudaSuccess) {
        mgpu_probe_touch<<<64, 128, 0, sa>>>(pa, bytes, 300000000LL);
        if (raw_free_async(pa, sa) == cudaSuccess) {
            auto t0 = std::chrono::steady_clock::now();
            cudaError_t m = raw_malloc_async((void**)&pb, bytes, sb);
            auto t1 = std::chrono::steady_clock::now();
            if (m == cudaSuccess && pb) {
                out[0] = (int64_t)std::chrono::duration_cast<std::chrono::microseconds>(
                             t1 - t0)
                             .count();
                out[4] = pb == pa;
                mgpu_probe_touch<<<8, 128, 0, sb>>>(pb, bytes, 1000000LL);
                (void)cudaStreamSynchronize(sb);
                auto t2 = std::chrono::steady_clock::now();
                out[1] = (int64_t)std::chrono::duration_cast<std::chrono::microseconds>(
                             t2 - t0)
                             .count();
                out[3] = cudaStreamQuery(sa) == cudaSuccess;
                (void)cudaGetLastError();
                (void)cudaStreamSynchronize(sa);
                auto t3 = std::chrono::steady_clock::now();
                out[2] = (int64_t)std::chrono::duration_cast<std::chrono::microseconds>(
                             t3 - t2)
                             .count();
                rc = 0;
            }
        }
    }
    (void)cudaGetLastError();
    if (pb) (void)raw_free_async(pb, sb);
    (void)cudaStreamSynchronize(sa);
    (void)cudaStreamSynchronize(sb);
    (void)cudaGetLastError();
    (void)cudaStreamDestroy(sa);
    (void)cudaStreamDestroy(sb);
    return rc;
}
#endif

#include "teardown.cuh"
#endif

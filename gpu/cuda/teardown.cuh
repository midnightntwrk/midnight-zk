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

// Teardown entry points of the CUDA core. Included once by
// midnight_gpu.cu, in its host section, after the sppark headers and the
// wipe state it uses. Every caller runs on the device-owner actor
// thread of the Rust side. No function here throws across the FFI boundary.

// Frees the NTT twiddle tables now, while the CUDA runtime is alive.
// 0: freed, or none was built. -1: a table was kept (a later call
// retries it).
extern "C" int mgpu_ntt_teardown()
{
    try {
        return NTTParameters::teardown() ? 0 : -1;
    } catch (...) {
        (void)cudaGetLastError();
        return -1;
    }
}

// Quarantined blocks that a successful context reset took away while
// their zeroing was still unconfirmed: [blocks, bytes]. A reset frees
// device memory but does not zero it, so such a block is lost unerased;
// sticky, never reset in the process's life.
static std::atomic<uint64_t> g_teardown_lost[2];

// The lost-unerased counters above. Host memory only, no CUDA call.
extern "C" void mgpu_teardown_lost(uint64_t out[2])
{
    out[0] = g_teardown_lost[0].load();
    out[1] = g_teardown_lost[1].load();
}

// Attempts the zeroing of every quarantined block whose zeroing is not
// confirmed, before a reset takes the blocks away (no free here: the
// reset, or a later retry when the reset fails, releases them). A block
// whose zeroing confirms is marked erased.
static void teardown_zero_quarantine()
{
    std::vector<quar_t> q;
    {
        std::lock_guard<std::mutex> g(g_wipe_mu);
        q = g_quar;
    }
    for (auto& b : q) {
        if (b.erased)
            continue;
        if (!wipe_block(b.p, b.n, nullptr, false))
            continue;
        std::lock_guard<std::mutex> g(g_wipe_mu);
        for (auto& c : g_quar)
            if (c.p == b.p)
                c.erased = true;
    }
}

// The staging bounce buffer is page-locked memory that belongs to the
// context: a reset unmaps it, so it cannot be read or written after the
// reset. It is zeroed before the reset (best effort: a transfer that is
// still in flight may write it again until the reset ends that transfer
// and takes the pages away). true: no buffer, or zeroed.
static bool teardown_zero_bounce()
{
    if (!g_stage.buf) return true;
    return host_wipe(g_stage.buf, g_stage.bytes.load());
}

// Forgets the host buffers that held witness bytes, after a successful
// reset, without a CUDA call. The bounce buffer went with the context
// (zeroed before the reset by teardown_zero_bounce; `bounce_zeroed` is
// its result): its pointer and its events are forgotten and its memory
// is not touched. The private read-back buffer is plain host memory:
// the reset ended every transfer, so it is zeroed now and freed, also
// when it was kept after an unconfirmed drain. A kept buffer was
// already counted once as an erasure failure, so a failed zeroing is
// not counted again for it. No copy may use either again.
static void teardown_forget_host_buffers(bool bounce_zeroed)
{
    if (g_stage.buf) {
        if (!bounce_zeroed && !g_stage.held)
            g_erase_fail++;
        g_stage.buf = nullptr;
        g_stage.bytes = 0;
        g_stage.events = false;
        g_stage.failed = false;
        g_stage.slow = false;
        g_stage.probed = false;
    }
    g_stage.held = false;
    g_stage.undrained_at = g_drain[1].load();
    // Whether or not a buffer was held, no staging allocation may make
    // a fresh context after the reset.
    g_stage.dead = true;
    if (g_rb) {
        bool held = g_rb_held;
        if (!host_wipe(g_rb, g_rb_bytes) && !held)
            g_erase_fail++;
        free(g_rb);
        g_rb = nullptr;
        g_rb_bytes = 0;
    }
    g_rb_held = false;
    g_rb_undrained_at = g_drain[1].load();
    // every transfer ended with the context: the unconfirmed drains so far are settled
    g_drain_settled = g_drain[1].load();
    g_rb_dead = true;
}

// Resets the CUDA context of device 0, which ends every transfer that is
// still in flight. Best effort, in this order: synchronise the device,
// free the NTT tables, attempt the zeroing of every unconfirmed
// quarantined block, reset. On a successful reset the tables that
// could not be freed are forgotten (they went with the context),
// every still-unconfirmed quarantined block is counted as lost
// unerased, and only then is the quarantine list cleared (its blocks
// went with the context), with the size and live records of the dead
// context; the bounce buffer (zeroed before the reset, unmapped by it)
// is forgotten and the read-back buffer is zeroed and freed, without a
// CUDA call. When the reset fails nothing is
// cleared and nothing is counted as lost: the blocks are still held.
// 0 only when the reset succeeded; -1 otherwise.
extern "C" int mgpu_teardown_context()
{
    try {
        (void)cudaDeviceSynchronize();
        (void)cudaGetLastError();
        bool freed = NTTParameters::teardown();
        teardown_zero_quarantine();
        bool bounce_zeroed = teardown_zero_bounce();
        if (cudaDeviceReset() != cudaSuccess) {
            (void)cudaGetLastError();
            return -1;
        }
        if (!freed)
            NTTParameters::abandon();
        {
            std::lock_guard<std::mutex> g(g_wipe_mu);
            for (auto& b : g_quar) {
                if (!b.erased) {
                    g_teardown_lost[0]++;
                    g_teardown_lost[1] += b.n;
                }
            }
            g_quar.clear();
            // The size and live records describe allocations of the
            // dead context: forget them so the byte counters and the
            // wrapper lookups no longer describe it (the peak stays:
            // it is the process history, not a live count).
            g_wipe_sizes.clear();
            g_live_sizes.clear();
            g_dev_live.store(0);
        }
        teardown_forget_host_buffers(bounce_zeroed);
        (void)cudaGetLastError();
        return 0;
    } catch (...) {
        (void)cudaGetLastError();
        return -1;
    }
}

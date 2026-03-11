// This file is part of midnight-zk.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

// VROOM MSM computation — isolated in its own translation unit.
// Keeping this separate from the data generation code is CRITICAL for
// performance: clang's template optimizer generates 10x+ faster code
// when the msm() template is the only major instantiation in the TU.

#include "../vroom/cpu/precompute/gmp_wrapper.hpp"

#include "../vroom/src/msm.hpp"
#include "../vroom/src/bounded_ring.hpp"
#include "../vroom/src/conversion_inversion.hpp"

#include "wrapper_types.hpp"

extern "C" {

uint64_t vroom_g1_msm(void* ctx_ptr, const void* points_ptr,
                       const void* scalars_ptr, size_t npoints) {
    auto* ctx = static_cast<VroomContext*>(ctx_ptr);
    auto* pts = static_cast<const VroomPoints*>(points_ptr);
    auto* sc = static_cast<const VroomScalars*>(scalars_ptr);

    auto result = msm(ctx->curve, ctx->ring,
                      pts->data.data(), sc->ptrs.data(),
                      npoints, 255);

    BigInt z = ctx->ring.to_bigint(result.z);
    return z.to_ulong();
}

uint64_t vroom_g1_msm_parallel(void* ctx_ptr, const void* points_ptr,
                                const void* scalars_ptr, size_t npoints,
                                size_t num_threads) {
    auto* ctx = static_cast<VroomContext*>(ctx_ptr);
    auto* pts = static_cast<const VroomPoints*>(points_ptr);
    auto* sc = static_cast<const VroomScalars*>(scalars_ptr);

    auto result = msm_parallel(ctx->curve, ctx->ring,
                               pts->data.data(), sc->ptrs.data(),
                               npoints, 255, num_threads);

    BigInt z = ctx->ring.to_bigint(result.z);
    return z.to_ulong();
}

} // extern "C"

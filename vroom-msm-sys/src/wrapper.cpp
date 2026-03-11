// This file is part of midnight-zk.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

// VROOM FFI wrapper — context management and data generation.
// The MSM computation is in wrapper_msm.cpp (separate TU for performance).

#include "../vroom/cpu/precompute/gmp_wrapper.hpp"

extern "C" {
#include "../vroom/blst/vect.h"
#include "../vroom/blst/fields.h"
#include "../vroom/blst/consts.h"
#include "../vroom/blst/point.h"
#include "../vroom/blst/bytes.h"
#include "../vroom/blst/ec_mult.h"
}

#include "../vroom/src/bounded_ring.hpp"
#include "../vroom/src/conversion_inversion.hpp"

#include "wrapper_types.hpp"

#include <random>
#include <cstring>

// ----- External BLST symbols -----

extern "C" {
    extern const POINTonE1 BLS12_381_G1;
    void blst_p1_mult(POINTonE1 *out, const POINTonE1 *a, const byte *scalar, size_t nbits);
    void blst_p1_to_affine(POINTonE1_affine *out, const POINTonE1 *a);
}

// ----- Helpers -----

static void bigint_to_bytes_le(uint8_t *bytes, const BigInt &value, size_t len) {
    BigInt temp = value;
    for (size_t i = 0; i < len; i++) {
        bytes[i] = static_cast<uint8_t>(temp.to_ulong() & 0xff);
        temp = temp >> 8;
    }
}

static AffPoint blst_g1_to_affine_point(const POINTonE1_affine &p, const RingType &ring) {
    BigInt x = vec384_montgomery_to_bigint(p.X);
    BigInt y = vec384_montgomery_to_bigint(p.Y);
    AffPoint result;
    result.x = ring.from_bigint(x);
    result.y = ring.from_bigint(y);
    return result;
}

// ----- FFI functions -----

extern "C" {

void* vroom_ctx_new() {
    return new VroomContext();
}

void vroom_ctx_free(void* ctx) {
    delete static_cast<VroomContext*>(ctx);
}

void* vroom_generate_points(void* ctx_ptr, size_t npoints, uint64_t seed) {
    auto* ctx = static_cast<VroomContext*>(ctx_ptr);
    auto* pts = new VroomPoints();
    pts->data.resize(npoints);

    BigInt r(bls12_381_scalar_modulus_hex, 16);

    std::mt19937_64 gen(seed);

    for (size_t i = 0; i < npoints; i++) {
        BigInt pt_scalar = BigInt::random(256) % r;

        byte scalar_bytes[32] = {0};
        bigint_to_bytes_le(scalar_bytes, pt_scalar, 32);

        POINTonE1 blst_proj;
        blst_p1_mult(&blst_proj, &BLS12_381_G1, scalar_bytes, 256);

        POINTonE1_affine blst_aff;
        blst_p1_to_affine(&blst_aff, &blst_proj);

        pts->data[i] = blst_g1_to_affine_point(blst_aff, ctx->ring);
    }

    return pts;
}

void vroom_free_points(void* points) {
    delete static_cast<VroomPoints*>(points);
}

void* vroom_generate_scalars(size_t npoints, uint64_t seed) {
    auto* sc = new VroomScalars();
    sc->data.resize(npoints);
    sc->ptrs.resize(npoints);

    std::mt19937_64 gen(seed);

    for (size_t i = 0; i < npoints; i++) {
        sc->data[i].resize(32);
        for (size_t j = 0; j < 32; j += 8) {
            uint64_t val = gen();
            size_t remaining = std::min(size_t(8), size_t(32) - j);
            std::memcpy(sc->data[i].data() + j, &val, remaining);
        }
        sc->ptrs[i] = sc->data[i].data();
    }

    return sc;
}

void vroom_free_scalars(void* scalars) {
    delete static_cast<VroomScalars*>(scalars);
}

} // extern "C"

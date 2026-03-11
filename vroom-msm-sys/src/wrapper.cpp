// VROOM MSM FFI wrapper for Rust benchmarks.
// Handles point generation (via BLST scalar mult), scalar generation,
// and MSM dispatch — all behind opaque pointers.

#include "../vroom/cpu/precompute/gmp_wrapper.hpp"

extern "C" {
#include "../vroom/blst/vect.h"
#include "../vroom/blst/fields.h"
#include "../vroom/blst/consts.h"
#include "../vroom/blst/point.h"
#include "../vroom/blst/bytes.h"
#include "../vroom/blst/ec_mult.h"
}

#include "../vroom/src/msm.hpp"
#include "../vroom/src/bounded_ring.hpp"
#include "../vroom/src/conversion_inversion.hpp"
#include "../vroom/src/batch_inversion.hpp"
#include "../vroom/src/batch_affine.hpp"
#include "../vroom/src/ec.hpp"

#include <vector>
#include <random>
#include <cstring>

// ----- BLS12-381 types (same as test_msm.cpp) -----

using RingType = BoundedRing<381, 8, 52, -1932, 2377, 12>;
using CurveType = G1<RingType>;
using AffPoint = typename CurveType::AffPoint;
using ProjPoint = typename CurveType::ProjPoint;

static const char* bls12_381_modulus_hex =
    "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf"
    "6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";

static const char* bls12_381_scalar_modulus_hex =
    "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001";

// ----- External BLST symbols -----

extern "C" {
    extern const POINTonE1 BLS12_381_G1;
    void blst_p1_mult(POINTonE1 *out, const POINTonE1 *a, const byte *scalar, size_t nbits);
    void blst_p1_to_affine(POINTonE1_affine *out, const POINTonE1 *a);
}

// ----- Helpers (from test_msm.cpp) -----

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

// ----- Opaque context types -----

struct VroomContext {
    RingType ring;
    CurveType curve;

    VroomContext() : ring(BigInt(bls12_381_modulus_hex, 16)), curve() {}
};

struct VroomPoints {
    std::vector<AffPoint> data;
};

struct VroomScalars {
    std::vector<std::vector<uint8_t>> data;
    std::vector<const uint8_t*> ptrs;
};

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

    // Use seed-based RNG for reproducibility
    std::mt19937_64 gen(seed);

    for (size_t i = 0; i < npoints; i++) {
        // Generate a random scalar in the scalar field
        // Use two 64-bit randoms to get a 128-bit value, then mod r
        // For full 256-bit: use BigInt::random seeded approach
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
        // Fill with random bytes from seeded RNG
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

uint64_t vroom_g1_msm(void* ctx_ptr, const void* points_ptr,
                       const void* scalars_ptr, size_t npoints) {
    auto* ctx = static_cast<VroomContext*>(ctx_ptr);
    auto* pts = static_cast<const VroomPoints*>(points_ptr);
    auto* sc = static_cast<const VroomScalars*>(scalars_ptr);

    auto result = msm(ctx->curve, ctx->ring,
                      pts->data.data(), sc->ptrs.data(),
                      npoints, 255);

    // Return first limb of Z coordinate to prevent dead-code elimination
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

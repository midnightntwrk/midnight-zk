// This file is part of midnight-zk.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

// Shared type definitions for the VROOM MSM FFI wrapper.
// Split into a header so that msm and generation TUs can share types
// without being compiled together (which degrades msm performance).

#pragma once

#include "../vroom/src/bounded_ring.hpp"
#include "../vroom/src/ec.hpp"

#include <vector>
#include <cstdint>

// ----- BLS12-381 types -----

using RingType = BoundedRing<381, 8, 52, -1932, 2377, 12>;
using CurveType = G1<RingType>;
using AffPoint = typename CurveType::AffPoint;
using ProjPoint = typename CurveType::ProjPoint;

// ----- Opaque context types -----

static const char* bls12_381_modulus_hex =
    "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf"
    "6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";

static const char* bls12_381_scalar_modulus_hex =
    "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001";

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

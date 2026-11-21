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

// The BLS12-381 base field `Fp` (blst_fp).
//
// An `Fp` is twelve little-endian 32-bit limbs of the Montgomery form
// `a * 2^384 mod p`, reduced: the same 48 bytes as the host's `[u64; 6]`
// blst_fp limbs. A host `G1AffineLimbs` (`[u64; 12]`) is `x` then `y`, two
// `Fp`; a `G1JacobianLimbs` (`[u64; 18]`) is `X`, `Y`, `Z`.
//
// p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

#ifndef MIDNIGHT_METAL_FP_H
#define MIDNIGHT_METAL_FP_H

#include "mont.h"

struct FpParams {
    enum : int { N = 12 };
    enum : uint { INV = 0xfffcfffdu };
    static MONT_INLINE uint mod(int i) {
        switch (i) {
        case 0: return 0xffffaaabu;
        case 1: return 0xb9feffffu;
        case 2: return 0xb153ffffu;
        case 3: return 0x1eabfffeu;
        case 4: return 0xf6b0f624u;
        case 5: return 0x6730d2a0u;
        case 6: return 0xf38512bfu;
        case 7: return 0x64774b84u;
        case 8: return 0x434bacd7u;
        case 9: return 0x4b1ba7b6u;
        case 10: return 0x397fe69au;
        default: return 0x1a0111eau;
        }
    }
    // 2^384 mod p
    static MONT_INLINE uint one(int i) {
        switch (i) {
        case 0: return 0x0002fffdu;
        case 1: return 0x76090000u;
        case 2: return 0xc40c0002u;
        case 3: return 0xebf4000bu;
        case 4: return 0x53c758bau;
        case 5: return 0x5f489857u;
        case 6: return 0x70525745u;
        case 7: return 0x77ce5853u;
        case 8: return 0xa256ec6du;
        case 9: return 0x5c071a97u;
        case 10: return 0xfa80e493u;
        default: return 0x15f65ec3u;
        }
    }
};

typedef mont::Elem<FpParams> Fp;

MONT_INLINE Fp fp_zero() { return mont::zero<FpParams>(); }
MONT_INLINE Fp fp_one() { return mont::one<FpParams>(); }
MONT_INLINE bool fp_is_zero(Fp a) { return mont::is_zero<FpParams>(a); }
MONT_INLINE bool fp_eq(Fp a, Fp b) { return mont::eq<FpParams>(a, b); }
MONT_INLINE bool fp_is_reduced(Fp a) { return mont::is_reduced<FpParams>(a); }
MONT_INLINE Fp fp_add(Fp a, Fp b) { return mont::add<FpParams>(a, b); }
MONT_INLINE Fp fp_sub(Fp a, Fp b) { return mont::sub<FpParams>(a, b); }
MONT_INLINE Fp fp_neg(Fp a) { return mont::neg<FpParams>(a); }
MONT_INLINE Fp fp_dbl(Fp a) { return mont::dbl<FpParams>(a); }
MONT_INLINE Fp fp_mul(Fp a, Fp b) { return mont::mul<FpParams>(a, b); }
MONT_INLINE Fp fp_sqr(Fp a) { return mont::sqr<FpParams>(a); }

#endif // MIDNIGHT_METAL_FP_H

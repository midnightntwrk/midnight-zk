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

// The BLS12-381 scalar field `Fr` (midnight_curves::Fq, blst_fr).
//
// An `Fr` is eight little-endian 32-bit limbs of the Montgomery form
// `a * 2^256 mod r`, reduced: the same 32 bytes as the host's `[u64; 4]`
// blst_fr limbs. A `device Fr *` over a buffer of host scalars needs no
// conversion pass.
//
// r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

#ifndef MIDNIGHT_METAL_FR_H
#define MIDNIGHT_METAL_FR_H

#include "mont.h"

struct FrParams {
    enum : int { N = 8 };
    enum : uint { INV = 0xffffffffu };
    static MONT_INLINE uint mod(int i) {
        switch (i) {
        case 0: return 0x00000001u;
        case 1: return 0xffffffffu;
        case 2: return 0xfffe5bfeu;
        case 3: return 0x53bda402u;
        case 4: return 0x09a1d805u;
        case 5: return 0x3339d808u;
        case 6: return 0x299d7d48u;
        default: return 0x73eda753u;
        }
    }
    // 2^256 mod r
    static MONT_INLINE uint one(int i) {
        switch (i) {
        case 0: return 0xfffffffeu;
        case 1: return 0x00000001u;
        case 2: return 0x00034802u;
        case 3: return 0x5884b7fau;
        case 4: return 0xecbc4ff5u;
        case 5: return 0x998c4fefu;
        case 6: return 0xacc5056fu;
        default: return 0x1824b159u;
        }
    }
};

typedef mont::Elem<FrParams> Fr;

MONT_INLINE Fr fr_zero() { return mont::zero<FrParams>(); }
MONT_INLINE Fr fr_one() { return mont::one<FrParams>(); }
MONT_INLINE bool fr_is_zero(Fr a) { return mont::is_zero<FrParams>(a); }
MONT_INLINE bool fr_eq(Fr a, Fr b) { return mont::eq<FrParams>(a, b); }
MONT_INLINE bool fr_is_reduced(Fr a) { return mont::is_reduced<FrParams>(a); }
MONT_INLINE Fr fr_add(Fr a, Fr b) { return mont::add<FrParams>(a, b); }
MONT_INLINE Fr fr_sub(Fr a, Fr b) { return mont::sub<FrParams>(a, b); }
MONT_INLINE Fr fr_neg(Fr a) { return mont::neg<FrParams>(a); }
MONT_INLINE Fr fr_dbl(Fr a) { return mont::dbl<FrParams>(a); }
MONT_INLINE Fr fr_mul(Fr a, Fr b) { return mont::mul<FrParams>(a, b); }
MONT_INLINE Fr fr_sqr(Fr a) { return mont::sqr<FrParams>(a); }

#endif // MIDNIGHT_METAL_FR_H

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

// The skew mask of the MSM (src/msm.rs): a fixed public pseudo-random vector
// `r` that depends only on the index. Element i, limb j (64-bit, Montgomery
// limbs used as they are) is the splitmix64 output number 4 i + j + 1 from
// the seed below, limb 3 shifted right by 3 so that every element is below
// the scalar modulus. It is the CUDA crate's `mask_vector` (gpu/src/msm.rs),
// computed here per element instead of sequentially.

#ifndef MIDNIGHT_METAL_MSM_H
#define MIDNIGHT_METAL_MSM_H

#include "fr.h"

namespace msm {

constant ulong MASK_SEED = 0x2545f4914f6cdd1dul;
constant ulong MASK_GAMMA = 0x9e3779b97f4a7c15ul;

// Output number k (from 1) of splitmix64 started at MASK_SEED.
MONT_INLINE ulong splitmix(ulong k) {
    ulong z = MASK_SEED + k * MASK_GAMMA;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ul;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebul;
    return z ^ (z >> 31);
}

MONT_INLINE Fr mask_elem(ulong i) {
    Fr r;
#pragma unroll
    for (int j = 0; j < 4; j++) {
        ulong w = splitmix(4 * i + (ulong)j + 1);
        if (j == 3) w >>= 3;
        r.l[2 * j] = (uint)w;
        r.l[2 * j + 1] = (uint)(w >> 32);
    }
    return r;
}

} // namespace msm

#endif // MIDNIGHT_METAL_MSM_H

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

// Test kernels of the G1 curve code (g1.h) and of the MSM mask (msm.h).

#include "fp.h"
#include "g1.h"
#include "msm.h"

namespace msm_test {

// Operation codes of `msm_test_g1` (tests/msm.rs uses the same numbers).
enum : uint {
    OP_MADD = 0,       // a + b_affine, or a - b_affine with the flag
    OP_ADD = 1,        // a + b
    OP_FROM_AFFINE = 2 // b_affine as XYZZ, negated with the flag
};

} // namespace msm_test

kernel void msm_test_g1(device const g1::Xyzz *a [[buffer(0)]],
                        device const g1::Xyzz *b [[buffer(1)]],
                        device const g1::Affine *b_affine [[buffer(2)]],
                        device const uint *flags [[buffer(3)]],
                        device g1::Xyzz *out [[buffer(4)]],
                        constant uint &op [[buffer(5)]],
                        constant uint &n [[buffer(6)]],
                        uint i [[thread_position_in_grid]]) {
    using namespace msm_test;
    if (i >= n) return;
    g1::Xyzz r = a[i];
    bool flag = flags[i] != 0;
    switch (op) {
    case OP_MADD: g1::add(r, b_affine[i], flag); break;
    case OP_ADD: g1::add(r, b[i]); break;
    default:
        r = g1::from_affine(b_affine[i]);
        g1::cneg(r, flag);
        break;
    }
    out[i] = r;
}

// The mask element `i0 + i` of the MSM (msm.metal), as Montgomery limbs.
kernel void msm_test_mask(device Fr *out [[buffer(0)]],
                          constant uint &i0 [[buffer(1)]],
                          constant uint &n [[buffer(2)]],
                          uint i [[thread_position_in_grid]]) {
    if (i >= n) return;
    out[i] = msm::mask_elem((ulong)i0 + i);
}

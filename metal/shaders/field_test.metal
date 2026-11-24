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

// Test kernels of the field arithmetic (fr.h, fp.h).

#include "fr.h"
#include "fp.h"

namespace field_test {

// Operation codes of `field_test_fr` / `field_test_fp` (the crate's tests use
// the same numbers).
enum : uint {
    OP_ADD = 0,
    OP_SUB = 1,
    OP_MUL = 2,
    OP_SQR = 3,
    OP_NEG = 4,
    OP_DBL = 5,
    OP_IS_REDUCED = 6,
    OP_ONE = 7,
    OP_EQ = 8,
};

template <typename P>
MONT_INLINE mont::Elem<P> flag(bool v) {
    mont::Elem<P> r = mont::zero<P>();
    r.l[0] = v ? 1u : 0u;
    return r;
}

template <typename P>
MONT_INLINE mont::Elem<P> apply(uint op, mont::Elem<P> a, mont::Elem<P> b) {
    switch (op) {
    case OP_ADD: return mont::add<P>(a, b);
    case OP_SUB: return mont::sub<P>(a, b);
    case OP_MUL: return mont::mul<P>(a, b);
    case OP_SQR: return mont::sqr<P>(a);
    case OP_NEG: return mont::neg<P>(a);
    case OP_DBL: return mont::dbl<P>(a);
    case OP_IS_REDUCED: return flag<P>(mont::is_reduced<P>(a));
    case OP_ONE: return mont::one<P>();
    case OP_EQ: return flag<P>(mont::eq<P>(a, b));
    default: return mont::zero<P>();
    }
}

} // namespace field_test

// out[i] = op(a[i], b[i]) for i < n.
template <typename P>
kernel void field_test_kernel(device const mont::Elem<P> *a [[buffer(0)]],
                              device const mont::Elem<P> *b [[buffer(1)]],
                              device mont::Elem<P> *out [[buffer(2)]],
                              constant uint &op [[buffer(3)]],
                              constant uint &n [[buffer(4)]],
                              uint gid [[thread_position_in_grid]]) {
    if (gid >= n) return;
    out[gid] = field_test::apply<P>(op, a[gid], b[gid]);
}

template [[host_name("field_test_fr")]] kernel void field_test_kernel<FrParams>(
    device const Fr *, device const Fr *, device Fr *, constant uint &, constant uint &, uint);
template [[host_name("field_test_fp")]] kernel void field_test_kernel<FpParams>(
    device const Fp *, device const Fp *, device Fp *, constant uint &, constant uint &, uint);

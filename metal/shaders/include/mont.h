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

// Montgomery arithmetic over a prime field of N 32-bit limbs.
//
// An element is `Elem<P>`: N little-endian 32-bit limbs of the Montgomery form
// `a * 2^(32 N) mod p`, reduced (below p). On a little-endian device this is
// bit-identical to the host's N/2 little-endian 64-bit limbs, so a buffer of
// blst limbs is read as it is.
//
// A parameter struct P provides:
//   enum : int  { N = <32-bit limbs> };
//   enum : uint { INV = -p^-1 mod 2^32 };
//   static uint mod(int i);        // limb i of p
//   static uint one(int i);        // limb i of 2^(32 N) mod p (Montgomery one)
// The top limb of p must be below 2^31 - 1 (the "no-carry" condition of the
// CIOS multiplication; both BLS12-381 fields meet it), so that `a + b < 2p`
// fits in N limbs and the products below never carry out of the top limb.
//
// Multiplication is CIOS over 32-bit limbs with 64-bit (`ulong`)
// accumulators, measured faster than the `mulhi`, product-scanning and
// 64-bit-limb variants for both fields.

#ifndef MIDNIGHT_METAL_MONT_H
#define MIDNIGHT_METAL_MONT_H

#include <metal_stdlib>

#define MONT_INLINE inline __attribute__((always_inline))

namespace mont {

template <typename P>
struct Elem {
    uint l[P::N];
};

// ---------------------------------------------------------------------------
// Basic operations

template <typename P>
MONT_INLINE Elem<P> zero() {
    Elem<P> r;
#pragma unroll
    for (int i = 0; i < P::N; i++) r.l[i] = 0;
    return r;
}

// The Montgomery form of 1.
template <typename P>
MONT_INLINE Elem<P> one() {
    Elem<P> r;
#pragma unroll
    for (int i = 0; i < P::N; i++) r.l[i] = P::one(i);
    return r;
}

template <typename P>
MONT_INLINE bool is_zero(Elem<P> a) {
    uint acc = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) acc |= a.l[i];
    return acc == 0;
}

template <typename P>
MONT_INLINE bool eq(Elem<P> a, Elem<P> b) {
    uint acc = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) acc |= a.l[i] ^ b.l[i];
    return acc == 0;
}

// a < p.
template <typename P>
MONT_INLINE bool is_reduced(Elem<P> a) {
    uint borrow = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong d = (ulong)a.l[i] - P::mod(i) - borrow;
        borrow = (uint)(d >> 63);
    }
    return borrow != 0;
}

// t - p if t >= p, else t (t < 2p).
template <typename P>
MONT_INLINE Elem<P> reduce_once(Elem<P> t) {
    Elem<P> d;
    uint borrow = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong x = (ulong)t.l[i] - P::mod(i) - borrow;
        d.l[i] = (uint)x;
        borrow = (uint)(x >> 63);
    }
    return borrow ? t : d;
}

template <typename P>
MONT_INLINE Elem<P> add(Elem<P> a, Elem<P> b) {
    Elem<P> s;
    uint carry = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong x = (ulong)a.l[i] + b.l[i] + carry;
        s.l[i] = (uint)x;
        carry = (uint)(x >> 32);
    }
    // a + b < 2p < 2^(32 N): no carry out of the top limb
    return reduce_once<P>(s);
}

template <typename P>
MONT_INLINE Elem<P> dbl(Elem<P> a) {
    Elem<P> s;
    uint carry = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        s.l[i] = (a.l[i] << 1) | carry;
        carry = a.l[i] >> 31;
    }
    return reduce_once<P>(s);
}

template <typename P>
MONT_INLINE Elem<P> sub(Elem<P> a, Elem<P> b) {
    Elem<P> d;
    uint borrow = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong x = (ulong)a.l[i] - b.l[i] - borrow;
        d.l[i] = (uint)x;
        borrow = (uint)(x >> 63);
    }
    // on a borrow add p back; the mask keeps the code branch free
    uint mask = 0u - borrow;
    uint carry = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong x = (ulong)d.l[i] + (P::mod(i) & mask) + carry;
        d.l[i] = (uint)x;
        carry = (uint)(x >> 32);
    }
    return d;
}

template <typename P>
MONT_INLINE Elem<P> neg(Elem<P> a) {
    Elem<P> d;
    uint borrow = 0;
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong x = (ulong)P::mod(i) - a.l[i] - borrow;
        d.l[i] = (uint)x;
        borrow = (uint)(x >> 63);
    }
    // -0 = 0
    uint mask = is_zero<P>(a) ? 0u : ~0u;
#pragma unroll
    for (int i = 0; i < P::N; i++) d.l[i] &= mask;
    return d;
}

// ---------------------------------------------------------------------------
// Multiplication

// a * b: CIOS, no-carry variant, 32-bit limbs with 64-bit accumulators.
template <typename P>
MONT_INLINE Elem<P> mul(Elem<P> a, Elem<P> b) {
    Elem<P> t = zero<P>();
#pragma unroll
    for (int i = 0; i < P::N; i++) {
        ulong x = (ulong)a.l[0] * b.l[i] + t.l[0];
        uint A = (uint)(x >> 32);
        uint t0 = (uint)x;
        uint m = t0 * (uint)P::INV;
        ulong y = (ulong)m * P::mod(0) + t0;
        uint C = (uint)(y >> 32);
#pragma unroll
        for (int j = 1; j < P::N; j++) {
            x = (ulong)a.l[j] * b.l[i] + t.l[j] + A;
            A = (uint)(x >> 32);
            y = (ulong)m * P::mod(j) + (uint)x + C;
            C = (uint)(y >> 32);
            t.l[j - 1] = (uint)y;
        }
        t.l[P::N - 1] = C + A;
    }
    return reduce_once<P>(t);
}

template <typename P>
MONT_INLINE Elem<P> sqr(Elem<P> a) {
    return mul<P>(a, a);
}

} // namespace mont

#endif // MIDNIGHT_METAL_MONT_H

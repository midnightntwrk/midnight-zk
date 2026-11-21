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

// BLS12-381 G1 points for the MSM: affine and XYZZ coordinates.
//
// The formulas are ported from sppark `ec/xyzz_t.hpp` (Copyright Supranational
// LLC, Apache-2.0, https://github.com/supranational/sppark, commit
// 08033103c14ff3c742e710b9463dde42acc0f058): `add-2008-s` and `madd-2008-s`,
// with `dbl-2008-s-1` and `mdbl-2008-s-1` for equal inputs (EFD, short
// Weierstrass, a = 0).
//
// - `g1::Affine`: `x`, `y` in `Fp`, the bytes of a host `blst_p1_affine`;
//   infinity is all zero.
// - `g1::Xyzz`: `X`, `Y`, `ZZZ`, `ZZ` (sppark's order), the point
//   `(X / ZZ, Y / ZZZ)`; infinity is stored all zero. As Jacobian coordinates
//   the point is `(X * ZZ, Y * ZZZ, ZZ)`. A negation negates `ZZZ`.

#ifndef MIDNIGHT_METAL_G1_H
#define MIDNIGHT_METAL_G1_H

#include "fp.h"

namespace g1 {

// The field multiplication of the curve formulas, out of line: one copy of
// its unrolled body serves every multiplication of a formula, where inlined
// copies overflow the GPU's instruction cache.
static __attribute__((noinline)) Fp mul(Fp a, Fp b) { return fp_mul(a, b); }

struct Affine {
    Fp x;
    Fp y;
};

struct Xyzz {
    Fp X;
    Fp Y;
    Fp ZZZ;
    Fp ZZ;
};

MONT_INLINE Fp fp_cneg(Fp a, bool flag) { return flag ? fp_neg(a) : a; }

MONT_INLINE bool is_inf(Affine a) { return fp_is_zero(a.x) && fp_is_zero(a.y); }

MONT_INLINE bool is_inf(Xyzz p) { return fp_is_zero(p.ZZZ) && fp_is_zero(p.ZZ); }

MONT_INLINE Xyzz inf() {
    Xyzz p;
    p.X = fp_zero();
    p.Y = fp_zero();
    p.ZZZ = fp_zero();
    p.ZZ = fp_zero();
    return p;
}

// sppark `xyzz_t::operator=(const affine_t&)`: ZZZ = ZZ = one, or zero for
// the point at infinity.
MONT_INLINE Xyzz from_affine(Affine a) {
    Xyzz p;
    p.X = a.x;
    p.Y = a.y;
    p.ZZZ = is_inf(a) ? fp_zero() : fp_one();
    p.ZZ = p.ZZZ;
    return p;
}

MONT_INLINE void cneg(thread Xyzz &p, bool neg) { p.ZZZ = fp_cneg(p.ZZZ, neg); }

// p31 += p2 (sppark `xyzz_t::add(const xyzz_t&)`): add-2008-s, doubling
// dbl-2008-s-1 when the points are equal, infinity when they are opposite.
// 12M + 2S for an addition.
MONT_INLINE void add(thread Xyzz &p31, Xyzz p2) {
    if (is_inf(p2)) {
        return;
    } else if (is_inf(p31)) {
        p31 = p2;
        return;
    }

    Fp U = mul(p31.X, p2.ZZ);      // U1 = X1*ZZ2
    Fp S = mul(p31.Y, p2.ZZZ);     // S1 = Y1*ZZZ2
    Fp P = mul(p2.X, p31.ZZ);      // U2 = X2*ZZ1
    Fp R = mul(p2.Y, p31.ZZZ);     // S2 = Y2*ZZZ1
    P = fp_sub(P, U);              // P = U2-U1
    R = fp_sub(R, S);              // R = S2-S1

    if (!fp_is_zero(P)) {          // X1 != X2: add
        Fp PP = mul(P, P);         // PP = P^2
        Fp PPP = mul(P, PP);       // PPP = P*PP
        p31.ZZ = mul(p31.ZZ, PP);
        p31.ZZZ = mul(p31.ZZZ, PPP);
        Fp Q = mul(U, PP);         // Q = U1*PP
        p31.X = mul(R, R);         // R^2
        p31.X = fp_sub(p31.X, PPP);
        p31.X = fp_sub(p31.X, Q);
        p31.X = fp_sub(p31.X, Q);  // X3 = R^2-PPP-2*Q
        Q = fp_sub(Q, p31.X);
        Q = mul(Q, R);             // R*(Q-X3)
        p31.Y = mul(S, PPP);       // S1*PPP
        p31.Y = fp_sub(Q, p31.Y);  // Y3 = R*(Q-X3)-S1*PPP
        p31.ZZ = mul(p31.ZZ, p2.ZZ);       // ZZ3 = ZZ1*ZZ2*PP
        p31.ZZZ = mul(p31.ZZZ, p2.ZZZ);    // ZZZ3 = ZZZ1*ZZZ2*PPP
    } else if (fp_is_zero(R)) {    // X1 == X2, Y1 == Y2: double
        U = fp_dbl(p31.Y);         // U = 2*Y1
        Fp V = mul(U, U);          // V = U^2
        Fp W = mul(U, V);          // W = U*V
        S = mul(p31.X, V);         // S = X1*V
        Fp M = mul(p31.X, p31.X);
        M = fp_add(fp_dbl(M), M);  // M = 3*X1^2 (a = 0)
        p31.X = mul(M, M);
        p31.X = fp_sub(p31.X, S);
        p31.X = fp_sub(p31.X, S);  // X3 = M^2-2*S
        p31.Y = mul(p31.Y, W);     // W*Y1
        S = fp_sub(S, p31.X);
        S = mul(S, M);             // M*(S-X3)
        p31.Y = fp_sub(S, p31.Y);  // Y3 = M*(S-X3)-W*Y1
        p31.ZZ = mul(p31.ZZ, V);      // ZZ3 = V*ZZ1
        p31.ZZZ = mul(p31.ZZZ, W);    // ZZZ3 = W*ZZZ1
    } else {                       // X1 == X2, Y1 == -Y2
        p31 = inf();
    }
}

// p31 += p2, or p31 -= p2 when `subtract` (sppark `xyzz_t::add(const
// affine_t&, bool)`): madd-2008-s, doubling mdbl-2008-s-1 when the points
// are equal, infinity when they are opposite. 8M + 2S for an addition.
MONT_INLINE void add(thread Xyzz &p31, Affine p2, bool subtract) {
    if (is_inf(p2)) {
        return;
    } else if (is_inf(p31)) {
        p31.X = p2.x;
        p31.Y = p2.y;
        p31.ZZZ = fp_one();
        p31.ZZ = fp_one();
        p31.ZZZ = fp_cneg(p31.ZZZ, subtract);
        return;
    }

    Fp R = mul(p2.y, p31.ZZZ);     // S2 = Y2*ZZZ1
    R = fp_cneg(R, subtract);
    R = fp_sub(R, p31.Y);          // R = S2-Y1
    Fp P = mul(p2.x, p31.ZZ);      // U2 = X2*ZZ1
    P = fp_sub(P, p31.X);          // P = U2-X1

    if (!fp_is_zero(P)) {          // X1 != X2: add
        Fp PP = mul(P, P);         // PP = P^2
        Fp PPP = mul(P, PP);       // PPP = P*PP
        p31.ZZ = mul(p31.ZZ, PP);          // ZZ3 = ZZ1*PP
        p31.ZZZ = mul(p31.ZZZ, PPP);       // ZZZ3 = ZZZ1*PPP
        Fp Q = mul(PP, p31.X);     // Q = X1*PP
        p31.X = mul(R, R);         // R^2
        p31.X = fp_sub(p31.X, PPP);
        p31.X = fp_sub(p31.X, Q);
        p31.X = fp_sub(p31.X, Q);  // X3 = R^2-PPP-2*Q
        Q = fp_sub(Q, p31.X);
        Q = mul(Q, R);             // R*(Q-X3)
        p31.Y = mul(p31.Y, PPP);           // Y1*PPP
        p31.Y = fp_sub(Q, p31.Y);  // Y3 = R*(Q-X3)-Y1*PPP
    } else if (fp_is_zero(R)) {    // X1 == X2, Y1 == +-Y2: double p2
        Fp U = fp_dbl(p2.y);       // U = 2*Y1
        p31.ZZ = mul(U, U);        // ZZ3 = V = U^2
        p31.ZZZ = mul(p31.ZZ, U);          // ZZZ3 = W = U*V
        Fp S = mul(p2.x, p31.ZZ);          // S = X1*V
        Fp M = mul(p2.x, p2.x);
        M = fp_add(fp_dbl(M), M);  // M = 3*X1^2 (a = 0)
        p31.X = mul(M, M);
        p31.X = fp_sub(p31.X, S);
        p31.X = fp_sub(p31.X, S);  // X3 = M^2-2*S
        p31.Y = mul(p31.ZZZ, p2.y);        // W*Y1
        S = fp_sub(S, p31.X);
        S = mul(S, M);             // M*(S-X3)
        p31.Y = fp_sub(S, p31.Y);  // Y3 = M*(S-X3)-W*Y1
        p31.ZZZ = fp_cneg(p31.ZZZ, subtract);
    } else {                       // X1 == X2, Y1 == -+Y2
        p31 = inf();
    }
}

} // namespace g1

#endif // MIDNIGHT_METAL_G1_H

// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Scene 3: an MSM with the bucket method, on six terms in a toy group of
// order 61 where point i is the multiple POINTS[i] of a generator G. The
// scene computes every value it shows and checks the result against the
// direct sum.

import { at, clamp01, ease, lerp, sub } from "../stage.js";

const Q = 61; // group order; scalars fit in 6 bits
const C = 3; // window width in bits
const BUCKETS = (1 << C) - 1;
const POINTS = [5, 11, 17, 23, 31, 40];
const SCALARS = [1, 1, 1, 1, 2, 1];
const MASK = [23, 44, 9, 58, 37, 12];

const mod = (v) => ((v % Q) + Q) % Q;
const name = (i) => `P${i}`;
const g = (v) => `[${v}]G`;

function compute() {
  const masked = SCALARS.map((s, i) => mod(s + MASK[i]));
  const digits = masked.map((s) => [s & BUCKETS, s >> C]); // [low, high]
  const windows = [0, 1].map((w) => {
    const members = Array.from({ length: BUCKETS + 1 }, () => []);
    digits.forEach((d, i) => d[w] && members[d[w]].push(i));
    const sums = members.map((m) => mod(m.reduce((acc, i) => acc + POINTS[i], 0)));
    // Running sum from the top bucket down: acc += B_j; sum += acc.
    const sweep = [];
    let acc = 0;
    let sum = 0;
    for (let j = BUCKETS; j >= 1; j--) {
      acc = mod(acc + sums[j]);
      sum = mod(sum + acc);
      sweep.push({ j, acc, sum });
    }
    return { members, sums, sweep, sum };
  });
  const combined = mod((windows[1].sum << C) + windows[0].sum);
  const maskMsm = mod(MASK.reduce((acc, r, i) => acc + r * POINTS[i], 0));
  const result = mod(combined - maskMsm);
  const direct = mod(SCALARS.reduce((acc, s, i) => acc + s * POINTS[i], 0));
  if (result !== direct) throw new Error("MSM scene: the bucket method and the direct sum differ");
  const load = (ds) => {
    const count = new Array(BUCKETS + 1).fill(0);
    ds.forEach((d) => d && count[d]++);
    return Math.max(...count);
  };
  return {
    masked,
    digits,
    windows,
    combined,
    maskMsm,
    result,
    rawLoad: load(SCALARS.map((s) => s & BUCKETS)),
    maskedLoad: Math.max(load(digits.map((d) => d[0])), load(digits.map((d) => d[1]))),
  };
}

const rowY = (i) => 21 + i * 9.2;
const bucketY = (j) => 21 + (j - 1) * 7.7;
const X = { point: 6, multiple: 16.5, s: 26.5, masked: 34.5, low: 43, high: 50, index: 56.5 };
const BUCKET_X = [68.5, 88]; // low window, high window
const BUCKET_W = 18;

export default function build(stage) {
  const m = compute();
  const n = POINTS.length;

  stage.label("terms", 28, 5, "head");
  stage.label("buckets", 78, 5, "head");
  stage.label("P = [p]G", 11, 11.5, "sm muted");
  stage.label("s", X.s, 11.5, "sm muted");
  const headMasked = stage.label("s + r", X.masked, 11.5, "sm muted");
  const headHigh = stage.label("high", X.high, 11.5, "sm muted");
  const headLow = stage.label("low", X.low, 11.5, "sm muted");
  const headBucket = [stage.label("low", BUCKET_X[0], 11.5, "sm muted"), stage.label("high", BUCKET_X[1], 11.5, "sm muted")];

  const rows = POINTS.map((p, i) => ({
    cell: stage.box(X.point, rowY(i), 8.4, 6, { token: "ink", r: 1.2, fill: 0.08 }),
    name: stage.label(name(i), X.point, rowY(i), ""),
    multiple: stage.label(String(p), X.multiple, rowY(i), "mono muted"),
    s: stage.label(String(SCALARS[i]), X.s, rowY(i), "mono"),
    masked: stage.label(String(m.masked[i]), X.masked, rowY(i), "mono"),
    digitBox: [
      stage.box(X.low, rowY(i), 5.8, 6, { token: "device", r: 1.2 }),
      stage.box(X.high, rowY(i), 5.8, 6, { token: "device", r: 1.2 }),
    ],
    digit: [
      stage.label(String(m.digits[i][0]), X.low, rowY(i), "mono"),
      stage.label(String(m.digits[i][1]), X.high, rowY(i), "mono"),
    ],
  }));

  const buckets = [0, 1].map((w) =>
    Array.from({ length: BUCKETS }, (_, k) => ({
      box: stage.box(BUCKET_X[w], bucketY(k + 1), BUCKET_W, 6, { token: "device", r: 1.2 }),
      text: stage.label("", BUCKET_X[w], bucketY(k + 1), ""),
    })),
  );
  const indices = Array.from({ length: BUCKETS }, (_, k) => stage.label(String(k + 1), X.index, bucketY(k + 1), "sm mono muted"));

  // One moving token per term and window.
  const tokens = [0, 1].map(() =>
    POINTS.map((_, i) => ({
      box: stage.box(0, 0, 8.4, 6, { token: "device", r: 1.2, fill: 0.3 }),
      text: stage.label(name(i), 0, 0, ""),
    })),
  );

  const lineA = stage.label("", 50, 77.5, "wrap");
  const lineB = stage.label("", 50, 83.5, "mono");
  const lineC = stage.label("", 50, 89, "mono");
  const lineD = stage.label("", 50, 96.5, "mono");
  const lineE = stage.label("", 50, 104, "mono device");

  const draw = (step, t) => {
    const mask = at(step, t, 1);
    const cut = at(step, t, 2);
    const fill = [at(step, t, 3), at(step, t, 4)];
    const sweep = at(step, t, 5);
    const combine = at(step, t, 6);
    const unmask = at(step, t, 7);

    headMasked.alpha(sub(mask, 0.1, 0.5));
    headHigh.alpha(sub(cut, 0.1, 0.5));
    headLow.alpha(sub(cut, 0.3, 0.7));
    rows.forEach((row, i) => {
      const stagger = i / n;
      row.s.alpha(step >= 1 ? lerp(1, 0.5, sub(mask, 0.5, 1)) : 1);
      row.masked.alpha(sub(mask, 0.15 + stagger * 0.4, 0.55 + stagger * 0.4));
      [1, 0].forEach((w, order) => {
        const shown = sub(cut, 0.1 + order * 0.25 + stagger * 0.3, 0.45 + order * 0.25 + stagger * 0.3);
        const zero = m.digits[i][w] === 0;
        const live = step === 3 + w;
        row.digitBox[w].fill(live ? 0.34 : 0.12).alpha(shown * (zero ? 0.4 : 1));
        row.digit[w].alpha(shown * (zero ? 0.5 : 1));
      });
    });

    // Bucket fill: each token leaves its row and lands in its bucket.
    [0, 1].forEach((w) => {
      const landed = Array.from({ length: BUCKETS + 1 }, () => []);
      tokens[w].forEach((token, i) => {
        const d = m.digits[i][w];
        const p = clamp01((fill[w] - (i / n) * 0.62) / 0.3);
        const moving = p > 0 && p < 1 && d !== 0;
        if (d !== 0 && p >= 1) landed[d].push(i);
        const e = ease(p);
        const x = lerp(X.point, BUCKET_X[w], e);
        const y = lerp(rowY(i), d ? bucketY(d) : rowY(i), e) - Math.sin(Math.PI * e) * 3;
        token.box.pos(x, y).alpha(moving ? 1 : 0);
        token.text.pos(x, y).alpha(moving ? 1 : 0);
      });
      buckets[w].forEach((bucket, k) => {
        const j = k + 1;
        const inside = landed[j];
        const windowShown = step >= 3 + w || (step === 2 && cut > 0.6) ? 1 : 0.4;
        // The running sum passes from bucket 7 down to bucket 1.
        const pass = sweep * BUCKETS - (BUCKETS - j);
        const hot = step === 5 && pass > 0 && pass < 1;
        bucket.box.fill(hot ? 0.45 : inside.length ? 0.24 : 0.05).alpha(windowShown);
        if (step <= 1) {
          // Before any point moves, the cells show how many points each
          // bucket would take: unmasked digits first, masked digits after.
          const maskedView = step === 1 && mask > 0.55;
          const digit = (i) => (maskedView ? m.digits[i][w] : w === 0 ? SCALARS[i] & BUCKETS : SCALARS[i] >> C);
          const load = POINTS.filter((_, i) => digit(i) === j).length;
          bucket.box.fill(load ? 0.1 + 0.07 * load : 0.05).alpha(1);
          bucket.text.text(load ? `${load} ${load === 1 ? "point" : "points"}` : "").alpha(load ? 1 : 0);
          return;
        }
        bucket.text.text(inside.map(name).join(" + ")).alpha(inside.length ? 1 : 0);
      });
      headBucket[w].alpha(step >= 3 + w ? 1 : 0.5);
    });
    indices.forEach((label) => label.alpha(step >= 2 ? 1 : 0.5));

    // Text lines under the table.
    if (step <= 1) {
      lineA
        .text(
          step === 0
            ? `without a mask, ${m.rawLoad} of ${n} points fall into bucket 1`
            : `with this mask, no bucket takes more than ${m.maskedLoad} points`,
        )
        .alpha(step === 0 ? 1 : sub(mask, 0.5, 0.9));
      lineB.text(`r = (${MASK.join(", ")}), public`).alpha(sub(mask, 0.1, 0.5));
    } else if (step === 2) {
      lineA.text(`${m.masked[0]} = ${m.digits[0][1]}·8 + ${m.digits[0][0]}: high digit ${m.digits[0][1]}, low digit ${m.digits[0][0]}`).alpha(sub(cut, 0.3, 0.7));
      lineB.alpha(0);
    } else if (step <= 4) {
      lineA.text(step === 3 ? "each point is added to the bucket of its low digit" : "the same for the high digits").alpha(1);
      lineB.alpha(0);
    } else {
      lineA.text("buckets 7 to 1: acc += bucket, sum += acc").alpha(step === 5 ? 1 : 0);
      const k = Math.min(BUCKETS - 1, Math.floor(sweep * BUCKETS));
      const live = step === 5 && sweep < 1;
      const text = (w, label) => {
        const window = m.windows[w];
        return live
          ? `${label}: bucket ${window.sweep[k].j}, acc ${window.sweep[k].acc}, sum ${window.sweep[k].sum}`
          : `${label} window sum = ${g(window.sum)}`;
      };
      lineB.text(text(0, "low")).alpha(1);
      lineC.text(text(1, "high")).alpha(1);
    }
    if (step < 5) lineC.alpha(0);
    lineD.text(`8·${g(m.windows[1].sum)} + ${g(m.windows[0].sum)} = ${g(m.combined)} = MSM(s + r)`).alpha(sub(combine, 0.2, 0.7));
    lineE.text(`${g(m.combined)} − ${g(m.maskMsm)} = ${g(m.result)} = MSM(s)`).alpha(sub(unmask, 0.2, 0.7));
  };
  // Next and reduced motion stop at every bucket of the running sum.
  draw.beats = { 5: [...Array.from({ length: BUCKETS }, (_, k) => (k + 0.5) / BUCKETS), 1] };
  // The same values as text, for the live region of the player.
  draw.describe = (step, t) => {
    if (step !== 5) return "";
    if (t >= 1) return `Low window sum ${g(m.windows[0].sum)}. High window sum ${g(m.windows[1].sum)}.`;
    const k = Math.min(BUCKETS - 1, Math.floor(t * BUCKETS));
    const [low, high] = [m.windows[0].sweep[k], m.windows[1].sweep[k]];
    return `Bucket ${low.j}. Low window: accumulator ${low.acc}, sum ${low.sum}. High window: accumulator ${high.acc}, sum ${high.sum}.`;
  };
  return draw;
}

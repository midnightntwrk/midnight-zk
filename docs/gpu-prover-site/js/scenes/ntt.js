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
// Scene 2: a radix-2 NTT on 8 points over the integers modulo 17, in the
// order of the stock CPU routine: bit reversal, then butterflies at pair
// distance 1, 2 and 4. The scene computes every value it shows and checks
// the last column against a direct evaluation of the polynomial.

import { at, lerp, sub } from "../stage.js";

const P = 17;
const OMEGA = 2; // order 8 modulo 17
const N = 8;
const LOG_N = 3;
const INPUT = [3, 1, 4, 1, 5, 9, 2, 6];

const mod = (v) => ((v % P) + P) % P;
const pow = (b, e) => {
  let r = 1;
  for (let i = 0; i < e; i++) r = mod(r * b);
  return r;
};
const bitrev = (i) => {
  let r = 0;
  for (let b = 0; b < LOG_N; b++) r |= ((i >> b) & 1) << (LOG_N - 1 - b);
  return r;
};
const SUP = ["⁰", "¹", "²", "³", "⁴", "⁵", "⁶", "⁷"];

/** Columns: input, after bit reversal, after each stage; and the butterflies. */
function compute() {
  const columns = [INPUT.slice()];
  const reversed = INPUT.map((_, i) => INPUT[bitrev(i)]);
  columns.push(reversed);
  const stages = [];
  let cur = reversed;
  for (let chunk = 2; chunk <= N; chunk *= 2) {
    const next = cur.slice();
    const pairs = [];
    for (let start = 0; start < N; start += chunk) {
      for (let i = 0; i < chunk / 2; i++) {
        const e = (i * N) / chunk; // twiddle exponent
        const lo = start + i;
        const hi = lo + chunk / 2;
        const t = mod(cur[hi] * pow(OMEGA, e));
        next[lo] = mod(cur[lo] + t);
        next[hi] = mod(cur[lo] - t);
        pairs.push({ lo, hi, e });
      }
    }
    stages.push(pairs);
    columns.push(next);
    cur = next;
  }
  const direct = INPUT.map((_, i) => {
    const x = pow(OMEGA, i);
    return mod(INPUT.reduce((acc, c, j) => acc + c * pow(x, j), 0));
  });
  if (direct.some((v, i) => v !== cur[i])) throw new Error("NTT scene: the network and the direct evaluation differ");
  return { columns, stages };
}

const COL_X = [14, 32, 50, 68, 86];
const HEADS = ["input", "bit reversal", "stage 1", "stage 2", "stage 3"];
const CELL_W = 9.6;
const CELL_H = 7.2;
const rowY = (i) => 21 + i * 10.6;

export default function build(stage) {
  const { columns, stages } = compute();

  const heads = HEADS.map((text, c) => stage.label(text, COL_X[c], 9.5, "sm head wrap narrow"));
  INPUT.forEach((_, i) => stage.label(`a${i}`, 4.4, rowY(i), "sm mono muted"));
  const outLabels = INPUT.map((_, i) => stage.label(`ω${SUP[i]}`, 95.8, rowY(i), "sm device"));

  // Wires first, so the cells cover their ends.
  const x0 = (c) => COL_X[c] + CELL_W / 2;
  const x1 = (c) => COL_X[c] - CELL_W / 2;
  const swapWires = INPUT.map((_, i) =>
    stage.line(x0(0), rowY(bitrev(i)), x1(1), rowY(i), { token: "device", thick: 0.3 }),
  );
  const stageWires = stages.map((pairs, s) =>
    pairs.flatMap(({ lo, hi }) => [
      stage.line(x0(s + 1), rowY(lo), x1(s + 2), rowY(lo), { token: "device", thick: 0.3 }),
      stage.line(x0(s + 1), rowY(hi), x1(s + 2), rowY(hi), { token: "device", thick: 0.3 }),
      stage.line(x0(s + 1), rowY(hi), x1(s + 2), rowY(lo), { token: "device", thick: 0.3 }),
      stage.line(x0(s + 1), rowY(lo), x1(s + 2), rowY(hi), { token: "device", thick: 0.3 }),
    ]),
  );
  // One butterfly of each stage is drawn heavier, and its arithmetic is
  // written out under the grid: the pair with the largest twiddle exponent.
  const spots = stages.map((pairs) => pairs.reduce((best, pair) => (pair.e > best.e ? pair : best), pairs[0]));
  const spotWires = spots.map(({ lo, hi }, s) => [
    stage.line(x0(s + 1), rowY(lo), x1(s + 2), rowY(lo), { token: "ink", thick: 0.62 }),
    stage.line(x0(s + 1), rowY(hi), x1(s + 2), rowY(hi), { token: "ink", thick: 0.62 }),
    stage.line(x0(s + 1), rowY(hi), x1(s + 2), rowY(lo), { token: "ink", thick: 0.62 }),
    stage.line(x0(s + 1), rowY(lo), x1(s + 2), rowY(hi), { token: "ink", thick: 0.62 }),
  ]);
  const twiddles = stages.map((pairs, s) =>
    pairs.map(({ hi, e }) => stage.label(`×ω${SUP[e]}`, COL_X[s + 1] + 9.2, rowY(hi) - 3.1, "mono chip device")),
  );

  const cells = columns.map((values, c) =>
    values.map((v, i) => ({
      box: stage.box(COL_X[c], rowY(i), CELL_W, CELL_H, { token: "device", r: 1.3 }),
      text: stage.label(String(v), COL_X[c], rowY(i), "mono"),
    })),
  );

  const note = stage.label("", 50, 105.5, "sm wrap");

  return (step, t) => {
    cells.forEach((column, c) => {
      const p = c === 0 ? 1 : at(step, t, c);
      const shown = c === 0 ? 1 : sub(p, 0.45, 0.85);
      const current = step === c || (step === 5 && c === 4);
      column.forEach(({ box, text }) => {
        box.color(current ? "device" : "ink").fill(current ? lerp(0.08, 0.3, shown) : 0.06).alpha(shown * (current ? 1 : 0.5));
        text.alpha(shown * (current || step < c ? 1 : 0.72));
      });
      heads[c].alpha(c === 0 ? 1 : Math.max(0.35, shown)).tone("device", current);
    });
    if (step === 5) heads[4].text("p(ω^i)");
    else heads[4].text("stage 3");

    const swap = at(step, t, 1);
    swapWires.forEach((wire) => wire.grow(sub(swap, 0, 0.55)).color(step === 1 ? "device" : "muted").alpha(swap > 0 ? (step === 1 ? 1 : 0.7) : 0));
    stageWires.forEach((wires, s) => {
      const p = at(step, t, s + 2);
      const active = step === s + 2;
      wires.forEach((wire, k) => {
        // The two straight wires first, then the two crossing wires.
        const late = k % 4 >= 2;
        wire.grow(sub(p, late ? 0.18 : 0, late ? 0.6 : 0.42)).color(active ? "device" : "muted").alpha(p > 0 ? 0.7 : 0);
      });
      spotWires[s].forEach((wire, k) => wire.grow(sub(p, k >= 2 ? 0.18 : 0, k >= 2 ? 0.6 : 0.42)).alpha(active && p > 0 ? 1 : 0));
      // A twiddle of 1 needs no label.
      twiddles[s].forEach((label, k) => label.alpha(active && stages[s][k].e > 0 ? sub(p, 0.2, 0.5) : 0));
    });

    const done = at(step, t, 5);
    outLabels.forEach((label) => label.alpha(sub(done, 0.1, 0.6)));
    const last = columns[4];
    if (step >= 2 && step <= 4) {
      const s = step - 2;
      const { lo, hi, e } = spots[s];
      const a = columns[s + 1][lo];
      const b = columns[s + 1][hi];
      const w = pow(OMEGA, e);
      note
        .text(
          `rows ${lo} and ${hi}: a = ${a}, b = ${b}, w = ${w}. a + w·b = ${columns[s + 2][lo]} and a − w·b = ${columns[s + 2][hi]}, modulo 17`,
        )
        .alpha(sub(at(step, t, step), 0.5, 0.9));
    } else {
      note.text(`row 1 holds p(ω) = p(2) = ${last[1]}; all 8 rows equal a direct evaluation`).alpha(sub(done, 0.4, 0.9));
    }
  };
}

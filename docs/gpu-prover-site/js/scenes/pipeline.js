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
// Scene 1: the proving pipeline. Thirteen rows from the instances to the
// verified proof, a CPU lane and a device lane, a mark at every random draw
// and a chip for the challenges that the transcript returns after a row.

import { at, ease, lerp, sub } from "../stage.js";

const CPU_X = 26.5;
const GPU_X = 73.5;
const BOX_W = 43;
const BOX_H = 5.8;
const TOP = 14;
const ROW = 7.7;
const GAP = 4.7; // extra space under a row that returns challenges

// cpu / gpu: the work of the row in each lane. rng: the row can draw random
// values. challenge: what the transcript returns after the row.
const ROWS = [
  { cpu: "Key, instances", gpu: "iNTTs" },
  { cpu: "Synthesis", rng: true },
  { cpu: "Multiplicities", rng: true },
  { gpu: "MSMs: group 1", challenge: "θ β γ, trash" },
  { cpu: "Argument columns", rng: true },
  { gpu: "MSMs: group 2", challenge: "y" },
  { gpu: "iNTTs, quotient" },
  { cpu: "Limbs, blinding", gpu: "MSMs: limbs", rng: true, challenge: "x" },
  { cpu: "Evaluations at x", challenge: "x₁ x₂" },
  { cpu: "Build f", gpu: "MSM: commit f", challenge: "x₃" },
  { cpu: "Evaluations at z", challenge: "x₄" },
  { cpu: "Opening quotient", gpu: "MSM → π" },
  { cpu: "Verify, return proof" },
];

// Row centres: a row that returns challenges leaves a gap for their chip.
const ROW_Y = [];
ROWS.reduce((yy, row) => {
  ROW_Y.push(yy);
  return yy + ROW + (row.challenge ? GAP : 0);
}, TOP);

export default function build(stage) {
  const y = (i) => ROW_Y[i];

  stage.bar(2.5, 8.5, 47, 129, { token: "cpu", fill: 0.07 });
  stage.bar(50.5, 8.5, 47, 129, { token: "device", fill: 0.07 });
  stage.label("CPU", CPU_X, 5, "head cpu");
  stage.label("GPU", GPU_X, 5, "head device");

  // The proof state enters a row at its first box and leaves at its last.
  const enter = ROWS.map((row, i) => ({ x: row.cpu ? CPU_X : GPU_X, y: y(i) }));
  const leave = ROWS.map((row, i) => ({ x: row.gpu ? GPU_X : CPU_X, y: y(i) }));
  const links = [];
  for (let i = 1; i < ROWS.length; i++) {
    const a = leave[i - 1];
    const b = enter[i];
    links.push(stage.line(a.x, a.y + BOX_H / 2, b.x, b.y - BOX_H / 2, { token: "faint", thick: 0.34 }));
  }

  const rows = ROWS.map((row, i) => {
    const out = { row };
    if (row.cpu) {
      out.cpu = stage.box(CPU_X, y(i), BOX_W, BOX_H, { token: "cpu" });
      out.cpuLabel = stage.label(row.cpu, CPU_X + (row.rng ? 2.5 : 0), y(i), "");
    }
    if (row.gpu) {
      out.gpu = stage.box(GPU_X, y(i), BOX_W, BOX_H, { token: "device" });
      out.gpuLabel = stage.label(row.gpu, GPU_X, y(i), "");
    }
    if (row.cpu && row.gpu) {
      out.hop = stage.line(CPU_X + BOX_W / 2, y(i), GPU_X - BOX_W / 2, y(i), {
        token: "device",
        thick: 0.34,
        head: true,
      });
    }
    if (row.rng) {
      out.rngHalo = stage.diamond(CPU_X - BOX_W / 2 + 4.2, y(i), 3, { token: "rng" });
      out.rng = stage.diamond(CPU_X - BOX_W / 2 + 4.2, y(i), 1.55, { token: "rng" });
    }
    if (row.challenge) {
      // The chip sits in the gap under its row, between the lanes.
      out.chip = stage.label(`transcript: ${row.challenge}`, 50, y(i) + (ROW + GAP) / 2, "mono sm chip");
    }
    return out;
  });

  const token = stage.dot(CPU_X, y(0) - BOX_H / 2, 1.2, { token: "ink" });

  return (step, t) => {
    rows.forEach((r, i) => {
      const p = at(step, t, i);
      const active = step === i;
      const arrive = sub(p, 0.3, 0.55);
      const tone = active ? lerp(0.1, 0.42, arrive) : p >= 1 ? 0.2 : 0.04;
      const edge = p > 0 ? lerp(0.45, 1, arrive) : 0.45;
      if (r.cpu) {
        r.cpu.fill(tone).alpha(edge);
        r.cpuLabel.alpha(p > 0 ? lerp(0.62, 1, arrive) : 0.62);
      }
      if (r.gpu) {
        const late = r.cpu ? sub(p, 0.62, 0.86) : arrive;
        r.gpu.fill(active ? lerp(0.1, 0.42, late) : p >= 1 ? 0.2 : 0.04).alpha(p > 0 ? lerp(0.45, 1, late) : 0.45);
        r.gpuLabel.alpha(p > 0 ? lerp(0.62, 1, late) : 0.62);
      }
      if (r.hop) r.hop.grow(sub(p, 0.52, 0.78)).alpha(p > 0.52 ? 1 : 0);
      if (r.rng) {
        const pulse = active ? Math.sin(Math.PI * sub(p, 0.4, 0.95)) : 0;
        r.rng.alpha(p > 0 ? lerp(0.75, 1, arrive) : 0.75);
        r.rngHalo.alpha(0.3 * pulse).scale(0.6 + 0.6 * sub(p, 0.4, 0.95));
      }
      if (r.chip) r.chip.alpha(sub(p, 0.82, 1));
      if (i > 0) links[i - 1].color(p > 0 ? "ink" : "faint").alpha(p > 0 ? 0.75 : 0.5);
    });

    // The marker moves along the link into the row of the current step.
    const to = enter[step];
    const a = step === 0 ? { x: to.x, y: to.y - BOX_H / 2 - 2 } : { x: leave[step - 1].x, y: leave[step - 1].y + BOX_H / 2 };
    const b = { x: to.x, y: to.y - BOX_H / 2 };
    const move = ease(t / 0.32);
    // After the move the marker rests at the left edge of the current row.
    const rest = sub(t, 0.36, 0.6);
    token.pos(lerp(lerp(a.x, b.x, move), 1.4, rest), lerp(lerp(a.y, b.y, move), to.y, rest)).alpha(1);
  };
}

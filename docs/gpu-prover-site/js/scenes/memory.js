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
// Scene 4: host and device memory during one request. The wipe line zeroes
// each witness-dependent buffer as it passes and stops above the public key
// copies. Then the buffers are freed, the two resident policies follow, and
// last the eviction under memory pressure. Block heights are not to scale.

import { at, lerp, sub } from "../stage.js";

const HOST = { x: 4, w: 43 };
const DEV = { x: 53, w: 43 };
const TOP = 14;
const BOTTOM = 92;

// Host blocks, from the top. `secret` marks witness-dependent data.
const HOST_BLOCKS = {
  srs: { y: 16, h: 10, text: "SRS, read-only" },
  key: { y: 28, h: 15, text: "Proving key" },
  prover: { y: 45, h: 9.5, text: "Prover vectors", secret: true },
  staging: { y: 56, h: 6.6, text: "MSM staging, s + r", secret: true },
  sums: { y: 64.1, h: 6.6, text: "Partial bucket sums", secret: true },
  coefficients: { y: 73.6, h: 5, text: "h(X) and its limbs", secret: true },
  points: { y: 79.4, h: 5, text: "Points, NTT outputs", secret: true },
  result: { y: 85.2, h: 5, text: "Counters" },
};
// Device blocks, stacked from the bottom.
const DEV_BLOCKS = {
  resident: { y: 58, h: 32, text: "Key copies" },
  cosets: { y: 37, h: 19, text: "Advice cosets", secret: true },
  numerator: { y: 26, h: 9, text: "Numerator, scratch", secret: true },
  msm: { y: 16, h: 8, text: "MSM buffers", secret: true },
};

export default function build(stage) {
  stage.label("Host memory", HOST.x + HOST.w / 2, 7.5, "head cpu");
  stage.label("Device memory", DEV.x + DEV.w / 2, 7.5, "head device");
  stage.box(HOST.x + HOST.w / 2, (TOP + BOTTOM) / 2, HOST.w, BOTTOM - TOP, { token: "cpu", fill: 0.05, r: 2, line: 0.36 });
  stage.box(DEV.x + DEV.w / 2, (TOP + BOTTOM) / 2, DEV.w, BOTTOM - TOP, { token: "device", fill: 0.05, r: 2, line: 0.36 });

  const block = (side, spec) => {
    const token = spec.secret ? "secret" : "ink";
    return {
      spec,
      side,
      bar: stage.bar(side.x + 2, spec.y, side.w - 4, spec.h, { token, fill: 0.26 }),
      edge: stage.box(side.x + side.w / 2, spec.y + spec.h / 2, side.w - 4, spec.h, { token, fill: 0, r: 0.6, line: 0.34 }),
      text: stage.label(spec.text, side.x + side.w / 2, spec.y + spec.h / 2, ""),
    };
  };
  const host = Object.fromEntries(Object.entries(HOST_BLOCKS).map(([k, spec]) => [k, block(HOST, spec)]));
  const dev = Object.fromEntries(Object.entries(DEV_BLOCKS).map(([k, spec]) => [k, block(DEV, spec)]));

  const other = {
    bar: stage.bar(DEV.x + 2, 16, DEV.w - 4, 1, { token: "faint", fill: 0.55 }),
    text: stage.label("Another program", DEV.x + DEV.w / 2, 30, ""),
  };
  const need = stage.box(DEV.x + DEV.w / 2, 53, DEV.w - 2, 76, { token: "device", fill: 0, r: 1, line: 0.5 });
  const needText = stage.label("computed need", DEV.x + DEV.w / 2, 53, "sm device");

  const gap = (y) => [HOST.x + HOST.w + 0.6, y, DEV.x - 0.6, y];
  const upKey = stage.line(...gap(36), { token: "ink", thick: 0.5, head: true });
  const upWitness = stage.line(...gap(59), { token: "secret", thick: 0.5, head: true });
  const [sx1, sy1, sx2, sy2] = gap(67.4);
  const downSums = stage.line(sx2, sy2, sx1, sy1, { token: "secret", thick: 0.5, head: true });
  const [x1, y1, x2, y2] = gap(82);
  const down = stage.line(x2, y2, x1, y1, { token: "device", thick: 0.5, head: true });
  // One wipe line per side: over the device buffers, and over host staging.
  const wipeDev = stage.bar(0, 0, 1, 1, { token: "ink", fill: 0.95 });
  const wipeHost = stage.bar(0, 0, 1, 1, { token: "ink", fill: 0.95 });

  const status = stage.label("", 50, 98.5, "head");
  const status2 = stage.label("", 50, 105, "sm muted wrap");

  /** Draws a block: `amount` of it is filled, `zero` turns it into zeros. */
  const paint = (b, { amount = 1, zero = 0, alpha = 1, ghost = false, text }) => {
    const { spec, side } = b;
    const h = spec.h * amount;
    b.bar.span(side.x + 2, spec.y + spec.h - h, side.w - 4, h).fill(ghost ? 0.05 : lerp(0.26, 0.03, zero)).alpha(alpha);
    b.edge.alpha(alpha * (ghost ? 0.5 : amount > 0.02 ? 1 : 0));
    b.text.text(text ?? (zero > 0.6 ? "0 0 0 0 0 0" : spec.text)).alpha(alpha * (amount > 0.5 || ghost ? 1 : 0)).tone("mono", zero > 0.6 && !text);
  };
  /** How far the line at height `y` has passed through a block, 0 to 1. */
  const passed = (b, y) => Math.min(1, Math.max(0, (y - b.spec.y) / b.spec.h));

  const STEP = { idle: 0, admit: 1, msm: 2, quotient: 3, read: 4, zero: 5, free: 6, evictPolicy: 7, keepPolicy: 8, pressure: 9 };
  const DEV_TOP = DEV_BLOCKS.msm.y;
  const DEV_END = DEV_BLOCKS.cosets.y + DEV_BLOCKS.cosets.h; // above the key copies

  return (step, t) => {
    const msm = at(step, t, STEP.msm);
    const quotient = at(step, t, STEP.quotient);
    const read = at(step, t, STEP.read);
    const zero = at(step, t, STEP.zero);
    const free = at(step, t, STEP.free);
    const evicted = at(step, t, STEP.evictPolicy);
    const kept = at(step, t, STEP.keepPolicy);
    const pressure = at(step, t, STEP.pressure);

    paint(host.srs, {});
    paint(host.key, {});

    // Key copies: uploaded during the quotient, after the proof cosets and
    // before the numerator is allocated. Freed
    // before the reply by default, kept by the other policy, evicted under
    // pressure.
    let resident = sub(quotient, 0.4, 0.68);
    let residentText;
    if (step === STEP.evictPolicy) resident = 1 - sub(evicted, 0.2, 0.7);
    if (step === STEP.keepPolicy) {
      resident = sub(kept, 0.1, 0.5);
      residentText = "Key copies, kept";
    }
    if (step === STEP.pressure) {
      resident = 1 - sub(pressure, 0.5, 0.8);
      residentText = "Key copies, kept";
    }
    if (step < STEP.quotient || resident < 0.03) {
      paint(dev.resident, { ghost: true, text: step <= STEP.quotient ? "No key copies" : "freed" });
    } else {
      paint(dev.resident, { amount: resident, text: residentText });
    }

    // Witness-dependent buffers exist from their first use until they are
    // freed. The MSM buffers come first, with the commitments.
    const live = step >= STEP.msm && step <= STEP.free;
    const lineY = lerp(DEV_TOP - 1, DEV_END, sub(zero, 0.05, 0.9));
    // The host line passes the staging vector and the quotient buffers (h(X)
    // and its limbs), which the feature `gpu` keeps in erasing owners.
    const hostLineY = lerp(host.staging.spec.y - 1, host.coefficients.spec.y + host.coefficients.spec.h, sub(zero, 0.05, 0.9));
    const gone = 1 - sub(free, 0.15, 0.7);
    const z = (b, y) => (step > STEP.zero ? 1 : step === STEP.zero ? passed(b, y) : 0);
    paint(host.prover, { alpha: live ? sub(msm, 0, 0.2) * gone : 0 });
    paint(host.staging, { alpha: live ? sub(msm, 0.05, 0.25) * gone : 0, zero: z(host.staging, hostLineY) });
    paint(dev.msm, { amount: sub(msm, 0.25, 0.5), alpha: live ? gone : 0, zero: z(dev.msm, lineY) });
    paint(dev.cosets, { amount: sub(quotient, 0.04, 0.32), alpha: live ? gone : 0, zero: z(dev.cosets, lineY) });
    paint(dev.numerator, { amount: sub(quotient, 0.72, 0.95), alpha: live ? gone : 0, zero: z(dev.numerator, lineY) });

    // The partial bucket sums of an MSM are on the host only until the MSM
    // has accumulated them. They are zeroed inside this step.
    const sumsShown = step === STEP.msm ? sub(msm, 0.5, 0.62) * (1 - sub(msm, 0.9, 1)) : 0;
    paint(host.sums, { alpha: sumsShown, zero: sub(msm, 0.72, 0.84) });
    // The final points stay with the prover, as on the CPU path.
    paint(host.points, { alpha: live ? sub(msm, 0.82, 0.96) * gone : 0 });
    const back = step >= STEP.read && step <= STEP.free ? sub(read, 0.4, 0.8) * gone : 0;
    paint(host.coefficients, { alpha: back, zero: z(host.coefficients, hostLineY) });
    paint(host.result, { alpha: back });

    upWitness.grow(sub(msm, 0.15, 0.4)).alpha(step === STEP.msm && msm < 0.6 ? 1 : 0);
    downSums.grow(sub(msm, 0.45, 0.6)).alpha(step === STEP.msm && msm > 0.45 && msm < 0.9 ? 1 : 0);
    upKey.grow(sub(quotient, 0.34, 0.5)).alpha(step === STEP.quotient && quotient > 0.34 && quotient < 0.72 ? 1 : 0);
    down.grow(sub(read, 0.05, 0.45)).alpha(step === STEP.read ? 1 : 0);

    const sweeping = step === STEP.zero && zero > 0.05 && zero < 0.9;
    wipeDev.span(DEV.x + 1, lineY, DEV.w - 2, 0.8).alpha(sweeping ? 1 : 0);
    wipeHost.span(HOST.x + 1, hostLineY, HOST.w - 2, 0.8).alpha(sweeping ? 1 : 0);

    // Admission outline, and the other program of the last step.
    const admit = at(step, t, STEP.admit);
    let needAlpha = step === STEP.admit ? sub(admit, 0.1, 0.5) : 0;
    let needTop = 15;
    let needHeight = 76;
    let shrink = 0;
    if (step === STEP.pressure) {
      shrink = sub(pressure, 0.6, 0.85);
      needAlpha = sub(pressure, 0.25, 0.45);
      needHeight = lerp(52, 22, shrink);
      needTop = lerp(15, 39, sub(pressure, 0.1, 0.3)) + lerp(0, 30, shrink);
    }
    need.pos(DEV.x + DEV.w / 2, needTop + needHeight / 2).scale(1, needHeight / 76).alpha(needAlpha);
    needText
      .pos(DEV.x + DEV.w / 2, step === STEP.pressure ? lerp(46, 64, shrink) : 30)
      .alpha(needAlpha)
      .text(step === STEP.pressure ? (shrink > 0.5 ? "smaller estimate" : "estimate for the next proof") : "estimate");
    const grown = step === STEP.pressure ? sub(pressure, 0, 0.25) : 0;
    other.bar.span(DEV.x + 2, 16, DEV.w - 4, 21 * grown).alpha(step === STEP.pressure ? 1 : 0);
    other.text.pos(DEV.x + DEV.w / 2, 26.5).alpha(step === STEP.pressure ? sub(pressure, 0.15, 0.3) : 0);

    const lines = [
      ["Idle between requests", "host: SRS and proving key"],
      ["The estimate fits in the free memory", "the key is registered on the host; nothing is uploaded yet"],
      [
        msm < 0.7 ? "Commitment MSMs" : "Bucket sums zeroed on the host",
        msm < 0.7 ? "masked scalars go up, partial bucket sums come back" : "after the host adds them up; the points stay with the prover",
      ],
      [
        quotient < 0.34 ? "Quotient: proof cosets first" : quotient < 0.7 ? "Then the key cosets it needs" : "Then numerator and scratch",
        quotient < 0.34 ? "built on the device from the witness" : quotient < 0.7 ? "public: reused, or uploaded from the host" : "evaluate, divide, extended inverse transform",
      ],
      ["Readback", "quotient coefficients and counters; no extended-domain vector"],
      [zero < 0.9 ? "Overwriting with zeros" : "Zeroed", "device buffers, host staging, h(X) and its limbs; key copies untouched"],
      [free < 0.7 ? "Freeing the zeroed buffers" : "Freed", "before the daemon takes the next request"],
      ["Default policy: free the key copies", "before each reply; the next request uploads them again"],
      ["The other policy, keep: the copies stay", "later requests reuse the uploads"],
      [
        pressure < 0.5 ? "Short, also after the wait" : pressure < 0.82 ? "Evicting key copies" : "Key copies evicted",
        pressure < 0.5 ? "another program holds device memory" : pressure < 0.82 ? "the quotient moves to the CPU" : "the smaller estimate fits: MSM and base-domain NTT on the device",
      ],
    ];
    status.text(lines[step][0]);
    status2.text(lines[step][1]);
  };
}

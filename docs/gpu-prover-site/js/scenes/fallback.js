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
// Scene 5: the fallback path, as three figures that share this module. The
// figure names its part with data-band: one hook call that declines, the
// admission ladder, or a client that cannot reach the daemon.

import { at, lerp, sub } from "../stage.js";

const RUNGS = [
  { name: "gpu", note: "fits" },
  { name: "wait", note: "recheck" },
  { name: "evict", note: "smaller need" },
  { name: "cpu", note: "still short" },
];
// Per ladder step, as shares of the device memory: what another program
// holds and what the daemon's own resident key copies hold.
// The first frame is a request that fits. The next two follow a request
// that is short until the evict step lowers its need. The last frame is a
// device where even the smaller need is short.
const LADDER = [
  { other: 0.12, own: 0.3, need: 0.5 },
  { other: 0.62, own: 0.3, need: 0.5 },
  { other: 0.62, own: 0, need: 0.2 },
  { other: 0.9, own: 0, need: 0.2 },
];
const GAUGE = { x: 8, w: 84, y: 47.6, h: 3.2 };

// Per part: its index, the first of its steps in the full sequence, and the
// top of its strip in the shared coordinates.
const PARTS = { hook: { index: 0, first: 0, top: 3 }, ladder: { index: 1, first: 3, top: 37.5 }, client: { index: 2, first: 7, top: 77 } };

/** The stage with every y moved up by `top`, so one part fills the stage. */
function strip(stage, top) {
  const fix = (item) => {
    const pos = item.pos.bind(item);
    item.pos = (x, y) => pos(x, y - top);
    if (item.span) {
      const span = item.span;
      item.span = (x, y, w, h) => span(x, y - top, w, h);
    }
    return item;
  };
  return {
    box: (cx, cy, ...rest) => fix(stage.box(cx, cy - top, ...rest)),
    bar: (x, y, ...rest) => fix(stage.bar(x, y - top, ...rest)),
    dot: (cx, cy, ...rest) => fix(stage.dot(cx, cy - top, ...rest)),
    line: (x1, y1, x2, y2, opts) => fix(stage.line(x1, y1 - top, x2, y2 - top, opts)),
    label: (text, x, y, cls) => fix(stage.label(text, x, y - top, cls)),
  };
}

export default function build(real) {
  const part = PARTS[real.host.closest("figure").dataset.band] ?? PARTS.hook;
  const stage = strip(real, part.top);
  const band = [[], [], []];
  const reg = (b, item) => {
    band[b].push(item);
    return item;
  };

  // Band A: one hook call.
  reg(0, stage.label("One hook call", 4, 6.5, "head l"));
  const prover = reg(0, stage.box(14, 22, 20, 8, { token: "cpu" }));
  reg(0, stage.label("prover", 14, 22, ""));
  const hook = reg(0, stage.box(42, 22, 14, 8, { token: "ink", fill: 0.08 }));
  reg(0, stage.label("hook", 42, 22, ""));
  const kernel = reg(0, stage.box(80, 13.5, 30, 8, { token: "device" }));
  const kernelText = reg(0, stage.label("GPU kernel", 80, 13.5, ""));
  const routine = reg(0, stage.box(80, 30.5, 30, 8, { token: "cpu" }));
  reg(0, stage.label("CPU routine", 80, 30.5, ""));
  const toHook = reg(0, stage.line(24.5, 22, 34.5, 22, { token: "ink", thick: 0.4, head: true }));
  const toKernel = reg(0, stage.line(49.5, 20.5, 64.5, 14.5, { token: "device", thick: 0.4, head: true }));
  const toRoutine = reg(0, stage.line(49.5, 23.5, 64.5, 29.5, { token: "cpu", thick: 0.4, head: true }));
  const crossA = [
    reg(0, stage.line(58.5, 15.2, 62.5, 19.2, { token: "ink", thick: 0.6 })),
    reg(0, stage.line(58.5, 19.2, 62.5, 15.2, { token: "ink", thick: 0.6 })),
  ];
  const input = reg(0, stage.label("input unchanged", 42, 30.5, "sm muted"));
  const count = reg(0, stage.label("declines: 0", 42, 35, "sm mono"));
  const same = reg(0, stage.label("stock value", 14, 30.5, "sm cpu"));
  const dot = stage.dot(0, 0, 1.2, { token: "ink" });

  // Band B: the admission ladder.
  reg(1, stage.label("Admission ladder", 4, 40.4, "head l"));
  reg(1, stage.bar(GAUGE.x, GAUGE.y, GAUGE.w, GAUGE.h, { token: "device", fill: 0.22 }));
  const otherBar = reg(1, stage.bar(0, 0, 1, 1, { token: "faint", fill: 0.8 }));
  const ownBar = reg(1, stage.bar(0, 0, 1, 1, { token: "ink", fill: 0.45 }));
  const ownText = reg(1, stage.label("key copies", 0, 0, "sm"));
  const verdict = reg(1, stage.label("", 50, 74.2, "sm mono wrap"));
  const freeEnd = reg(1, stage.bar(0, 0, 1, 1, { token: "device", fill: 1 }));
  const needBar = reg(1, stage.bar(0, 0, 1, 1, { token: "ink", fill: 0.85 }));
  const needTip = reg(1, stage.bar(0, 0, 1, 1, { token: "ink", fill: 0.85 }));
  const needText = reg(1, stage.label("need", 0, 0, "sm l"));
  const otherText = reg(1, stage.label("other user", 0, 0, "sm r muted"));
  reg(1, stage.label("free", GAUGE.x, GAUGE.y - 2.6, "sm l device"));
  const rungs = RUNGS.map((rung, i) => {
    const x = 14 + i * 24;
    return {
      box: reg(1, stage.box(x, 62.6, 20, 7.4, { token: i < 3 ? "device" : "cpu" })),
      name: reg(1, stage.label(rung.name, x, 62.6, "mono")),
      note: reg(1, stage.label(rung.note, x, 69, "sm muted")),
    };
  });
  const arrows = [0, 1, 2].map((i) => reg(1, stage.line(24.4 + i * 24, 62.6, 27.6 + i * 24, 62.6, { token: "faint", thick: 0.4 })));

  // Band C: client, daemon and breaker.
  reg(2, stage.label("Client and daemon", 4, 80.5, "head l"));
  const client = reg(2, stage.box(13, 92, 18, 8, { token: "cpu" }));
  reg(2, stage.label("client", 13, 92, ""));
  const daemon = reg(2, stage.box(50, 88, 22, 7.5, { token: "cpu" }));
  reg(2, stage.label("daemon", 50, 88, ""));
  const local = reg(2, stage.box(50, 101, 22, 7.5, { token: "cpu" }));
  reg(2, stage.label("CPU prover", 50, 101, ""));
  const toDaemon = reg(2, stage.line(22.5, 90.5, 38.5, 88.3, { token: "ink", thick: 0.4, head: true }));
  const toLocal = reg(2, stage.line(22.5, 93.5, 38.5, 100.5, { token: "cpu", thick: 0.4, head: true }));
  const crossC = [
    reg(2, stage.line(28.5, 87.2, 32.5, 91.2, { token: "ink", thick: 0.6 })),
    reg(2, stage.line(28.5, 91.2, 32.5, 87.2, { token: "ink", thick: 0.6 })),
  ];
  const verify = reg(2, stage.box(84, 101, 22, 7.5, { token: "ink", fill: 0.08 }));
  const verifyText = reg(2, stage.label("verify", 84, 101, ""));
  const toVerify = reg(2, stage.line(61.5, 101, 72.5, 101, { token: "ink", thick: 0.4, head: true }));
  const daemonVerify = reg(2, stage.line(61.5, 89.5, 75, 97, { token: "ink", thick: 0.4, head: true }));
  const fails = [0, 1, 2].map((i) => ({
    ring: reg(2, stage.dot(77 + i * 5, 86.5, 1.7, { token: "faint" })),
    core: reg(2, stage.dot(77 + i * 5, 86.5, 1.15, { token: "ink" })),
  }));
  const breaker = reg(2, stage.label("breaker: closed", 82, 91.5, "sm mono"));
  const final = stage.label("", 50, 109, "sm wrap");

  return (own, t) => {
    const step = own + part.first;
    const dim = (b) => (b === part.index ? 1 : 0);

    // Band A.
    const call = at(step, t, 0);
    const decline = at(step, t, 1);
    const cpu = at(step, t, 2);
    const a = dim(0);
    band[0].forEach((item) => item.alpha(a));
    prover.fill(step === 0 ? 0.36 : 0.16);
    hook.fill(step <= 2 ? lerp(0.08, 0.22, sub(call, 0.3, 0.6)) : 0.08);
    toHook.grow(sub(call, 0.05, 0.4));
    toKernel.grow(sub(call, 0.45, 0.85)).alpha(a * lerp(1, 0.35, sub(decline, 0.3, 0.6)));
    const crossed = sub(decline, 0.2, 0.5);
    crossA.forEach((line) => line.grow(crossed).alpha(crossed > 0 ? a : 0));
    kernel.fill(lerp(0.16, 0.04, crossed)).alpha(a * lerp(1, 0.55, crossed));
    kernelText.alpha(a * lerp(1, 0.6, crossed));
    input.alpha(a * sub(decline, 0.5, 0.9));
    count.text(`declines: ${decline > 0.5 ? 1 : 0}`).alpha(a * (step >= 1 ? 1 : 0.5));
    toRoutine.grow(sub(cpu, 0.05, 0.4)).alpha(cpu > 0.05 ? a : 0);
    routine.fill(step === 2 ? lerp(0.16, 0.4, sub(cpu, 0.3, 0.6)) : step > 2 ? 0.22 : 0.08).alpha(a * (step >= 2 ? 1 : 0.5));
    same.alpha(a * sub(cpu, 0.75, 1));
    // The value travels back from the CPU routine to the prover.
    const back = sub(cpu, 0.55, 0.95);
    dot
      .color("cpu")
      .pos(lerp(64.5, 24.5, back), lerp(29.5, 23.2, back))
      .alpha(step === 2 && cpu > 0.55 && cpu < 0.97 ? 1 : 0);

    // Band B.
    const b = dim(1);
    band[1].forEach((item) => item.alpha(b));
    const li = Math.min(3, Math.max(0, step - 3));
    const lp = step >= 3 && step <= 6 ? t : step > 6 ? 1 : 0;
    const from = LADDER[Math.max(0, li - 1)];
    const to = LADDER[li];
    const k = sub(lp, 0.05, 0.5);
    const otherShare = step < 3 ? LADDER[0].other : lerp(li === 0 ? to.other : from.other, to.other, k);
    const ownShare = step < 3 ? LADDER[0].own : lerp(li === 0 ? to.own : from.own, to.own, k);
    const needShare = step < 3 ? LADDER[0].need : lerp(li === 0 ? to.need : from.need, to.need, k);
    otherBar.span(GAUGE.x + GAUGE.w * (1 - otherShare), GAUGE.y, GAUGE.w * otherShare, GAUGE.h);
    ownBar.span(GAUGE.x + GAUGE.w * (1 - otherShare - ownShare), GAUGE.y, GAUGE.w * ownShare, GAUGE.h);
    ownText.pos(GAUGE.x + GAUGE.w * (1 - otherShare - ownShare / 2), GAUGE.y + GAUGE.h + 3.6);
    ownText.alpha(ownShare > 0.15 ? b : 0);
    const free = Math.max(0, 1 - otherShare - ownShare);
    freeEnd.span(GAUGE.x + GAUGE.w * free - 0.5, GAUGE.y - 0.8, 0.9, GAUGE.h + 1.6);
    const pct = (v) => `${Math.round(v * 100)}%`;
    
    verdict.text(`free ${pct(free)}, need ${pct(needShare)}: ${free >= needShare - 1e-9 ? "fits" : "short"}`);
    needBar.span(GAUGE.x, GAUGE.y + GAUGE.h + 1.2, GAUGE.w * needShare, 0.6);
    needTip.span(GAUGE.x + GAUGE.w * needShare - 0.6, GAUGE.y - 1.2, 0.6, GAUGE.h + 3);
    needText.pos(GAUGE.x, GAUGE.y + GAUGE.h + 3.8);
    otherText.pos(GAUGE.x + GAUGE.w, GAUGE.y - 2.6);
    rungs.forEach((rung, i) => {
      const lit = step >= 3 && step <= 6 && li === i ? sub(lp, 0.45, 0.8) : 0;
      const passed = step >= 3 && i < li;
      rung.box.fill(lerp(passed ? 0.04 : 0.1, 0.42, lit)).alpha(b * (passed ? 0.5 : 1));
      rung.name.alpha(b * (passed ? 0.6 : 1));
      rung.note.alpha(b * (step >= 3 && li === i ? 1 : 0.7));
    });
    arrows.forEach((arrow, i) => arrow.color(step >= 3 && li > i ? "ink" : "faint"));

    // Band C.
    const c = dim(2);
    band[2].forEach((item) => item.alpha(c));
    const down = at(step, t, 7);
    const open = at(step, t, 8);
    const check = at(step, t, 9);
    const downX = sub(down, 0.15, 0.45);
    crossC.forEach((line) => line.grow(downX).alpha(downX > 0 ? c : 0));
    daemon.fill(lerp(0.16, 0.04, downX)).alpha(c * lerp(1, 0.55, downX));
    toDaemon.alpha(c * lerp(1, 0.35, Math.max(downX, sub(open, 0.6, 0.9))));
    toLocal.grow(sub(down, 0.45, 0.8)).alpha(down > 0.45 ? c : 0);
    local.fill(step === 7 ? lerp(0.1, 0.4, sub(down, 0.6, 0.9)) : step > 7 ? 0.24 : 0.08).alpha(c * (step >= 7 ? 1 : 0.5));
    client.fill(step === 7 || step === 8 ? 0.3 : 0.16);
    fails.forEach((fail, i) => {
      const on = step > 8 ? 1 : step === 8 ? (i === 0 ? 1 : sub(open, 0.1 + i * 0.2, 0.25 + i * 0.2)) : step === 7 && i === 0 ? sub(down, 0.5, 0.7) : 0;
      fail.core.alpha(c * on);
      fail.ring.alpha(c);
    });
    const isOpen = step > 8 || (step === 8 && open > 0.7);
    breaker.text(isOpen ? "breaker: open" : "breaker: closed").tone("cpu", isOpen);
    toVerify.grow(sub(check, 0.1, 0.4)).alpha(step === 9 ? c : 0);
    daemonVerify.grow(sub(check, 0.1, 0.4)).alpha(step === 9 ? 0.6 * c : 0);
    verify.fill(lerp(0.08, 0.3, sub(check, 0.4, 0.7))).alpha(step === 9 ? c : c * 0.5);
    verifyText.alpha(step === 9 ? c : c * 0.6);
    final.text("a proof leaves only after the verifier accepts it").alpha(sub(check, 0.6, 0.95));
  };
}

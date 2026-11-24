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

// Drawing kit for the step animations.
//
// A stage is a three.js scene under an orthographic camera plus a layer of
// HTML labels. World coordinates run from (0, 0) at the top left to (W, H) at
// the bottom right. Every colour is a CSS token, so a theme change repaints
// the scene. A scene is a pure function of (step, t): it sets every object
// from that pair and keeps no state of its own.

import * as THREE from "three";

export const W = 100;
export const H = 112;

export const clamp01 = (v) => Math.min(1, Math.max(0, v));
export const ease = (t) => 1 - Math.pow(1 - clamp01(t), 3);
/** Progress of sub-interval [a, b] of t, eased. */
export const sub = (t, a, b) => ease((t - a) / (b - a));
/** Progress of step `s` given the current (step, t). */
export const at = (step, t, s) => (step > s ? 1 : step < s ? 0 : t);
export const lerp = (a, b, p) => a + (b - a) * p;

const probe = document.createElement("canvas");
probe.width = probe.height = 1;
const probeCtx = probe.getContext("2d", { willReadFrequently: true });

/** Resolves a CSS colour token to an sRGB triple through a 2D canvas. */
function resolveToken(host, token) {
  const span = document.createElement("span");
  span.style.color = `var(--${token})`;
  host.appendChild(span);
  const css = getComputedStyle(span).color;
  span.remove();
  probeCtx.clearRect(0, 0, 1, 1);
  probeCtx.fillStyle = "#000";
  probeCtx.fillStyle = css;
  probeCtx.fillRect(0, 0, 1, 1);
  const d = probeCtx.getImageData(0, 0, 1, 1).data;
  return [d[0] / 255, d[1] / 255, d[2] / 255];
}

function roundedRect(w, h, r) {
  const s = new THREE.Shape();
  const x = -w / 2;
  const y = -h / 2;
  r = Math.min(r, w / 2, h / 2);
  s.moveTo(x + r, y);
  s.lineTo(x + w - r, y);
  s.absarc(x + w - r, y + r, r, -Math.PI / 2, 0, false);
  s.lineTo(x + w, y + h - r);
  s.absarc(x + w - r, y + h - r, r, 0, Math.PI / 2, false);
  s.lineTo(x + r, y + h);
  s.absarc(x + r, y + h - r, r, Math.PI / 2, Math.PI, false);
  s.lineTo(x, y + r);
  s.absarc(x + r, y + r, r, Math.PI, Math.PI * 1.5, false);
  return s;
}

/** A drawable with a token colour, an opacity and a position. */
class Item {
  constructor(stage, object, materials) {
    this.stage = stage;
    this.object = object;
    this.materials = materials;
    this.token = null;
  }
  color(token) {
    if (token !== this.token) {
      this.token = token;
      const [r, g, b] = this.stage.rgb(token);
      for (const m of this.materials) m.color.setRGB(r, g, b, THREE.SRGBColorSpace);
    }
    return this;
  }
  alpha(a) {
    a = clamp01(a);
    for (const m of this.materials) m.opacity = a * (m.userData.k ?? 1);
    this.object.visible = a > 0.004;
    return this;
  }
  pos(x, y) {
    this.object.position.x = x;
    this.object.position.y = -y;
    return this;
  }
  scale(sx, sy = sx) {
    this.object.scale.set(sx, sy, 1);
    return this;
  }
  repaint() {
    const token = this.token;
    this.token = null;
    if (token) this.color(token);
  }
}

class Label {
  constructor(stage, text, x, y, cls) {
    this.el = document.createElement("span");
    this.el.className = `lbl ${cls}`.trim();
    this.shown = 1;
    this.value = null;
    this.height = stage.height;
    stage.labelLayer.appendChild(this.el);
    this.text(text).pos(x, y);
  }
  text(value) {
    if (value !== this.value) {
      this.value = value;
      this.el.textContent = value;
    }
    return this;
  }
  pos(x, y) {
    this.el.style.left = `${(x / W) * 100}%`;
    this.el.style.top = `${(y / this.height) * 100}%`;
    return this;
  }
  /**
   * Below 0.3 the label fades. From 0.3 up it is fully opaque, and a value
   * under 1 shows it in the muted text colour. A settled label therefore
   * keeps the contrast of the text tokens and is never half transparent.
   */
  alpha(a) {
    a = clamp01(a);
    if (a !== this.shown) {
      this.shown = a;
      this.el.style.opacity = Math.min(1, a / 0.3).toFixed(3);
      this.el.classList.toggle("dimmed", a < 0.95);
    }
    return this;
  }
  tone(cls, on = true) {
    this.el.classList.toggle(cls, on);
    return this;
  }
}

export class Stage {
  constructor(host) {
    this.host = host;
    // World height; a figure can ask for a taller stage with data-height.
    this.height = Number(host.dataset.height) || H;
    
    this.items = [];
    this.palette = new Map();
    this.scene = new THREE.Scene();
    this.camera = new THREE.OrthographicCamera(0, W, 0, -this.height, -50, 50);
    this.renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
    this.renderer.setClearColor(0x000000, 0);
    this.canvas = this.renderer.domElement;
    this.canvas.setAttribute("aria-hidden", "true");
    host.appendChild(this.canvas);
    this.labelLayer = document.createElement("div");
    this.labelLayer.className = "labels";
    this.labelLayer.setAttribute("aria-hidden", "true");
    host.appendChild(this.labelLayer);
    this.z = 0;
    this.resize();
    new ResizeObserver(() => {
      this.resize();
      this.onchange?.();
    }).observe(host);
  }

  resize() {
    const w = Math.max(1, this.host.clientWidth);
    const h = Math.max(1, this.host.clientHeight);
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    this.renderer.setSize(w, h, false);
  }

  rgb(token) {
    if (!this.palette.has(token)) this.palette.set(token, resolveToken(this.host, token));
    return this.palette.get(token);
  }

  /** Reads the tokens again after a theme change. */
  repaint() {
    this.palette.clear();
    for (const item of this.items) item.repaint();
  }

  render() {
    this.renderer.render(this.scene, this.camera);
  }

  #add(object, materials, token, alpha) {
    object.position.z = this.z;
    this.z += 0.01;
    this.scene.add(object);
    const item = new Item(this, object, materials);
    this.items.push(item);
    return item.color(token).alpha(alpha);
  }

  #mat(k = 1) {
    const m = new THREE.MeshBasicMaterial({ transparent: true, depthTest: false });
    m.userData.k = k;
    return m;
  }

  /** A filled rounded rectangle with an outline, centred on (cx, cy). */
  box(cx, cy, w, h, { token = "ink", fill = 0.16, r = 1.6, line = 0.42, alpha = 1 } = {}) {
    const group = new THREE.Group();
    const fillMat = this.#mat(fill);
    const lineMat = this.#mat(1);
    const outer = roundedRect(w, h, r);
    group.add(new THREE.Mesh(new THREE.ShapeGeometry(outer, 8), fillMat));
    if (line > 0) {
      const ring = roundedRect(w, h, r);
      ring.holes.push(roundedRect(w - 2 * line, h - 2 * line, Math.max(0.1, r - line)));
      group.add(new THREE.Mesh(new THREE.ShapeGeometry(ring, 8), lineMat));
    }
    const item = this.#add(group, line > 0 ? [fillMat, lineMat] : [fillMat], token, alpha);
    item.fill = (k) => {
      fillMat.userData.k = k;
      return item;
    };
    return item.pos(cx, cy);
  }

  /** A plain rectangle given by its top left corner; `span` resizes it. */
  bar(x, y, w, h, { token = "ink", fill = 0.3, alpha = 1 } = {}) {
    const mat = this.#mat(fill);
    const geo = new THREE.PlaneGeometry(1, 1);
    geo.translate(0.5, -0.5, 0);
    const item = this.#add(new THREE.Mesh(geo, mat), [mat], token, alpha);
    item.span = (x0, y0, w0, h0) => {
      item.object.position.x = x0;
      item.object.position.y = -y0;
      item.object.scale.set(Math.max(w0, 1e-4), Math.max(h0, 1e-4), 1);
      return item;
    };
    item.fill = (k) => {
      mat.userData.k = k;
      return item;
    };
    return item.span(x, y, w, h);
  }

  dot(cx, cy, r, { token = "ink", alpha = 1 } = {}) {
    const mat = this.#mat(1);
    return this.#add(new THREE.Mesh(new THREE.CircleGeometry(r, 28), mat), [mat], token, alpha).pos(cx, cy);
  }

  /** A square turned 45 degrees: the mark of a random draw. */
  diamond(cx, cy, r, { token = "rng", alpha = 1 } = {}) {
    const mat = this.#mat(1);
    const mesh = new THREE.Mesh(new THREE.PlaneGeometry(r * 1.42, r * 1.42), mat);
    mesh.rotation.z = Math.PI / 4;
    return this.#add(mesh, [mat], token, alpha).pos(cx, cy);
  }

  /**
   * A straight line from (x1, y1) to (x2, y2). `grow(p)` draws the first
   * part `p` of it. With `head`, the line ends in an arrow head.
   */
  line(x1, y1, x2, y2, { token = "ink", thick = 0.42, alpha = 1, head = false, dash = 0 } = {}) {
    const dx = x2 - x1;
    const dy = y2 - y1;
    const len = Math.hypot(dx, dy) || 1e-4;
    const group = new THREE.Group();
    group.rotation.z = Math.atan2(-dy, dx);
    const mat = this.#mat(1);
    const shaft = new THREE.Group();
    const headSize = head ? Math.max(1.5, thick * 3.6) : 0;
    const shaftLen = len - headSize * 0.8;
    if (dash > 0) {
      for (let s = 0; s < shaftLen; s += dash * 2) {
        const geo = new THREE.PlaneGeometry(Math.min(dash, shaftLen - s), thick);
        geo.translate(s + Math.min(dash, shaftLen - s) / 2, 0, 0);
        shaft.add(new THREE.Mesh(geo, mat));
      }
    } else {
      const geo = new THREE.PlaneGeometry(shaftLen, thick);
      geo.translate(shaftLen / 2, 0, 0);
      shaft.add(new THREE.Mesh(geo, mat));
    }
    group.add(shaft);
    let tip = null;
    if (head) {
      const tri = new THREE.Shape();
      tri.moveTo(0, 0);
      tri.lineTo(-headSize, headSize * 0.55);
      tri.lineTo(-headSize, -headSize * 0.55);
      tri.closePath();
      tip = new THREE.Mesh(new THREE.ShapeGeometry(tri), mat);
      group.add(tip);
    }
    const item = this.#add(group, [mat], token, alpha).pos(x1, y1);
    item.grow = (p) => {
      p = clamp01(p);
      shaft.scale.x = Math.max(p, 1e-4);
      if (tip) {
        tip.position.x = len * p;
        tip.visible = p > 0.05;
      }
      return item;
    };
    return item.grow(1);
  }

  label(text, x, y, cls = "") {
    return new Label(this, text, x, y, cls);
  }
}

const ICONS = {
  restart: '<path d="M3.5 8a4.5 4.5 0 1 0 1.4-3.3M3.2 2.6v2.7h2.7" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/>',
  back: '<path d="M11.5 3.2 5.6 8l5.9 4.8zM4.4 3.2v9.6" fill="currentColor" stroke="currentColor" stroke-width="1.3" stroke-linejoin="round" stroke-linecap="round"/>',
  play: '<path d="M4.6 2.8 12.6 8l-8 5.2z" fill="currentColor" stroke="currentColor" stroke-width="1.3" stroke-linejoin="round"/>',
  pause: '<path d="M5 3v10M11 3v10" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round"/>',
  next: '<path d="M4.5 3.2 10.4 8l-5.9 4.8zM11.6 3.2v9.6" fill="currentColor" stroke="currentColor" stroke-width="1.3" stroke-linejoin="round" stroke-linecap="round"/>',
};
const icon = (name) => `<svg viewBox="0 0 16 16" aria-hidden="true">${ICONS[name]}</svg>`;

const STEP_MS = 2600;
const HOLD_MS = 900;
const HOLD_MAX_MS = 6000;
const FADE_MS = 180;

/**
 * Binds a scene to its figure: the controls, the caption of the current
 * step, and the clock. The steps come from the figure's ordered list, so the
 * text alternative and the animation cannot drift apart.
 *
 * A scene can name sub-beats: `draw.beats = { 5: [0.5, 1] }` makes Next stop
 * at t = 0.5 of step 5 before it reaches the end. Play runs through them.
 */
export class Player {
  constructor(figure, build) {
    this.figure = figure;
    this.steps = [...figure.querySelectorAll(".steps > li")];
    this.caption = figure.querySelector(".step-now");
    this.stage = new Stage(figure.querySelector(".stage"));
    this.draw = build(this.stage);
    this.beats = this.draw.beats ?? {};
    this.step = 0;
    this.t = 1;
    this.target = 1; // where a single step forward stops
    this.pending = 0; // Next presses not served yet
    this.playing = false;
    this.once = false;
    this.speed = 1;
    this.hold = 0;
    this.last = 0;
    this.lost = false;
    this.reduced = window.matchMedia("(prefers-reduced-motion: reduce)");
    this.#controls();
    this.stage.onchange = () => this.paint();
    this.reduced.addEventListener("change", () => {
      this.pause();
      this.t = 1;
      this.sync();
    });
        // Playback follows the drawing, not the long transcript beside it.
    new IntersectionObserver(([entry]) => !entry.isIntersecting && this.pause(), { rootMargin: "80px" }).observe(this.stage.host);
    document.addEventListener("visibilitychange", () => document.hidden && this.pause());
    // Without its drawing the labels mean nothing: fall back to the text.
    this.stage.canvas.addEventListener("webglcontextlost", (event) => {
      event.preventDefault();
      this.pause();
      this.lost = true;
      figure.dataset.webgl = "off";
      figure.querySelector(".steps-text").open = true;
    });
    this.stage.canvas.addEventListener("webglcontextrestored", () => {
      this.lost = false;
      this.stage.repaint();
      figure.dataset.webgl = "on";
      this.sync();
    });
    this.sync();
  }

  #controls() {
    const view = this.figure.querySelector(".anim-view");
    const name = this.figure.dataset.name;
    const bar = document.createElement("div");
    bar.className = "controls";
    bar.setAttribute("role", "group");
    bar.setAttribute("aria-label", `Controls for the ${name} animation`);
    const dots = this.steps
      .map((li, i) => {
        const title = (li.querySelector("strong")?.textContent ?? "").replace(/[.\s]+$/, "");
        return `<button type="button" class="dot" data-step="${i}" aria-label="Step ${i + 1}: ${title}" title="Step ${i + 1}: ${title}"></button>`;
      })
      .join("");
    bar.innerHTML = `
      <div class="seek">
        <div class="dots" role="group" aria-label="Steps">${dots}</div>
        <input type="range" class="scrub" min="0" max="1000" value="1000" aria-label="Position within the step" />
      </div>
      <button type="button" class="btn" data-act="restart" aria-label="Back to the first step" title="Back to the first step">${icon("restart")}</button>
      <button type="button" class="btn" data-act="back" aria-label="Previous step" title="Previous step">${icon("back")}</button>
      <button type="button" class="btn play" data-act="play"></button>
      <button type="button" class="btn" data-act="next" aria-label="Next step" title="Next step">${icon("next")}</button>
      <span class="meta">
        <span class="count"></span>
        <label class="speed">Speed
          <select data-act="speed">
            <option value="0.5">0.5x</option>
            <option value="1" selected>1x</option>
            <option value="2">2x</option>
          </select>
        </label>
      </span>
      <span class="vh" data-act="live" aria-live="polite"></span>
      <span class="motion-note" hidden>Reduced motion is on. Each step shows its final frame, and some steps stop at frames in between. Use the step buttons.</span>`;
    view.appendChild(bar);
    this.ui = {
      restart: bar.querySelector('[data-act="restart"]'),
      back: bar.querySelector('[data-act="back"]'),
      play: bar.querySelector('[data-act="play"]'),
      next: bar.querySelector('[data-act="next"]'),
      speed: bar.querySelector('[data-act="speed"]'),
      count: bar.querySelector(".count"),
      note: bar.querySelector(".motion-note"),
      speedBox: bar.querySelector(".speed"),
      live: bar.querySelector('[data-act="live"]'),
      dots: [...bar.querySelectorAll(".dot")],
      scrub: bar.querySelector(".scrub"),
    };
    bar.addEventListener("click", () => (this.touched = true), { capture: true });
    this.ui.restart.addEventListener("click", () => this.go(0, 1));
    this.ui.back.addEventListener("click", () => this.back());
    this.ui.next.addEventListener("click", () => this.next());
    this.ui.play.addEventListener("click", () => (this.playing ? this.pause() : this.play()));
    this.ui.speed.addEventListener("change", () => (this.speed = Number(this.ui.speed.value)));
    // A dot jumps to its step and plays it once; the current dot replays it.
    for (const dot of this.ui.dots) dot.addEventListener("click", () => this.replay(Number(dot.dataset.step)));
        // The range follows the clock except while the reader drags it.
    this.ui.scrub.addEventListener("pointerdown", () => {
      this.seeking = true;
      this.pause();
    });
    for (const type of ["pointerup", "pointercancel", "change"]) this.ui.scrub.addEventListener(type, () => (this.seeking = false));
        this.ui.scrub.addEventListener("input", () => {
      // Read the value first: pausing repaints and would reset the range.
      const value = Number(this.ui.scrub.value) / 1000;
      this.touched = true;
      this.pause();
      this.pending = 0;
      this.t = value;
      this.sync();
    });
  }

  get last_step() {
    return this.steps.length - 1;
  }

  /** The stops of a step: its sub-beats, always ending at 1. */
  stops(step) {
    return this.beats[step] ?? [1];
  }

  /** The state one step forward from (step, t), or null at the end. */
  after(step, t) {
    const stop = this.stops(step).find((b) => b > t + 1e-6);
    if (stop !== undefined) return [step, stop];
    if (step >= this.last_step) return null;
    return [step + 1, this.stops(step + 1)[0]];
  }

    /** Steps back once, through the same stops as Next. */
  back() {
    const t = this.playing && this.once ? this.target : this.t;
    const stop = [...this.stops(this.step)].reverse().find((b) => b < t - 1e-6);
    if (stop !== undefined) this.go(this.step, stop);
    else this.go(this.step - 1, 1);
  }

  go(step, t) {
    this.pause();
    this.pending = 0;
    this.step = Math.min(this.last_step, Math.max(0, step));
    this.t = t;
    this.#fade();
    this.sync();
  }

  /** A short crossfade for a jump. Reduced motion shows the frame at once. */
    #fade() {
    if (this.reduced.matches) return;
    for (const layer of [this.stage.canvas, this.stage.labelLayer]) {
      layer.animate?.([{ opacity: 0.35 }, { opacity: 1 }], { duration: FADE_MS, easing: "ease-out" });
    }
  }

  replay(step) {
    if (this.reduced.matches) {
      this.go(step, 1);
      return;
    }
    this.pause();
    this.pending = 0;
    this.step = step;
    this.t = 0;
    this.target = this.stops(step)[0];
    this.once = true;
    this.#run();
  }

  /**
   * Steps forward once, to the next sub-beat or the next step. Every press
   * counts: a press during a transition finishes it and queues one more.
   */
  next() {
    const to = this.after(this.step, this.playing && this.once ? this.target : this.t);
    if (!to) return;
    if (this.reduced.matches) {
      this.go(to[0], to[1]);
      return;
    }
    if (this.playing && this.once) {
      this.pending += 1;
      this.t = this.target; // finish the transition in flight
      return;
    }
    this.pause();
    this.#advance(to);
  }

  #advance([step, stop]) {
    if (step !== this.step) {
      this.step = step;
      this.t = 0;
    }
    this.target = stop;
    this.once = true;
    this.#run();
  }

  play() {
    if (this.reduced.matches) return;
    this.pending = 0;
    if (this.step >= this.last_step && this.t >= 1) {
      this.step = 0;
      this.t = 0;
    } else if (this.t >= 1) {
      this.step += 1;
      this.t = 0;
    }
    this.once = false;
    this.#run();
  }

  #run() {
    this.hold = 0;
    if (this.playing) {
      this.sync();
      return;
    }
    this.playing = true;
    this.last = performance.now();
    this.sync();
    requestAnimationFrame((now) => this.#tick(now));
  }

  pause() {
    if (!this.playing) return;
    this.playing = false;
    this.sync();
  }

  #tick(now) {
    if (!this.playing) return;
    const dt = Math.min(64, now - this.last) * this.speed;
    this.last = now;
    const stop = this.once ? this.target : 1;
    if (this.t < stop) {
      this.t = Math.min(stop, this.t + dt / STEP_MS);
    }
    if (this.once && this.t >= stop) {
      const to = this.pending > 0 ? this.after(this.step, this.t) : null;
      if (to) {
        this.pending -= 1;
        this.#advance(to);
      } else {
        this.pending = 0;
        this.pause();
        return;
      }
    } else if (!this.once && this.t >= 1) {
      if (this.step >= this.last_step) {
        this.pause();
        return;
      }
      this.hold += dt;
      // A longer caption stays longer before the next step starts, up to a cap.
      const words = this.steps[this.step].textContent.trim().split(/\s+/).length;
      if (this.hold >= Math.min(HOLD_MAX_MS, HOLD_MS + words * 230)) {
        this.hold = 0;
        this.step += 1;
        this.t = 0;
        this.sync();
      }
    }
    this.paint();
    requestAnimationFrame((n) => this.#tick(n));
  }

  paint() {
    if (this.lost) return;
    this.draw(this.step, this.t);
    this.stage.render();
    if (!this.seeking) this.ui.scrub.value = String(Math.round(this.t * 1000));
  }

  /** Brings the controls and the caption in line with the state. */
  sync() {
    const reduced = this.reduced.matches;
    const atEnd = this.step >= this.last_step && this.t >= 1;
    const playLabel = this.playing ? "Pause" : atEnd ? "Replay" : "Play";
    this.ui.play.innerHTML = `${icon(this.playing ? "pause" : "play")}<span>${playLabel}</span>`;
    this.ui.play.hidden = reduced;
    this.ui.note.hidden = !reduced;
    this.ui.speedBox.hidden = reduced;
    this.ui.scrub.hidden = reduced;
    this.ui.back.disabled = this.step === 0 && this.t <= this.stops(0)[0];
    this.ui.restart.disabled = this.step === 0 && this.t >= 1;
    this.ui.next.disabled = atEnd;
    const stops = this.stops(this.step);
    const part = stops.findIndex((b) => b >= this.t - 1e-6);
    const parts = stops.length > 1 && !this.playing ? `, part ${Math.max(0, part) + 1} of ${stops.length}` : "";
    this.ui.count.textContent = `Step ${this.step + 1} of ${this.steps.length}${parts}`;
    this.ui.dots.forEach((dot, i) => {
      dot.classList.toggle("done", i < this.step);
      if (i === this.step) dot.setAttribute("aria-current", "step");
      else dot.removeAttribute("aria-current");
    });
        const changed = this.caption.dataset.step !== String(this.step);
    if (changed) {
      this.caption.dataset.step = String(this.step);
      this.caption.innerHTML = this.steps[this.step].innerHTML;
    }
    // During playback a screen reader hears the step and its title only. A
    // manual step reads the whole explanation, and a stop inside a step
    // reads the values that the scene shows there.
    if (this.touched && (changed || !this.playing)) {
      const title = this.steps[this.step].querySelector("strong")?.textContent ?? "";
      const all = this.steps[this.step].textContent.replace(/\s+/g, " ").trim();
      const detail = !this.playing ? (this.draw.describe?.(this.step, this.t) ?? "") : "";
      const text = `Step ${this.step + 1} of ${this.steps.length}${parts}. ${detail || (this.playing && !this.once ? title : all)}`;
      if (text !== this.ui.live.textContent) this.ui.live.textContent = text;
    }
    this.figure.dataset.step = String(this.step + 1);
    this.paint();
  }
}

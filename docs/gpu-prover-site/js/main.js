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

// Page behaviour: theme toggle, section highlight in the contents list,
// benchmark tables, and the five step animations.

import { renderBenchmarks } from "./benchmarks.js";

const SCENES = {
  pipeline: () => import("./scenes/pipeline.js"),
  ntt: () => import("./scenes/ntt.js"),
  msm: () => import("./scenes/msm.js"),
  memory: () => import("./scenes/memory.js"),
  fallback: () => import("./scenes/fallback.js"),
};

function themeToggle() {
  const meta = document.querySelector('meta[name="color-scheme"]');
  const button = document.querySelector(".theme-toggle");
  const system = window.matchMedia("(prefers-color-scheme: dark)");
  const store = {
    get: () => {
      try {
        return localStorage.getItem("color-scheme");
      } catch {
        return null;
      }
    },
    set: (value) => {
      try {
        if (value) localStorage.setItem("color-scheme", value);
        else localStorage.removeItem("color-scheme");
      } catch {
        // The theme still applies for this page view.
      }
    },
  };
  const notify = () => document.dispatchEvent(new CustomEvent("themechange"));
  button.addEventListener("click", () => {
    const systemScheme = system.matches ? "dark" : "light";
    const rendered = meta.content === "light dark" ? systemScheme : meta.content;
    const target = rendered === "dark" ? "light" : "dark";
    // An override equal to the system scheme means "follow the system again".
    const stored = target === systemScheme ? null : target;
    store.set(stored);
    meta.content = stored ?? "light dark";
    notify();
  });
  window.addEventListener("storage", (event) => {
    if (event.key === "color-scheme") {
      meta.content = event.newValue ?? "light dark";
      notify();
    }
  });
  system.addEventListener("change", notify);
}

function contentsHighlight() {
  const links = new Map(
    [...document.querySelectorAll(".toc a")].map((a) => [a.getAttribute("href").slice(1), a]),
  );
  const seen = new Set();
  const observer = new IntersectionObserver(
    (entries) => {
      for (const entry of entries) {
        if (entry.isIntersecting) seen.add(entry.target.id);
        else seen.delete(entry.target.id);
      }
      let current = null;
      for (const id of links.keys()) if (seen.has(id)) current ??= id;
      if (!current) return;
      for (const [id, a] of links) {
        if (id === current) a.setAttribute("aria-current", "true");
        else a.removeAttribute("aria-current");
      }
      // On narrow screens the list is a strip: keep the current link in view
      // inside the strip without moving the page or the focus.
      const strip = document.querySelector(".toc ol");
      if (strip.scrollWidth > strip.clientWidth) {
        const a = links.get(current);
        strip.scrollTo({ left: a.offsetLeft - strip.offsetLeft - 16, behavior: "instant" });
      }
    },
    { rootMargin: "-20% 0px -65% 0px" },
  );
  for (const id of links.keys()) {
    const section = document.getElementById(id);
    if (section) observer.observe(section);
  }
}

/** Loads the web fonts without holding the first paint. */
function fonts() {
  const href = document.querySelector('meta[name="font-css"]')?.content;
  if (!href) return Promise.resolve();
  const link = document.createElement("link");
  link.rel = "stylesheet";
  link.href = href;
  // Resolves when the font faces are known, or after 3 s without them.
  const known = new Promise((resolve) => {
    link.addEventListener("load", resolve);
    link.addEventListener("error", resolve);
    setTimeout(resolve, 3000);
  });
  document.head.appendChild(link);
  return known.then(() => document.fonts?.ready);
}

/** Builds every repository link from the one base in the page head. */
function repoLinks() {
  const base = document.querySelector('meta[name="repo-base"]')?.content;
  if (!base) return;
  for (const a of document.querySelectorAll("a[data-repo]")) a.href = base + a.dataset.repo;
}

/**
 * Starts each animation when its figure comes near the viewport. The drawing
 * kit and three.js load on the first such figure, not with the page.
 */
function animations() {
  let kit = null;
  const start = async (figure) => {
    const text = figure.querySelector(".steps-text");
    const stage = figure.querySelector(".stage");
    try {
      kit ??= import("./stage.js");
      const [{ Player }, scene] = await Promise.all([kit, SCENES[figure.dataset.scene]()]);
      const player = new Player(figure, scene.default);
      document.addEventListener("themechange", () => {
        player.stage.repaint();
        player.paint();
      });
            figure.dataset.webgl = "on";
    } catch (error) {
      console.warn(`Animation "${figure.dataset.scene}" is not available.`, error);
      figure.dataset.webgl = "off";
      // The notice is plain text now, not an image.
      stage.removeAttribute("role");
      stage.removeAttribute("aria-label");
      text.open = true;
    }
  };
  const observer = new IntersectionObserver(
    (entries) => {
      for (const entry of entries) {
        if (!entry.isIntersecting) continue;
        observer.unobserve(entry.target);
        start(entry.target);
      }
    },
    { rootMargin: "100% 0px" },
  );
  for (const figure of document.querySelectorAll(".anim[data-scene]")) {
    // The transcript closes now, so the page height is settled before a
    // scene starts. A scene that fails opens it again.
    figure.querySelector(".steps-text").open = false;
    observer.observe(figure);
  }
  document.documentElement.dataset.ready = "true";
}

/** A link to a section opens on that section, also in a fresh tab. */
function settle(content) {
  let moved = false;
  for (const type of ["wheel", "touchstart", "keydown"]) {
    window.addEventListener(type, () => (moved = true), { once: true, passive: true });
  }
  Promise.resolve(content).then(() => requestAnimationFrame(() => (moved ? document.documentElement.classList.add("settled") : landNow())));
  const landNow = () => {
    const target = location.hash && document.getElementById(location.hash.slice(1));
    if (target) target.scrollIntoView({ behavior: "instant", block: "start" });
    document.documentElement.classList.add("settled");
  };
}

/** Print shows every transcript in full. */
function printing() {
  let closed = [];
  window.addEventListener("beforeprint", () => {
    closed = [...document.querySelectorAll("details.steps-text:not([open])")];
    for (const d of closed) d.open = true;
  });
  window.addEventListener("afterprint", () => {
    for (const d of closed) d.open = false;
  });
}

repoLinks();
const typeface = fonts();
themeToggle();
printing();
contentsHighlight();
const benchmarks = renderBenchmarks().then(repoLinks);
animations();
settle(Promise.allSettled([benchmarks, typeface]));

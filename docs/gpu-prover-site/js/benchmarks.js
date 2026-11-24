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

// Renders the benchmark section from data/benchmarks.json. Every measured
// number on the page comes from that file.

const DATA_URL = new URL("../data/benchmarks.json", import.meta.url);
// The results file of the one measurement session that the headline quotes.
const SESSION_URL = new URL("../data/session.json", import.meta.url);

function el(tag, text, attrs = {}) {
  const node = document.createElement(tag);
  if (text != null) node.textContent = text;
  for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, value);
  return node;
}

/** Builds a table from `{ columns, rows }`; the first column is the row header. */
function table(set, captionId) {
  const wrap = el("div", null, { class: "table-wrap", role: "region", tabindex: "0", "aria-labelledby": captionId });
  const t = el("table", null, set.stack ? { class: "stackable" } : {});
  const head = el("tr");
  for (const column of set.columns) {
    head.appendChild(el("th", column.label, { scope: "col", ...(column.numeric ? { class: "num" } : {}) }));
  }
  const thead = el("thead");
  thead.appendChild(head);
  const tbody = el("tbody");
  for (const row of set.rows) {
    const tr = el("tr");
    set.columns.forEach((column, index) => {
      const value = row[column.key];
      const text = value == null || value === "" ? "not reported" : String(value);
      const cell =
        index === 0
          ? el("th", text, { scope: "row" })
          : el("td", text, { "data-label": column.label, ...(column.numeric ? { class: "num" } : {}) });
      tr.appendChild(cell);
    });
    tbody.appendChild(tr);
  }
  t.append(thead, tbody);
  wrap.appendChild(t);
  return wrap;
}

/** Fills one slot with a data set: label, table and notes, or its empty text. */
function section(slot, set, titleId) {
  if (!slot) return;
  slot.replaceChildren();
  if (!set?.rows?.length) {
    // No rows: the heading stays, and the sentence of the data set stands in
    // for the table.
    slot.appendChild(el("p", set?.empty ?? "No measurements are available.", { class: "empty" }));
    return;
  }
  if (set.label) slot.appendChild(el("p", set.label, { class: "bench-label" }));
  slot.appendChild(table(set, titleId));
  if (set.notes?.length) {
    const notes = el("ul");
    for (const note of set.notes) notes.appendChild(el("li", note));
    const prose = el("div", null, { class: "prose bench-notes" });
    prose.appendChild(notes);
    slot.appendChild(prose);
  }
}

/** A link to a repository file; main.js gives it its address. */
function repo(text, path) {
  return el("a", text, { "data-repo": path });
}

/**
 * One board of the headline results: one row for each machine or circuit
 * size, the CPU and GPU times as two bars on one scale, and the speed-up
 * set large. A row may carry cold times, shown under the warm ones. A row
 * with a `group` text starts a labelled group.
 */
function board(set) {
  const c = set.columns;
  const table = el("table", null, { class: "results-table" });
  table.appendChild(el("caption", set.caption));
  const head = el("tr");
  for (const key of ["gpu", "cpu", "device", "speedup"]) head.appendChild(el("th", c[key], { scope: "col" }));
  const thead = el("thead");
  thead.appendChild(head);
  const tbody = el("tbody");
  for (const row of set.rows) {
    if (row.group) {
      const g = el("tr", null, { class: "results-group" });
      g.appendChild(el("th", row.group, { colspan: "4", scope: "colgroup" }));
      tbody.appendChild(g);
    }
    const tr = el("tr");
    tr.appendChild(el("th", row.gpu, { scope: "row" }));
    const time = (label, text, seconds, cold, kind) => {
      const td = el("td", null, { class: `results-time ${kind}`, "data-label": label });
      td.appendChild(repo(text, row.source));
      const bar = el("span", null, { class: "results-bar", "aria-hidden": "true" });
      bar.style.setProperty("--share", `${Math.max(2, (100 * seconds) / Math.max(row.cpu_s, row.gpu_s)).toFixed(1)}%`);
      td.appendChild(bar);
      if (cold) td.appendChild(el("span", `${c.cold ?? "cold"} ${cold}`, { class: "results-cold" }));
      return td;
    };
    tr.appendChild(time(c.cpu, row.cpu, row.cpu_s, row.cpu_cold, "cpu"));
    tr.appendChild(time(c.device, row.device, row.gpu_s, row.gpu_cold, "device"));
    const fast = el("td", null, { class: "results-speedup", "data-label": c.speedup });
    const link = repo(row.speedup, row.source);
    link.appendChild(el("span", "x", { class: "times" }));
    fast.appendChild(link);
    tr.appendChild(fast);
    tbody.appendChild(tr);
    if (row.detail) {
      const more = el("tr", null, { class: "results-detail" });
      more.appendChild(el("td", row.detail, { colspan: "4" }));
      tbody.appendChild(more);
    }
  }
  table.append(thead, tbody);
  // The table is laid out as a grid, so its roles are stated explicitly.
  table.setAttribute("role", "table");
  for (const group of [thead, tbody]) group.setAttribute("role", "rowgroup");
  for (const tr of table.querySelectorAll("tr")) tr.setAttribute("role", "row");
  for (const th of table.querySelectorAll("thead th")) th.setAttribute("role", "columnheader");
  for (const th of table.querySelectorAll("tbody th")) th.setAttribute("role", "rowheader");
  for (const td of table.querySelectorAll("td")) td.setAttribute("role", "cell");
  const wrap = el("div", null, { class: "results-board" });
  wrap.appendChild(table);
  const foot = el("p", `${set.note ?? ""} `, { class: "results-source" });
  (set.sources ?? []).forEach((source, i) => {
    if (i) foot.append(" · ");
    foot.appendChild(repo(source.text, source.path));
  });
  wrap.appendChild(foot);
  return wrap;
}

/** Fills `{name}` fields of a text from `vars`. */
function fill(text, vars) {
  return (text ?? "").replace(/\{(\w+)\}/g, (_, name) => `${vars[name] ?? ""}`);
}

const seconds = (x) => `${x.toFixed(3)} s`;

/** The distinct per-proof counts of a recorded list, or null when none is recorded. */
function counts(list) {
  const all = Array.isArray(list) ? list : [];
  const ok = (v) => (typeof v === "number" && Number.isInteger(v) && v >= 0) || (typeof v === "string" && /^\d+$/.test(v));
  const recorded = all.filter(ok).map(Number);
  if (!recorded.length) return null;
  return { values: [...new Set(recorded)].sort((a, b) => a - b), missing: recorded.length < all.length };
}

/** A sentence on hook declines per proof, or null when none was recorded. */
function declineNote(c, single) {
  if (!c) return null;
  if (c.missing) {
    const what = c.values.length === 1 ? `count was ${c.values[0]}` : `counts were ${joined(c.values)}`;
    return `The recorded hook-decline ${what}. Other counts were unreported.`;
  }
  if (c.values.length === 1) return single(c.values[0]);
  return `The recorded hook-decline counts were ${joined(c.values)} per proof.`;
}

/** The verification sentence for a list of paths, from their flags. */
function verification(paths, total) {
  if (paths.some((p) => p.all_verified === false)) return "The session reports a stock-verification failure.";
  if (!paths.every((p) => p.all_verified === true)) return "Verification was not reported for every path.";
  return total == null ? "The stock verifier accepted every proof." : `The stock verifier accepted all ${total} proofs.`;
}

/** A proof-time ratio of a prover change, with enough digits to stay apart from zero. */
const ratioText = (x) => `${x >= 0.01 ? x.toFixed(3) : x.toPrecision(2)}x`;
const joined = (xs) => (xs.length < 2 ? `${xs[0]}` : `${xs.slice(0, -1).join(", ")} and ${xs[xs.length - 1]}`);
const ratio = (x) => `${x.toFixed(x >= 10 ? 1 : 2)}`;

/** The reason texts of the declines that a session row can carry. */
const DECLINES = {
  "below-min-k": (n) => `${n} hook calls per proof were below the minimum size and ran on the CPU.`,
  "msm below-min-k": (n) => `${n} small MSMs per proof left on the CPU (below the minimum k).`,
};

/**
 * Turns the results file of a measurement session into the tables of the
 * page: the per-size board, the one-proof-at-a-time table, the batch table
 * and the CPU-change ratios. A block that the session lacks gives nothing.
 */
function fromSession(session, data) {
  const m = session.meta ?? {};
  const vars = { device: m.device, threads: m.threads, base: m.base, tree: m.tree };
  const dated = [m.date && `Measured on ${m.date}.`, m.clocks && `Clocks: ${m.clocks}.`, m.temperatures && `Temperatures: ${m.temperatures}.`]
    .filter(Boolean)
    .join(" ");
  const results = `${m.source}/RESULTS.md`;
  const out = {};
  if (session.h2h?.length && data.results_h2h) {
    const rows = session.h2h.map((r) => {
      const f = counts(r.gpu.fallbacks);
      const detail = [];
      if (f && f.values.some((n) => n > 0)) {
        const one = DECLINES[r.gpu.decline_reason] ?? ((n) => `Each GPU proof recorded ${n} hook declines.`);
        detail.push(declineNote(f, one));
      }
      if (r.gpu.cold_s > r.cpu.cold_s) detail.push("The cold GPU proof is slower than the cold CPU proof.");
      if (r.gpu.peak_device_bytes) detail.push(`Device peak ${(r.gpu.peak_device_bytes / 1e6).toFixed(1)} MB.`);
      return {
        gpu: `k = ${r.k}`,
        cpu_s: r.cpu.warm_median_s,
        gpu_s: r.gpu.warm_median_s,
        cpu: seconds(r.cpu.warm_median_s),
        device: seconds(r.gpu.warm_median_s),
        cpu_cold: seconds(r.cpu.cold_s),
        gpu_cold: seconds(r.gpu.cold_s),
        speedup: ratio(r.cpu.warm_median_s / r.gpu.warm_median_s),
        source: results,
        detail: detail.join(" "),
      };
    });
    const runs = [...new Set(session.h2h.flatMap((r) => [r.cpu.warm_runs, r.gpu.warm_runs]))];
    const warm = runs.length === 1 && Number.isFinite(runs[0]) ? `the median of ${runs[0]} warm proofs` : "the median of its warm proofs";
    const paths = session.h2h.flatMap((r) => [r.cpu, r.gpu]);
    const complete = paths.every((p) => Number.isInteger(p.warm_runs) && typeof p.cold_s === "number");
    const total = complete ? paths.reduce((sum, p) => sum + p.warm_runs + 1, 0) : null;
    const verified = verification(paths, total);
    out.h2h = {
      ...data.results_h2h,
      caption: `${fill(data.results_h2h.caption, { ...vars, warm, verified })} ${dated}`.trim(),
      rows,
      sources: [
        { text: "Results", path: results },
        { text: "Raw result files", path: `${m.source}/raw` },
        ...(data.results_h2h.extra_sources ?? []),
      ],
    };
  }
  const seq = session.seq;
  if (seq?.gpu?.prefix && seq?.cpu?.prefix && data.sequential) {
    const sizes = Object.keys(seq.gpu.prefix).filter((n) => seq.cpu.prefix[n]).sort((a, b) => a - b);
    const g = seq.gpu.prefix;
    const c = seq.cpu.prefix;
    const n = sizes[sizes.length - 1];
    const notes = [];
    if (seq.gpu.peak_device_bytes != null) notes.push(`The GPU device peak was ${(seq.gpu.peak_device_bytes / 1e6).toFixed(1)} MB.`);
    const sf = declineNote(counts(seq.gpu.fallbacks), (n) =>
      n === 0 ? "No GPU proof recorded a hook decline." : `Each GPU proof recorded ${n} hook declines.`,
    );
    if (sf) notes.push(sf);
    notes.push(verification([seq.gpu, seq.cpu], null));
    out.sequential = {
      ...data.sequential,
      label: fill(data.sequential.label, { ...vars, k: seq.k ?? 16, n }),
      notes,
      source: results,
      rows: sizes.map((s) => ({
        n: s,
        gpu_ps: g[s].proofs_per_s.toFixed(2),
        gpu_lat: seconds(g[s].median_latency_s),
        cpu_ps: c[s].proofs_per_s.toFixed(2),
        cpu_lat: seconds(c[s].median_latency_s),
        ratio: `${(g[s].proofs_per_s / c[s].proofs_per_s).toFixed(1)}x`,
      })),
    };
  }
  const batch = session.batch;
  if (batch?.sizes && data.batch_session) {
    const sizes = Object.keys(batch.sizes).sort((a, b) => a - b);
    out.batch = {
      ...data.batch_session,
      label: fill(data.batch_session.label, { ...vars, k: batch.k, sizes: joined(sizes) }),
      source: results,
      rows: sizes.map((s) => {
        const b = batch.sizes[s];
        return {
          n: s,
          gpu_ps: b.gpu_proofs_per_s.toFixed(2),
          cpu_ps: b.cpu_proofs_per_s.toFixed(2),
          ratio: `${(b.gpu_proofs_per_s / b.cpu_proofs_per_s).toFixed(1)}x`,
        };
      }),
    };
  }
  if (session.ratios?.length && data.cpu_changes) {
    out.cpuRows = session.ratios
      .filter((r) => typeof r.ratio === "number" && Number.isFinite(r.ratio) && r.ratio > 0)
      .map((r) => ({ change: r.change, what: r.what, ratio: ratioText(r.ratio), value: r.ratio }));
  }
  return out;
}

/** The headline results: every board that has measured rows, in order. */
function results(slot, sets) {
  if (!slot) return;
  slot.replaceChildren();
  for (const set of sets) if (set?.rows?.length) slot.appendChild(board(set));
  if (!slot.childElementCount) slot.remove();
}

/**
 * The prover changes that also speed up the CPU path. The section stays
 * hidden until the data file holds an accepted change or a dropped one.
 */
function cpuChanges(set) {
  const sectionEl = document.getElementById("cpu-too");
  // A change counts as accepted only with a measured ratio.
  // Rows come from the session with their numeric value already checked.
  const accepted = (set?.rows ?? []).filter((row) => typeof row.value === "number" && Number.isFinite(row.value) && row.value > 0);
  if (!sectionEl || !(accepted.length || set?.dropped?.length)) return;
  if (accepted.length) {
    section(document.querySelector('[data-bench="cpu-too"]'), { ...set, rows: accepted }, "cpu-too-title");
    for (const node of sectionEl.querySelectorAll("[data-cpu-accepted]")) node.hidden = false;
    // "Faster" only when every accepted change is measured faster (ratio above 1, unrounded).
    if (accepted.every((row) => typeof row.value === "number" && row.value > 1)) {
      document.getElementById("cpu-too-title").textContent = "Faster host-side prover work";
      const tocLink = document.querySelector('.toc a[href="#cpu-too"]');
      if (tocLink) tocLink.textContent = "Faster host-side prover work";
      for (const node of sectionEl.querySelectorAll("[data-cpu-faster]")) node.hidden = false;
    }
  }
  // A change whose comparison is still running is named as in progress, never shown as a ratio.
  const pendingSlot = document.querySelector('[data-bench="cpu-too"]');
  if (pendingSlot && set.pending && !accepted.length) pendingSlot.replaceChildren(el("p", set.pending));
  const dropped = document.querySelector('[data-bench="cpu-too-dropped"]');
  if (dropped && set.dropped?.length) {
    const list = el("ul");
    for (const line of set.dropped) list.appendChild(el("li", line));
    dropped.replaceChildren(el("p", "Considered and left out:"), list);
  }
  sectionEl.hidden = false;
  const toc = document.querySelector('.toc a[href="#cpu-too"]')?.closest("li");
  if (toc) toc.hidden = false;
}

export async function renderBenchmarks() {
  const slot = (name) => document.querySelector(`[data-bench="${name}"]`);
  let data;
  try {
    const response = await fetch(DATA_URL);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    data = await response.json();
  } catch (error) {
    console.warn("The benchmark data did not load.", error);
    for (const name of ["results", "identity"]) slot(name)?.remove();
    slot("compact")?.replaceChildren(
      el("p", "The benchmark data did not load. Serve this directory over HTTP.", { class: "empty" }),
    );
    return;
  }
  for (const name of ["identity"]) {
    const target = slot(name);
    if (!target) continue;
    if (data[name]) target.textContent = data[name];
    else target.remove();
  }
  let session = {};
  try {
    const response = await fetch(SESSION_URL);
    if (response.ok) session = fromSession(await response.json(), data);
  } catch (error) {
    console.warn("The session results did not load.", error);
  }
  results(slot("results"), [session.h2h]);
  // Accepted changes come only from the measurement session.
  cpuChanges({ ...data.cpu_changes, rows: session.cpuRows ?? [] });
  if (session.batch) {
    section(slot("batch-session"), session.batch, "batch-session-title");
    for (const node of document.querySelectorAll("[data-batch-session]")) node.hidden = false;
  }
  section(slot("compact"), data.compact_programs, "compact-title");
  section(slot("preview"), data.preview, "preview-title");
  section(slot("large"), data.large_circuit, "large-title");
  section(slot("checks"), data.checks, "oracle-title");
  if (session.sequential) section(slot("sequential"), session.sequential, "sequential-title");
  // The static source line of the sequential table follows the session.
  const src = document.querySelector("[data-session-source]");
  if (src && session.sequential?.source) {
    const [first, second] = src.querySelectorAll("a");
    const dir = session.sequential.source.replace(/\/RESULTS\.md$/, "");
    if (first) first.replaceWith(repo(`${dir}/RESULTS.md`, `${dir}/RESULTS.md`));
    if (second) second.replaceWith(repo("raw/", `${dir}/raw`));
  }
}

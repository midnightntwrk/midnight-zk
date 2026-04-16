#!/usr/bin/env python3
"""
Plot CPU usage over time from an IVC profiling JSON file.

Usage:
    python plot_profile.py ivc_step_0_profile.json [ivc_step_1_profile.json ...]

Produces one PNG per input file, e.g. ivc_step_0_profile_cpu.png.

Dependencies:
    pip install matplotlib numpy
"""

import json
import sys
import numpy as np
import matplotlib
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.ticker as mticker

matplotlib.rcParams["font.size"] = 9

# ── Colour assignment: group phases by prefix, assign a hue family ────────────
# Each entry: prefix → base colour.  Sub-phases inherit the same hue, slightly
# lightened/darkened so you can tell them apart.
GROUP_BASE = {
    "trace":         "#2171b5",   # blue   – witness generation
    "parse_advices": "#6baed6",   # light blue – parse_advices sub-phases
    "nu_poly":       "#31a354",   # green  – numerator polynomial
    "proof":         "#e6550d",   # orange – proof finalisation
    "fft":           "#756bb1",   # purple – FFTs
    "msm":           "#e377c2",   # pink   – MSMs
}
# Fine-grained overrides for specific phases that need to stand out.
PHASE_COLOR_OVERRIDE = {
    "trace::parse_advices":              "#08519c",
    "parse_advices::synthesize":         "#2171b5",
    "parse_advices::commit":             "#6baed6",
    "nu_poly::evaluate_numerator":       "#006d2c",
    "nu_poly::custom_gates":             "#74c476",
    "nu_poly::permutation_cosets":       "#41ab5d",
    "nu_poly::permutation_constraints":  "#238b45",
    "nu_poly::lookup_cosets":            "#a1d99b",
    "nu_poly::lookup_constraints":       "#31a354",
    "nu_poly::trash_cosets":             "#c7e9c0",
    "nu_poly::trash_constraints":        "#74c476",
    "nu_poly::advice_cosets":            "#005a32",
    "nu_poly::instance_cosets":          "#238b45",
    "proof::multi_open":                 "#a63603",
    "proof::compute_h_poly":             "#e6550d",
    "proof::write_evals":                "#fd8d3c",
    "proof::evaluate_permutation_data":  "#fdae6b",
    "proof::compute_linearization_poly": "#fdd0a2",
    "fft::coeff_to_extended":            "#54278f",
    "fft::lagrange_to_coeff":            "#9e9ac8",
    "msm::commit_lagrange":              "#980043",
    "msm::commit":                       "#d4b9da",
}
_FALLBACK = list(plt.cm.tab20.colors)
_fallback_seen: dict = {}


def phase_color(phase: str) -> str:
    if phase in PHASE_COLOR_OVERRIDE:
        return PHASE_COLOR_OVERRIDE[phase]
    prefix = phase.split("::")[0]
    if prefix in GROUP_BASE:
        return GROUP_BASE[prefix]
    if phase not in _fallback_seen:
        _fallback_seen[phase] = _FALLBACK[len(_fallback_seen) % len(_FALLBACK)]
    return _fallback_seen[phase]


def load(path: str) -> dict:
    with open(path) as f:
        return json.load(f)


def build_spans(times, phases):
    """Return list of (phase, t_start, t_end) for contiguous phase runs."""
    spans = []
    if not phases:
        return spans
    cur_phase, t_start = phases[0], times[0]
    for t, ph in zip(times[1:], phases[1:]):
        if ph != cur_phase:
            spans.append((cur_phase, t_start, t))
            cur_phase, t_start = ph, t
    spans.append((cur_phase, t_start, times[-1]))
    return spans


def plot_file(path: str):
    data = load(path)
    samples = data.get("cpu_samples", [])
    if not samples:
        print(f"  No cpu_samples in {path}, skipping.")
        return

    times    = np.array([s["time_ms"] for s in samples])
    phases   = [s.get("phase", "") for s in samples]
    n_cores  = len(samples[0]["cores"])

    user_total = np.array([sum(c["user_pct"] for c in s["cores"]) for s in samples])
    sys_total  = np.array([sum(c["sys_pct"]  for c in s["cores"]) for s in samples])
    per_core   = np.array(
        [[c["user_pct"] + c["sys_pct"] for c in s["cores"]] for s in samples]
    ).T  # (n_cores, n_samples)

    spans = build_spans(times, phases)

    # Unique phases in order of first appearance (for legend)
    seen_order = list(dict.fromkeys(ph for ph, _, _ in spans if ph))

    total_span = float(times[-1] - times[0])
    max_cpu    = n_cores * 100

    # ── Pre-compute arrow annotations so we know how many levels are needed ───
    MIN_LABEL_FRAC = 0.05
    MIN_ARROW_FRAC = 0.005
    px_per_ms = 3000 / total_span
    def label_hw_ms(text):
        return (len(text) * 5.5) / px_per_ms

    best: dict = {}
    for ph, t0, t1 in spans:
        if not ph:
            continue
        frac = (t1 - t0) / total_span
        if MIN_ARROW_FRAC <= frac < MIN_LABEL_FRAC:
            if ph not in best or (t1 - t0) > (best[ph][1] - best[ph][0]):
                best[ph] = (t0, t1)
    narrow = sorted([(ph, t0, t1) for ph, (t0, t1) in best.items()], key=lambda x: x[1])

    LEVELS   = [1.10, 1.38, 1.66, 1.94]
    level_rx = [-1e9] * len(LEVELS)
    arrow_assignments = []   # (ph, t0, t1, level)
    max_level_used = -1
    for ph, t0, t1 in narrow:
        mid  = (t0 + t1) / 2
        hw   = label_hw_ms(ph.split("::")[-1])
        chosen = len(LEVELS) - 1
        for i, rx in enumerate(level_rx):
            if mid - hw > rx:
                chosen = i
                break
        level_rx[chosen] = mid + hw
        max_level_used = max(max_level_used, chosen)
        arrow_assignments.append((ph, t0, t1, LEVELS[chosen]))

    # Strip height: 0.35 base + 0.15 per arrow level used (min 0.35, max ~1.0)
    n_arrow_levels = max_level_used + 1 if max_level_used >= 0 else 0
    strip_h = 0.35 + 0.18 * n_arrow_levels
    # Top margin: leave just enough room for the suptitle
    top_margin = 0.93 if n_arrow_levels == 0 else 0.91

    # ── Figure: 3 rows (strip | CPU area | heatmap) + colorbar column ─────────
    fig = plt.figure(figsize=(20, 10))
    gs  = fig.add_gridspec(
        3, 2,
        width_ratios=[1, 0.018],
        height_ratios=[strip_h, 1.8, 0.9],
        hspace=0.06,
        wspace=0.03,
    )
    ax_strip = fig.add_subplot(gs[0, 0])
    ax_cpu   = fig.add_subplot(gs[1, 0], sharex=ax_strip)
    ax_heat  = fig.add_subplot(gs[2, 0], sharex=ax_strip)
    ax_cbar  = fig.add_subplot(gs[2, 1])

    step_label = path.replace("\\", "/").split("/")[-1].replace("_profile.json", "")
    fig.suptitle(f"CPU Profile — {step_label}", fontsize=13, y=1.005)

    # ── Row 0: Phase strip ────────────────────────────────────────────────────
    ax_strip.set_xlim(times[0], times[-1])
    ax_strip.set_ylim(0, 1)
    ax_strip.axis("off")   # no ticks/labels — it's purely visual

    # Threshold: spans wider than this fraction of total get a label drawn inside.
    MIN_LABEL_FRAC = 0.05

    # Draw all coloured bands first
    for ph, t0, t1 in spans:
        color = phase_color(ph) if ph else "#eeeeee"
        ax_strip.barh(
            0.5, t1 - t0, left=t0, height=1.0,
            color=color, linewidth=0.5, edgecolor="white",
        )

    # Inside labels for wide spans
    for ph, t0, t1 in spans:
        if not ph:
            continue
        color = phase_color(ph)
        if (t1 - t0) / total_span >= MIN_LABEL_FRAC:
            label = ph.split("::")[-1]
            rgb = matplotlib.colors.to_rgb(color)
            luminance = 0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]
            text_color = "white" if luminance < 0.45 else "black"
            ax_strip.text(
                (t0 + t1) / 2, 0.5, label,
                ha="center", va="center",
                fontsize=7.5, color=text_color,
                fontweight="bold",
                rotation=90,
                clip_on=True,
            )

    # Arrow annotations — use the pre-computed assignments
    for ph, t0, t1, level in arrow_assignments:
        mid   = (t0 + t1) / 2
        label = ph.split("::")[-1]
        color = phase_color(ph)
        ax_strip.annotate(
            label,
            xy        =(mid, 1.0),
            xytext    =(mid, level),
            xycoords  =("data", "axes fraction"),
            textcoords=("data", "axes fraction"),
            ha="center", va="bottom",
            fontsize=6.5, color="black",
            clip_on=False,
            arrowprops=dict(
                arrowstyle="-|>",
                color=color,
                lw=1.0,
                mutation_scale=7,
                shrinkA=0, shrinkB=2,
            ),
        )

    # ── Row 1: Stacked CPU area chart ─────────────────────────────────────────
    # Faint vertical lines at phase boundaries
    for ph, t0, _ in spans:
        ax_cpu.axvline(t0, color="black", linewidth=0.4, alpha=0.35, zorder=1)

    ax_cpu.fill_between(times, 0, user_total,
                        color="#1a6faf", alpha=0.85, label="user", zorder=2)
    ax_cpu.fill_between(times, user_total, user_total + sys_total,
                        color="#e08030", alpha=0.80, label="sys",  zorder=2)

    ax_cpu.axhline(max_cpu, color="#cc0000", linestyle="--",
                   linewidth=0.9, label=f"max ({n_cores} cores)", zorder=3)

    ax_cpu.set_ylabel("Total CPU %\n(all cores)", fontsize=9)
    ax_cpu.set_ylim(0, max_cpu * 1.05)
    ax_cpu.tick_params(labelbottom=False)
    ax_cpu.legend(loc="upper right", fontsize=8, framealpha=0.9)
    ax_cpu.yaxis.set_major_formatter(mticker.FuncFormatter(
        lambda v, _: f"{int(v)}%"
    ))

    # ── Row 2: Per-core heatmap ───────────────────────────────────────────────
    im = ax_heat.imshow(
        per_core,
        aspect="auto",
        origin="upper",
        extent=[times[0], times[-1], n_cores - 0.5, -0.5],
        vmin=0, vmax=100,
        cmap="YlOrRd",
        interpolation="nearest",
    )
    for ph, t0, _ in spans:
        ax_heat.axvline(t0, color="black", linewidth=0.4, alpha=0.35)

    ax_heat.set_ylabel("Core", fontsize=9)
    ax_heat.set_xlabel("Time (ms)", fontsize=9)
    ax_heat.set_yticks(range(n_cores))
    ax_heat.set_yticklabels([str(i) for i in range(n_cores)], fontsize=7)

    cb = fig.colorbar(im, cax=ax_cbar)
    cb.set_label("CPU %", fontsize=8)

    # ── Legend: only phases that appear, matching strip colours exactly ───────
    handles = [
        mpatches.Patch(facecolor=phase_color(ph), edgecolor="grey",
                       linewidth=0.5, label=ph)
        for ph in seen_order
    ]
    fig.legend(
        handles=handles,
        loc="lower center",
        ncol=min(5, len(handles)),
        fontsize=7.5,
        framealpha=0.95,
        bbox_to_anchor=(0.5, 0.0),
        title="Phase (matches coloured strip above)",
        title_fontsize=8,
    )

    fig.subplots_adjust(top=top_margin, bottom=0.14)

    out = path.replace(".json", "_cpu.png")
    plt.savefig(out, dpi=150, bbox_inches="tight")
    print(f"  → saved {out}")
    plt.close(fig)


def main():
    paths = sys.argv[1:]
    if not paths:
        print("Usage: python plot_profile.py ivc_step_*.json")
        sys.exit(1)
    for path in paths:
        print(f"Processing {path} ...")
        plot_file(path)


if __name__ == "__main__":
    main()

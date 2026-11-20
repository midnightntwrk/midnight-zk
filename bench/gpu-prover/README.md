# GPU prover benchmarks

Benchmark harnesses and measurement data for the GPU prover. Nothing here is part of a
production crate: the package `midnight-gpu-prover-bench` is not published and holds only the
rc.1 bench executable.

| Path | What it is |
|---|---|
| [`rc1/`](rc1/README.md) | The rc.1 chain-circuit bench (`rc1-bench`), its scripts and per-GPU results. Built with no feature for the stock CPU prover, `rc1-bench-cuda` for the CUDA hooks, `rc1-bench-metal` for the Metal hooks (macOS only). |
| [`session/`](session/run.sh) | The measurement session behind the tables in `docs/gpu-prover/benchmarks.md`: the runner, the summary script and the raw rows. |
| [`abab/`](abab/README.md) | Interleaved A/B comparisons of two trees. |
| [`h2h/`](h2h/results/RESULTS.md) | Head-to-head CPU and GPU runs of the rc.1 bench. |
| [`compact/`](compact/README.md) | The Compact proof suite on midnight-proofs 0.8.x. A separate Cargo workspace with its own lock file; not a member of the root workspace. |
| [`large-circuit/`](large-circuit/README.md) | The k = 21 measurements made before the port to 0.9.0-rc.1. |

Run the scripts from the repository root, for example `bash bench/gpu-prover/rc1/scripts/build.sh`.

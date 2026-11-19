# Interleaved comparisons of two trees on the rc1 bench

Each file compares two trees with the public k = 21 circuit of `gpu-prover/bench/rc1`. The two binaries (`rc1-bench` with the feature `rc1-bench-cuda`) are built from the two trees with the same toolchain, lockfile and CUDA target, and share one key cache. The runs alternate: tree A, tree B, tree A, tree B, one prover process per run. A pair is one run of each tree.

Each run makes one cold proof and five warm proofs (`RC1_WARM=5`). The ratio of a pair is the median `prove_s` of the five warm proofs of tree A divided by that of tree B. A ratio above 1 means tree B is faster. Every proof was verified by the stock CPU verifier (`verified`).

Columns: `tree` (short commit id), `pair`, then the columns of the bench (`gpu-prover/bench/rc1/README.md`): `mode rep k threads start_load1 proof state prove_s verify_s verified msm_calls ntt_calls quotient_calls device_errors fallbacks declines hook_declines h2d_copies h2d_bytes d2h_copies d2h_bytes msm_d2h_copies msm_d2h_bytes stage peak_device_bytes gpu_model device_total_bytes`. `rep` is the bench's own repeat field (1 to 3) and carries no meaning here; `pair` is the pair number. `start_load1` is the one-minute load the process sampled at its gate before the cold proof.

## b0230e08-vs-ffa83b28.tsv

Trees: `b0230e08` (before the merge of upstream main) and `ffa83b28` (after it). `RAYON_NUM_THREADS=8`, k = 21, RTX 5090 Laptop GPU, three pairs.

| pair | b0230e08 warm median (s) | ffa83b28 warm median (s) | ratio | gate load (A / B) |
|---|---:|---:|---:|---|
| 1 | 4.787 | 4.779 | 1.002 | 1.89 / 1.65 |
| 2 | 4.846 | 4.807 | 1.008 | 1.87 / 1.86 |
| 3 | 4.727 | 4.825 | 0.980 | 1.55 / 1.72 |

Median ratio 1.002, range 0.980 to 1.008. Both trees make 11 device MSM calls and 7 device NTT calls per proof, with a device peak of 1.84 GiB and no fallback.

## ffa83b28-vs-inversion-scans.tsv

Trees: `ffa83b28` and the same tree with the chunked parallel batch inversion and the parallel exclusive scans applied (feature `prover-par`, which the bench's `gpu` build enables). The tree label of the second arm is `ffa83b28+inversion+scans`; the inversion commit measured here is the second version of that change (the rational advice path included). `RAYON_NUM_THREADS=8`, k = 21, RTX 5090 Laptop GPU, five pairs.

| pair | ffa83b28 warm median (s) | with inversion and scans (s) | ratio | gate load (A / B) |
|---|---:|---:|---:|---|
| 1 | 4.786 | 4.518 | 1.059 | 1.91 / 1.74 |
| 2 | 4.797 | 4.437 | 1.081 | 1.96 / 1.87 |
| 3 | 4.726 | 4.462 | 1.059 | 1.16 / 1.24 |
| 4 | 4.804 | 4.449 | 1.080 | 1.95 / 1.56 |
| 5 | 4.742 | 4.488 | 1.057 | 1.22 / 1.21 |

Median ratio 1.059, range 1.057 to 1.081. Device calls per proof and the device peak (1.84 GiB) are the same in both arms. The inversion change that this pull request carries is narrower than the version measured here: it inverts the permutation and LogUp denominators in parallel and leaves the rational advice path as it is in stock. The measurement session in `gpu-prover/bench/session/` measures the final change.

## lookup-k20-ffa83b28-vs-scans.tsv

Trees: `ffa83b28` and the same tree with the parallel exclusive scans for the permutation product and the LogUp sum (`ffa83b28+scans`). The rc1 circuit has no lookups, so this comparison uses the seeded random circuit of the midnight-proofs `gpu-test` feature (`gpu::test_switches::RandomCircuit`) at k = 20: random gates, one batched LogUp lookup, a copy constraint and a trash argument. Each run makes one cold proof and five warm proofs with the device hooks installed; every proof verified. Columns: `tree`, `pair`, `bench`, `k`, `threads`, `proof` (index), `state`, `prove_s`, `proof_bytes`, `verified`, `device_bytes`, `declines` (class:reason:count, cumulative in the process; the small MSMs below the device minimum run on the CPU). `RAYON_NUM_THREADS=8`, RTX 5090 Laptop GPU, three pairs.

| pair | ffa83b28 warm median (s) | with scans (s) | ratio |
|---|---:|---:|---:|
| 1 | 8.927 | 8.988 | 0.993 |
| 2 | 8.986 | 8.888 | 1.011 |
| 3 | 9.035 | 8.956 | 1.009 |

Median ratio 1.009, range 0.993 to 1.011: about 50 ms of a 9 s proof. The scans are not in this pull request: they were neutral on the rc1 bench and on this circuit.

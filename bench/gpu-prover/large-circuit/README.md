# Large-circuit measurements (pre-port)

This directory holds the k = 21 measurements of the GPU prover design. They
were taken with the hooks of this design on midnight-proofs 0.8.3 and a CUDA
backend of the same design, before the port to midnight-proofs 0.9.0-rc.1. The
circuit is one k = 21 circuit. Its keys and inputs are not part of this
repository. Only the public measurements are here.

## Files

| File | Content |
|---|---|
| `gpu-k21.tsv` | One row per GPU model: the warm timed set (n = 5), the cold proof, phase and MSM medians, device calls, fallbacks, device peak, host high-water mark, resident copies, and one CPU-only proof on the same machine. |
| `cpu-gpu-k21-rtx-5080-laptop.tsv` | The CPU path and the GPU path of one earlier build on one machine with an RTX 5080 Laptop GPU, with the phase split. Each row pools 5 warm proofs from three runs. A warm proof is one made after another proof in the same process. No quiet-gate record exists for these runs. |

## Method of `gpu-k21.tsv`

- One proof makes 23 MSMs of 2^21 terms, 35 NTTs, 17 coset transforms and one
  quotient on the device.
- A timed set is one cold proof (the first after the start) and 5 warm proofs.
  The tables give the median, minimum and maximum of the warm proofs.
- A set started only when the 1-minute load of the machine was below 2 (the
  quiet gate). The load during the set is the prover itself.
- Every GPU proof had 0 fallbacks and passed the stock verifier.
- The phases are the four timed sections of the prover: advice (phase 1), the
  lookup, permutation and trash commitments (phase 2, "trace"), the quotient
  (phase 3) and the evaluations with the multi-open argument (phase 4).
- `platform` is `Linux` for a native Linux host and `WSL2` for a Linux guest
  on Windows. `pcie_link` is the link that the device reported (generation and
  width). `driver` is the NVIDIA driver version.
- `cpu_only_prove_s_n1` is one proof by a build without the CUDA toolkit on
  the same machine (n = 1, no timed set).

The four machines have different CPUs, power limits and buses. Compare a GPU
row with the CPU figure of the same row only. Do not rank the GPU models with
this table.

## Columns of `gpu-k21.tsv`

| Column | Unit | Meaning |
|---|---|---|
| `gpu_model` | | Device name |
| `platform`, `driver`, `pcie_link`, `device_mib` | | Host platform, driver version, PCIe link, device memory |
| `n_warm`, `warm_median_s`, `warm_min_s`, `warm_max_s` | s | Warm timed set |
| `cold_s` | s | First proof after the start |
| `msm_s_median` | s | Time of the 23 MSMs of one proof |
| `msm_calls`, `ntt_calls`, `coset_calls`, `quotient_calls`, `fallbacks` | count | Device calls of one proof |
| `phase1_advice_s` to `phase4_finalise_s` | s | Phase medians of the warm proofs |
| `device_peak_gib`, `host_hwm_gib` | GiB | Device peak of the prover and host high-water mark |
| `cpu_only_prove_s_n1` | s | One CPU-only proof |
| `resident_gib`, `resident_uploads` | GiB, count | Resident proving-key copies of one proof |

The results of the code in this pull request on 0.9.0-rc.1 go into
`docs/gpu-prover/benchmarks.md`, section 4, when they exist.

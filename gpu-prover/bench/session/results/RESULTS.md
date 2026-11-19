# Measurement session 2026-11-18

Tree `9070a373` on base `4bea43d4`. NVIDIA GeForce RTX 5090 Laptop GPU, 24463 MiB, 615.78.08, 3090 MHz, 14001 MHz, [N/A]. CPU: Intel(R) Core(TM) Ultra 9 275HX cores=24. 24 prover threads. Every proof was checked by the stock CPU verifier.

Clocks: CPU mean core clock 1409 to 4422 MHz (median 3175); GPU SM clock 172 to 2497 MHz (median 180), memory clock 405 to 14001 MHz (median 405).

Temperatures: CPU package 51 to 102 C (median 71), 57 C at the start; GPU 44 to 60 C (median 47).

## Single proofs by size (seconds)

| k | CPU cold | GPU cold | CPU warm median (min-max) | GPU warm median (min-max) | Warm speed-up | GPU device peak | GPU declines |
|---|---|---|---|---|---|---|---|
| 14 | 0.151 | 0.252 | 0.163 (0.156-0.163) | 0.110 (0.108-0.112) | 1.48x | 42.5 MB | 2 hook |
| 15 | 0.323 | 0.268 | 0.346 (0.344-0.352) | 0.131 (0.131-0.134) | 2.63x | 59.5 MB | 0  |
| 16 | 0.561 | 0.356 | 0.566 (0.558-0.579) | 0.199 (0.198-0.221) | 2.84x | 89.9 MB | 0  |
| 17 | 1.160 | 0.553 | 1.084 (1.061-1.212) | 0.363 (0.347-0.368) | 2.98x | 150.7 MB | 0  |
| 18 | 2.208 | 0.849 | 2.130 (2.053-2.151) | 0.693 (0.687-0.708) | 3.07x | 272.3 MB | 0  |
| 19 | 4.326 | 1.243 | 4.215 (4.130-4.325) | 1.046 (1.045-1.076) | 4.03x | 515.6 MB | 0  |
| 20 | 8.544 | 2.404 | 8.549 (8.410-8.590) | 2.282 (2.159-2.343) | 3.75x | 1002.1 MB | 0  |
| 21 | 17.576 | 4.714 | 17.917 (17.740-17.920) | 4.374 (4.354-4.459) | 4.10x | 1975.2 MB | 0  |

## Sequential run at k = 16

| Warm proofs | GPU proofs/s | CPU proofs/s |
|---|---|---|
| 1 | 5.07 | 1.75 |
| 4 | 5.03 | 1.74 |
| 16 | 4.89 | 1.71 |
| 64 | 4.85 | 1.71 |

## Batch proving at k = 16

| Batch size | GPU proofs/s | CPU proofs/s | GPU busy fraction |
|---|---|---|---|
| 1 | 1.69 | 1.69 | 0.04 |
| 2 | 1.99 | 1.86 | 0.22 |
| 4 | 2.12 | 1.74 | 0.21 |
| 8 | 2.21 | 1.91 | 0.22 |

## Alternating comparisons

Ratio = warm median without the change / warm median with it, per pair; median over pairs.

| Change | Bench | k | Pairs | Ratio (min-max) |
|---|---|---|---|---|
| Parallel batch inversion | rc1-gpu | 21 | 5 | 1.022 (1.011-1.031) |

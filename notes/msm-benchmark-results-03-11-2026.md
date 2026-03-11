# MSM Benchmark Results — March 11, 2026

BLS12-381 G1, 256-bit scalars, 2^20 (1,048,576) points.
GCP VMs: Intel Ice Lake @ 2.60GHz, AVX-512 IFMA supported.

## 4-core VM (n2-standard-4)

| Implementation | Time | Notes |
|:---|:---:|:---|
| VROOM C++ (parallel) | **381 ms** | Native, auto threads, clang++ -O3 -mavx512ifma |
| VROOM C++ (1 thread) | **605 ms** | Native, AVX512-IFMA |
| BLST C (Pippenger) | **635 ms** | Native single-threaded via C API |
| Blst Rust (multi_exp) | 3,744 ms | Rayon multi-threaded (4 cores) |
| msm_best Rust | 4,080 ms | Rayon multi-threaded (4 cores) |
| VROOM FFI (4t parallel) | 10,246 ms | Via Rust FFI wrapper |
| VROOM FFI (1 thread) | 17,917 ms | Via Rust FFI wrapper |

## 16-core VM (n2-standard-16)

| Implementation | Time | Notes |
|:---|:---:|:---|
| VROOM C++ (parallel) | **394 ms** | Native, auto threads |
| VROOM C++ (1 thread) | **570 ms** | Native, AVX512-IFMA |
| BLST C (Pippenger) | **616 ms** | Native single-threaded via C API |
| Blst Rust (multi_exp) | 952 ms | Rayon multi-threaded (16 cores) |
| msm_best Rust | 1,373 ms | Rayon multi-threaded (16 cores) |
| VROOM FFI (16t parallel) | 11,353 ms | Via Rust FFI wrapper |
| VROOM FFI (1 thread) | 15,952 ms | Via Rust FFI wrapper |

## Full Range Results (16-core VM)

| Size | Blst Rust | msm_best Rust | Vroom FFI (1t) | Vroom FFI (16t) |
|:---:|:---:|:---:|:---:|:---:|
| 2^8 | **1.03 ms** | 2.25 ms | 11.05 ms | 10.06 ms |
| 2^10 | **2.51 ms** | 5.35 ms | 30.39 ms | 39.92 ms |
| 2^12 | **8.45 ms** | 14.67 ms | 100.96 ms | 93.80 ms |
| 2^14 | 29.59 ms | **28.03 ms** | 364.73 ms | 264.74 ms |
| 2^16 | **96.79 ms** | 98.49 ms | 1,181 ms | 904.04 ms |
| 2^18 | **264.96 ms** | 359.00 ms | 4,178 ms | 3,232 ms |
| 2^20 | **939.54 ms** | 1,366 ms | 16,017 ms | 11,505 ms |

## Key Findings

1. **VROOM C++ native is fastest single-threaded MSM**: 570ms vs BLST 616ms (8% faster)
2. **VROOM C++ parallel is overall winner**: 394ms on 16 cores
3. **FFI wrapper has ~28x overhead**: VROOM native 570ms vs FFI 15,952ms — critical bug
4. **Rust Blst multi_exp scales well**: 3.7s (4 cores) → 0.95s (16 cores) = 3.9x
5. **VROOM parallel saturates early**: 381ms (4 cores) → 394ms (16 cores), no improvement

## FFI Wrapper Overhead Investigation

The 28x overhead from C++ native to Rust FFI wrapper needs investigation.
Likely causes: point generation method, data conversion, or compilation flags.
See: `vroom-msm-sys/src/wrapper.cpp` vs `VROOM/src/bench_msm.cpp`.

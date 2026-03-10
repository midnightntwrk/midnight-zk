# BLST vs VROOM: MSM on BLS12-381 Comparison

## Field Arithmetic — The Fundamental Divergence

| | BLST | VROOM |
|---|---|---|
| **Representation** | 6×64-bit limbs, Montgomery form | 8×52-bit limbs, RNS Montgomery across 2 channels |
| **Multiply instruction** | `mulx` (64-bit) + `adox`/`adcx` (carry chains) | `vmadd52lo`/`vmadd52hi` (AVX512-IFMA, 8-wide) |
| **Parallelism** | Sequential scalar pipeline | 8 limb-multiplications per instruction (SIMD) |
| **Reduction** | Classic Montgomery reduction | RNS base conversion (matrix-vector multiply) |
| **Redundancy** | Fully reduced after each op | Allows values up to ~3p before reduction; batches reductions |

BLST uses hand-tuned x86-64 assembly exploiting ADX/MULX for a tight sequential pipeline. VROOM vectorizes across limbs using AVX512-IFMA's 52-bit fused multiply-add, processing 8 limbs in parallel per 512-bit register. The tradeoff: VROOM gets ~3-4x faster field multiplication but pays for expensive RNS base conversions when reducing.

## EC Point Representation

| | BLST | VROOM |
|---|---|---|
| **Internal coords** | XYZZ (X, Y, Z, ZZ=Z²) | Projective/Jacobian (X, Y, Z) |
| **Mixed addition cost** | ~8M + 2S (saves Z² recomputation) | ~9M + 5A |
| **Doubling** | Standard XYZZ doubling | Standard projective doubling |

BLST's XYZZ coordinates cache Z² to save one multiplication per mixed addition — a ~10-15% saving at the EC level. VROOM uses standard projective coordinates, relying on raw field speed to compensate.

## MSM Algorithm — Both Use Pippenger, Different Details

Both implement Pippenger's bucket method with the same high-level structure: decompose scalars into windows → scatter points into buckets → integrate buckets via summation-by-parts → accumulate windows.

Key differences:

| | BLST (via `p1_affines::mult`) | VROOM (`pippenger.hpp`) |
|---|---|---|
| **Scalar encoding** | Raw unsigned digits | Raw unsigned digits |
| **Window size** | Internal heuristic (~15-16 for 2^20) | `log2(n) - 3` (e.g., 17 for 2^20) |
| **Bucket count** | 2^w - 1 per window | 2^w - 1 per window |
| **Small-n dispatch** | Always Pippenger | n=1: GLV scalar mul; n<32: naive accumulation |
| **Parallelism** | Internal threading in BLST | Explicit chunking across windows |

The custom Rust `msm_best` (used for n > 2^18) adds **Booth encoding** on top — halving bucket count to 2^(w-1) using signed digits. Neither BLST's nor VROOM's Pippenger uses this optimization.

## Scalar Multiplication (Single Point)

| | BLST | VROOM |
|---|---|---|
| **Algorithm** | `blst_p1_mult` — internal windowed method | GLV endomorphism: k → (k1, k2), 128-bit half-scalars |
| **Doublings** | ~255 | ~128 (halved via endomorphism) |
| **Precomputation** | Minimal | 2^4 = 16 table entries per channel |

VROOM's GLV decomposition using the cube root of unity endomorphism `φ(x,y) = (βx, y)` is a significant win for individual scalar muls — halving the number of doublings. BLST likely uses similar techniques internally but the Rust wrapper just calls `blst_p1_mult` as a black box.

## Compile-Time Safety — VROOM's Unique Feature

VROOM tracks overflow bounds at the C++ type level:

```
Bounds<a,b> + Bounds<c,d> = Bounds<a+c, b+d>
```

Every arithmetic operation produces a new type encoding the possible value range. `static_assert` fires at compile time if any operation could overflow a 52-bit limb. This is enforced through the full stack: `Bounds` → `BoundedElement` → `SmallElement`/`ExpandedElement` → `BoundedRing`. BLST has no equivalent — correctness relies on manual auditing of assembly.

## Benchmarks (Intel Sapphire Rapids)

| Operation | BLST | VROOM | Speedup |
|---|---|---|---|
| G1 Addition | 797 ns | 225 ns | **3.5x** |
| G1 Mixed Add | 616 ns | 216 ns | **2.9x** |
| G1 Doubling | 349 ns | 203 ns | **1.7x** |
| G1 Scalar Mul | 97.5 µs | 45 µs | **2.2x** |
| MSM 2^20 (1T) | 636 ms | 596 ms | **1.07x** |
| MSM 2^20 (4T) | — | 305 ms | **2.1x vs BLST 1T** |

The paradox: VROOM is 3-4x faster at field arithmetic and 2x faster at scalar mul, but only ~7% faster at large MSM. This is because Pippenger is dominated by **memory access patterns** (bucket scatter/gather), not raw arithmetic. BLST's prefetching and XYZZ coordinates partially close the gap at the MSM level.

## Summary of Tradeoffs

**BLST strengths:**
- Mature, production-hardened, widely deployed
- XYZZ coordinates optimize the mixed-addition bottleneck in Pippenger
- Better memory access patterns (prefetching during bucket scatter)
- No AVX512-IFMA hardware requirement — works everywhere

**VROOM strengths:**
- 3-4x faster field arithmetic via AVX512-IFMA vectorization
- Compile-time overflow safety eliminates a class of bugs
- GLV endomorphism for single scalar mul (2x fewer doublings)
- Redundant representation amortizes reductions across batched operations
- Clean C++20 template architecture

**The core insight:** For MSM at scale, the bottleneck shifts from arithmetic to memory — which is why VROOM's massive field-level speedup compresses to only ~7% at 2^20-point MSM. The real wins from VROOM would come from combining its fast arithmetic with better bucket management (signed digits, prefetching, XYZZ) or from operations where arithmetic dominates (pairing, single scalar mul, small MSMs).

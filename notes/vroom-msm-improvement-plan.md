# VROOM MSM Improvement Plan

Based on comparative analysis of BLST vs VROOM (see `blst-vs-vroom-msm-comparison.md`).

## 1. GLV Endomorphism Inside Pippenger (High Impact, ~30-40% fewer windows)

VROOM already implements GLV for single scalar mul but **doesn't use it in Pippenger**. The idea:

- Decompose each 255-bit scalar k into two ~128-bit half-scalars: `k = k1 + k2·λ (mod r)`
- Replace each `(k, P)` pair with two pairs: `(k1, P)` and `(k2, φ(P))` where `φ(x,y) = (βx, y)`
- Computing φ(P) is nearly free — one field multiplication on x
- **Result:** double the points, but halve the scalar bit-length (128 vs 255 bits)
- Same number of bucket additions, but **~half the windows** → half the integration passes and doublings between windows

This is the single biggest algorithmic win available because it directly attacks the window count, which determines how many times the entire bucket integration loop runs.

## 2. Booth Encoding / Signed Digits (Medium-High Impact, ~10-15%)

Currently VROOM uses unsigned digit decomposition: digit range `[0, 2^w-1]`, requiring `2^w - 1` buckets. The Rust `msm_best` uses Booth encoding:

- Extract `w+1` overlapping bits per window, convert to signed digit in `[-2^(w-1), +2^(w-1)]`
- Negative digits → negate the point (free: just negate y-coordinate)
- **Bucket count halved:** `2^(w-1)` instead of `2^w`

At w=17 (VROOM's choice for 2^20 points), this means 65K buckets instead of 131K:
- **Memory halved:** ~9MB instead of ~18MB — much better L3 cache residency
- **Integration cost halved:** fewer buckets to traverse in summation-by-parts
- **Implementation effort:** Low — modify `extract_bits` to extract w+1 bits, add sign handling in scatter

Combined with GLV (#1), you'd use signed digits on 128-bit half-scalars, compounding both savings.

## 3. Prefetching in Bucket Scatter (Medium Impact, ~10-20% at large n)

VROOM's scatter loop has random access into the bucket array. At 2^20 points with 65K+ buckets (each ~144 bytes), the working set far exceeds L2 cache. Each bucket access is likely a cache miss.

```cpp
// Current: random access, no prefetch
buckets[digit] = add_mixed_point(buckets[digit], points[i]);

// Improved: prefetch next bucket while processing current
auto next_digit = extract_bits(scalars[i+1], window, wbits);
_mm_prefetch(&buckets[next_digit], _MM_HINT_T0);
buckets[digit] = add_mixed_point(buckets[digit], points[i]);
```

BLST does this internally and it's a key reason BLST stays competitive despite slower field arithmetic. This is low-effort, high-return for large n.

## 4. XYZZ Coordinates (Medium Impact, ~8-10% on EC additions)

Replace `ProjectivePoint(X, Y, Z)` with `XYZZPoint(X, Y, ZZ, ZZZ)` where `ZZ = Z²`, `ZZZ = Z³`:

| Operation | Current (Projective) | XYZZ |
|---|---|---|
| Mixed addition | ~10M | ~8M + 2S |
| Storage | 3 field elements | 4 field elements |

The extra storage (4 vs 3 elements) trades ~33% more memory for ~20% fewer multiplications per mixed addition. Since scatter is the dominant phase and each scatter step is one mixed addition, this directly speeds up the bottleneck. VROOM's fast IFMA multiplications make the absolute savings smaller than for BLST, but it's still free performance.

## 5. Batch Affine Addition (High Impact but Complex, ~15-25%)

The Rust `msm_best` uses Montgomery's trick: batch 64 point additions with a **single field inversion** instead of per-addition inversions. Cost drops from ~10M per addition to ~3M + amortized inversion.

The challenge for VROOM: field inversion in RNS Montgomery is expensive (Fermat's method: `a^(p-2) mod p` ≈ 380+ multiplications). But amortized over 64 points, that's ~6M extra per point — still saving vs 10M.

The hybrid approach from `msm_best` is key:
- **Cold buckets** (first hit): schedule for batch affine addition
- **Hot buckets** (already occupied): use Jacobian mixed addition directly
- This avoids the scheduling overhead for frequently-hit buckets while batching the long tail

This is the most complex optimization but has the highest ceiling.

## 6. Window-Level Parallelization (Scaling improvement)

Current VROOM parallelism: split points across threads, each with its own bucket array, then merge. This requires an O(nbuckets × nthreads) merge phase.

Alternative: **parallelize across windows** instead of across points. Each window's scatter + integrate is fully independent. With ~8 windows (128-bit scalars from GLV / 17-bit window), this gives natural 8-way parallelism with **zero merge overhead**.

The downside is that each thread touches all points (worse cache locality for points). A hybrid approach — window-parallel for outer loop, point-parallel within each window — could get the best of both.

## 7. Lazy Reduction (Low-Hanging Fruit, ~5%)

VROOM's redundant RNS representation already allows values up to ~3p. During the scatter loop, multiple mixed additions to the same bucket accumulate bounds. Currently each mixed addition calls `batch_reduce`. If bounds permit, defer reduction across 2-3 additions before reducing — saving RNS base conversions (the most expensive step in VROOM's pipeline).

## Prioritized Roadmap

| Priority | Optimization | Effort | Expected Gain | Compounds With |
|---|---|---|---|---|
| **P0** | Booth encoding | Low | 10-15% | Everything |
| **P0** | Prefetching | Low | 10-20% | Everything |
| **P1** | GLV in Pippenger | Medium | 30-40% fewer windows | Booth |
| **P1** | XYZZ coordinates | Medium | 8-10% | Batch affine |
| **P2** | Batch affine addition | High | 15-25% | XYZZ, Booth |
| **P2** | Window-level parallelism | Medium | Better scaling | GLV (more windows) |
| **P3** | Lazy reduction | Low | ~5% | All |

**Conservative compound estimate:** Booth + prefetch + GLV could yield **~40-50% improvement** over current VROOM single-threaded MSM at 2^20 points, turning the current 596ms → ~300-350ms single-threaded, which would be a decisive win over BLST's 636ms even without multi-threading.

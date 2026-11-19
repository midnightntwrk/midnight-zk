# Benchmarks

Every number in this document comes from a file in the repository. The
Compact numbers come from [`gpu-prover/bench/compact/results/`](../../gpu-prover/bench/compact/results/compare-rtx-5080-laptop.tsv).
The large-circuit numbers come from [`gpu-prover/bench/large-circuit/`](../../gpu-prover/bench/large-circuit/README.md).
Each table names the GPU model and the platform.

## Which code was measured

The Compact suite and the large circuit were measured with the hooks of this
design on midnight-proofs 0.8.3, with a CUDA backend of the same design. The
Midnight proof server pins midnight-proofs 0.8.2, and 0.8.3 is compatible with
it, so the 0.8.3 numbers apply to the proof server stack. The pull request
carries the same design on midnight-proofs 0.9.0-rc.1. The 0.8.3 backport is
not in the pull request. Section 4 gives numbers for the code of this pull
request on 0.9.0-rc.1, on a public k = 21 circuit.

## 1. Compact suite: CPU and GPU

**Setup.** One machine with an RTX 5080 Laptop GPU (sm_120) and an Intel Core
Ultra 9 290HX Plus, x86_64, 24 prover threads, rustc 1.99.1. The CPU baseline
is stock midnight-proofs 0.8.3. The GPU run is the hooked 0.8.3.

Both runs use
the same jobs and the same command: one warm-up and 5 timed repetitions per
proof. The times are the prover call (witness generation and `create_proof`)
as the median of the 5 repetitions. Key loading and verification are timed
apart. The method is in [compact-suite.md](compact-suite.md) and the
[benchmark README](../../gpu-prover/bench/compact/README.md).

**Comparison rule.** A proof is checked in one of two ways:

- `bytes-equal`: all CPU repetitions of the proof give the same bytes, and
  every GPU repetition gives those bytes too. This holds for 39 proofs (k 6 to
  10), with the same thread count.
- `verified`: the other 94 proofs change from one repetition to the next, also
  on the CPU with one thread. The circuits library draws a point from `OsRng`
  during synthesis (the foreign-curve chip), so the prover's seeded RNG does
  not make them reproducible. Each GPU repetition of these proofs verifies
  under the stock verifier, and its public inputs equal those of the stock run.

All 798 GPU proofs (133 proofs, 6 runs each) pass their check. No hook fell
back to the CPU.

### 1.1 Totals: RTX 5080 Laptop GPU

| Quantity | CPU | GPU |
|---|---:|---:|
| Proofs | 133 | 133 |
| Sum of per-proof medians | 77.25 s | 43.74 s |
| Median of per-proof medians | 0.388 s | 0.297 s |
| p95 of per-proof medians | 2.565 s | 1.103 s |
| Speed-up of the sums | | 1.77 |
| Checks | | 39 `bytes-equal`, 94 `verified` |

### 1.2 By k: RTX 5080 Laptop GPU

| k | Proofs | CPU s (median) | GPU s (median) | Speed-up (sum) | Speed-up range | Checks (bytes-equal / verified) |
|---:|---:|---:|---:|---:|---|---|
| 6 | 7 | 0.024 | 0.026 | 0.92 | 0.86 to 1.01 | 7 / 0 |
| 7 | 15 | 0.026 | 0.027 | 0.98 | 0.85 to 1.22 | 9 / 6 |
| 8 | 14 | 0.030 | 0.031 | 0.99 | 0.89 to 1.17 | 11 / 3 |
| 9 | 9 | 0.044 | 0.040 | 1.08 | 0.98 to 1.12 | 9 / 0 |
| 10 | 3 | 0.064 | 0.058 | 1.14 | 1.04 to 1.25 | 3 / 0 |
| 11 | 2 | 0.220 | 0.202 | 1.08 | 1.08 to 1.09 | 0 / 2 |
| 13 | 47 | 0.400 | 0.307 | 1.29 | 1.20 to 1.43 | 0 / 47 |
| 14 | 16 | 0.754 | 0.470 | 1.60 | 1.48 to 1.70 | 0 / 16 |
| 15 | 8 | 1.397 | 0.673 | 2.06 | 1.91 to 2.16 | 0 / 8 |
| 16 | 11 | 2.565 | 1.103 | 2.34 | 2.28 to 2.39 | 0 / 11 |
| 17 | 1 | 4.726 | 1.880 | 2.51 | 2.51 | 0 / 1 |

Small proofs are slower on the GPU: 24 proofs at k 6 to 9 have a speed-up
below 1. At those sizes the transfer and launch costs are larger than the CPU
work. The 0.8.3 backend of this run offered the NTT, coset and quotient work to
the device at every size and the MSM only from 2^14 terms. The pull request
sets a common threshold, `MIDNIGHT_GPU_MIN_K` (default 14), below which every
call stays on the CPU. The speed-up grows with k: 1.29 at k = 13, 2.51 at
k = 17.

### 1.3 Per proof: RTX 5080 Laptop GPU

The columns give the CPU and GPU median prove time of 5 repetitions, the
speed-up and the check. The last column gives the device calls of one
repetition (MSM / NTT / coset / quotient / fallbacks), the largest count of any
repetition. A circuit proved with the keys
of another program names that program.

| Program | Circuit | k | CPU s | GPU s | Speed-up | Check | Device calls (MSM/NTT/coset/quotient/fallbacks) |
|---|---|---:|---:|---:|---:|---|---|
| t02-counter-example | increment | 6 | 0.024 | 0.027 | 0.86 | bytes-equal | 0/26/26/1/0 |
| t03-counter-compiler | increment | 6 | 0.024 | 0.026 | 0.89 | bytes-equal | 0/26/26/1/0 |
| t04-welcome | check_in | 6 | 0.024 | 0.024 | 1.01 | bytes-equal | 0/26/26/1/0 |
| t04-welcome | check_in | 6 | 0.023 | 0.026 | 0.87 | bytes-equal | 0/26/26/1/0 |
| t04-welcome | check_in | 6 | 0.024 | 0.027 | 0.88 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | echoStored | 6 | 0.022 | 0.023 | 0.95 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | echoStored | 6 | 0.025 | 0.025 | 1.00 | bytes-equal | 0/26/26/1/0 |
| a01-adt-counter | test_big_increment | 7 | 0.028 | 0.023 | 1.22 | bytes-equal | 0/26/26/1/0 |
| a04-map-bool-map-counter | test | 7 | 0.026 | 0.026 | 0.99 | bytes-equal | 0/26/26/1/0 |
| d06-nft | ownerOf | 7 | 0.025 | 0.030 | 0.85 | verified | 0/26/26/1/0 |
| d06-nft | getApproved | 7 | 0.028 | 0.025 | 1.10 | verified | 0/26/26/1/0 |
| t01-tiny | get | 7 | 0.027 | 0.027 | 1.01 | bytes-equal | 0/26/26/1/0 |
| t01-tiny | get | 7 | 0.025 | 0.025 | 0.96 | bytes-equal | 0/26/26/1/0 |
| t01-tiny | get | 7 | 0.024 | 0.027 | 0.89 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | add (x02-composable-inner keys) | 7 | 0.028 | 0.027 | 1.03 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | add (x02-composable-inner keys) | 7 | 0.024 | 0.027 | 0.92 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | add (x02-composable-inner keys) | 7 | 0.024 | 0.025 | 0.96 | bytes-equal | 0/26/26/1/0 |
| x02-composable-inner | add | 7 | 0.025 | 0.027 | 0.92 | bytes-equal | 0/26/26/1/0 |
| z03-block-time | testBlockTimeGt | 7 | 0.027 | 0.028 | 0.97 | verified | 0/26/26/1/0 |
| z03-block-time | testBlockTimeGte | 7 | 0.028 | 0.031 | 0.92 | verified | 0/26/26/1/0 |
| z03-block-time | testBlockTimeLt | 7 | 0.027 | 0.028 | 0.96 | verified | 0/26/26/1/0 |
| z03-block-time | testBlockTimeLte | 7 | 0.026 | 0.026 | 0.99 | verified | 0/26/26/1/0 |
| a01-adt-counter | test_all | 8 | 0.029 | 0.025 | 1.17 | bytes-equal | 0/26/26/1/0 |
| a02-set-field | test | 8 | 0.030 | 0.029 | 1.03 | bytes-equal | 0/26/26/1/0 |
| a03-map-field-field | test | 8 | 0.029 | 0.032 | 0.92 | bytes-equal | 0/26/26/1/0 |
| a08-kernel | test | 8 | 0.030 | 0.029 | 1.01 | bytes-equal | 0/26/26/1/0 |
| d06-nft | balanceOf | 8 | 0.030 | 0.031 | 0.96 | bytes-equal | 0/26/26/1/0 |
| d06-nft | balanceOf | 8 | 0.031 | 0.030 | 1.04 | verified | 0/26/26/1/0 |
| x01-composable-outer | add | 8 | 0.030 | 0.030 | 1.01 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | addViaArg | 8 | 0.030 | 0.034 | 0.89 | verified | 0/26/26/1/0 |
| x01-composable-outer | addViaConst | 8 | 0.030 | 0.030 | 0.98 | bytes-equal | 0/26/26/1/0 |
| x01-composable-outer | setInner | 8 | 0.032 | 0.033 | 0.99 | verified | 0/26/26/1/0 |
| z02-unshielded-tokens | getUnshieldedBalanceGtTest | 8 | 0.031 | 0.035 | 0.90 | bytes-equal | 0/26/26/1/0 |
| z02-unshielded-tokens | getUnshieldedBalanceLtTest | 8 | 0.032 | 0.031 | 1.03 | bytes-equal | 0/26/26/1/0 |
| z02-unshielded-tokens | getUnshieldedBalanceTest | 8 | 0.031 | 0.031 | 1.02 | bytes-equal | 0/26/26/1/0 |
| z02-unshielded-tokens | receiveUnshieldedTest | 8 | 0.032 | 0.033 | 0.96 | bytes-equal | 0/26/26/1/0 |
| d06-nft | approve | 9 | 0.046 | 0.043 | 1.07 | bytes-equal | 0/26/26/1/0 |
| d06-nft | setApprovalForAll | 9 | 0.044 | 0.039 | 1.12 | bytes-equal | 0/26/26/1/0 |
| d06-nft | isApprovedForAll | 9 | 0.044 | 0.040 | 1.11 | bytes-equal | 0/26/26/1/0 |
| d06-nft | isApprovedForAll | 9 | 0.050 | 0.045 | 1.12 | bytes-equal | 0/26/26/1/0 |
| z02-unshielded-tokens | sendUnshieldedToContractTest | 9 | 0.044 | 0.045 | 0.98 | bytes-equal | 0/26/26/1/0 |
| z02-unshielded-tokens | sendUnshieldedToSelfTest | 9 | 0.043 | 0.040 | 1.07 | bytes-equal | 0/26/26/1/0 |
| z02-unshielded-tokens | sendUnshieldedToUserTest | 9 | 0.044 | 0.042 | 1.06 | bytes-equal | 0/26/26/1/0 |
| z04-set-qualified-coin | test_QualifiedShieldedCoinInfo | 9 | 0.041 | 0.036 | 1.12 | bytes-equal | 0/26/26/1/0 |
| z04-set-qualified-coin | test_QualifiedShieldedCoinInfo | 9 | 0.038 | 0.034 | 1.11 | bytes-equal | 0/26/26/1/0 |
| a05-list-field | test | 10 | 0.059 | 0.051 | 1.15 | bytes-equal | 0/26/26/1/0 |
| d06-nft | transfer | 10 | 0.073 | 0.058 | 1.25 | bytes-equal | 0/26/26/1/0 |
| d06-nft | transferFrom | 10 | 0.064 | 0.062 | 1.04 | bytes-equal | 0/26/26/1/0 |
| j02-schnorr | verifySchnorrN3 | 11 | 0.221 | 0.203 | 1.09 | verified | 0/28/28/1/0 |
| j02-schnorr | verifySchnorrN3 | 11 | 0.218 | 0.202 | 1.08 | verified | 0/28/28/1/0 |
| d01-example-bboard | post | 13 | 0.443 | 0.336 | 1.32 | verified | 0/32/32/1/0 |
| d01-example-bboard | takeDown | 13 | 0.433 | 0.355 | 1.22 | verified | 0/32/32/1/0 |
| d01-example-bboard | post | 13 | 0.437 | 0.343 | 1.27 | verified | 0/32/32/1/0 |
| d01-example-bboard | takeDown | 13 | 0.421 | 0.346 | 1.22 | verified | 0/32/32/1/0 |
| d02-battleship | player1Shoot | 13 | 0.377 | 0.297 | 1.27 | verified | 0/32/32/1/0 |
| d02-battleship | checkBoard2 | 13 | 0.468 | 0.391 | 1.20 | verified | 0/32/32/1/0 |
| d02-battleship | player2Shoot | 13 | 0.380 | 0.291 | 1.31 | verified | 0/32/32/1/0 |
| d02-battleship | checkBoard1 | 13 | 0.467 | 0.386 | 1.21 | verified | 0/32/32/1/0 |
| d02-battleship | player1Shoot | 13 | 0.388 | 0.289 | 1.34 | verified | 0/32/32/1/0 |
| d02-battleship | checkBoard2 | 13 | 0.475 | 0.386 | 1.23 | verified | 0/32/32/1/0 |
| d02-battleship | player2Shoot | 13 | 0.396 | 0.277 | 1.43 | verified | 0/32/32/1/0 |
| d02-battleship | checkBoard1 | 13 | 0.489 | 0.383 | 1.28 | verified | 0/32/32/1/0 |
| d02-battleship | player1Shoot | 13 | 0.388 | 0.296 | 1.31 | verified | 0/32/32/1/0 |
| d02-battleship | checkBoard2 | 13 | 0.481 | 0.394 | 1.22 | verified | 0/32/32/1/0 |
| d03-micro-dao | dao_voting_token | 13 | 0.370 | 0.290 | 1.27 | verified | 0/32/32/1/0 |
| d03-micro-dao | advance | 13 | 0.400 | 0.309 | 1.29 | verified | 0/32/32/1/0 |
| d03-micro-dao | advance | 13 | 0.414 | 0.314 | 1.32 | verified | 0/32/32/1/0 |
| d03-micro-dao | advance | 13 | 0.400 | 0.308 | 1.30 | verified | 0/32/32/1/0 |
| d03-micro-dao | advance | 13 | 0.417 | 0.318 | 1.31 | verified | 0/32/32/1/0 |
| d03-micro-dao | advance | 13 | 0.403 | 0.306 | 1.32 | verified | 0/32/32/1/0 |
| d06-nft | mintAdmin | 13 | 0.378 | 0.299 | 1.27 | verified | 0/32/32/1/0 |
| d06-nft | mintAdmin | 13 | 0.381 | 0.307 | 1.24 | verified | 0/32/32/1/0 |
| d06-nft | mintAdmin | 13 | 0.392 | 0.293 | 1.34 | verified | 0/32/32/1/0 |
| d06-nft | burnAdmin | 13 | 0.379 | 0.290 | 1.31 | verified | 0/32/32/1/0 |
| d06-nft | rotateAdmin | 13 | 0.369 | 0.295 | 1.25 | verified | 0/32/32/1/0 |
| h03-election-ctor | add_voter | 13 | 0.401 | 0.320 | 1.25 | verified | 0/32/32/1/0 |
| h03-election-ctor | add_voter | 13 | 0.416 | 0.323 | 1.29 | verified | 0/32/32/1/0 |
| h03-election-ctor | add_voter | 13 | 0.413 | 0.321 | 1.29 | verified | 0/32/32/1/0 |
| h03-election-ctor | advance | 13 | 0.392 | 0.299 | 1.31 | verified | 0/32/32/1/0 |
| h03-election-ctor | advance | 13 | 0.387 | 0.281 | 1.38 | verified | 0/32/32/1/0 |
| h03-election-ctor | advance | 13 | 0.390 | 0.297 | 1.31 | verified | 0/32/32/1/0 |
| h03-election-ctor | set_topic | 13 | 0.369 | 0.297 | 1.24 | verified | 0/32/32/1/0 |
| t01-tiny | clear | 13 | 0.382 | 0.295 | 1.29 | verified | 0/32/32/1/0 |
| t01-tiny | set | 13 | 0.373 | 0.290 | 1.29 | verified | 0/32/32/1/0 |
| t04-welcome | add_organizer | 13 | 0.388 | 0.282 | 1.37 | verified | 0/32/32/1/0 |
| t04-welcome | add_participant | 13 | 0.392 | 0.287 | 1.37 | verified | 0/32/32/1/0 |
| t04-welcome | add_participant | 13 | 0.372 | 0.282 | 1.32 | verified | 0/32/32/1/0 |
| w02-bboard-testcenter | post | 13 | 0.425 | 0.342 | 1.24 | verified | 0/32/32/1/0 |
| w02-bboard-testcenter | take_down | 13 | 0.437 | 0.335 | 1.31 | verified | 0/32/32/1/0 |
| w02-bboard-testcenter | post | 13 | 0.439 | 0.339 | 1.29 | verified | 0/32/32/1/0 |
| w02-bboard-testcenter | take_down | 13 | 0.436 | 0.345 | 1.26 | verified | 0/32/32/1/0 |
| z01-zerocash | zerocash_mint | 13 | 0.440 | 0.349 | 1.26 | verified | 0/32/32/1/0 |
| z01-zerocash | zerocash_mint | 13 | 0.433 | 0.337 | 1.29 | verified | 0/32/32/1/0 |
| z02-unshielded-tokens | mintUnshieldedToContractTest | 13 | 0.390 | 0.291 | 1.34 | verified | 0/32/32/1/0 |
| z02-unshielded-tokens | mintUnshieldedToSelfTest | 13 | 0.377 | 0.303 | 1.24 | verified | 0/32/32/1/0 |
| z02-unshielded-tokens | mintUnshieldedToUserTest | 13 | 0.381 | 0.289 | 1.32 | verified | 0/32/32/1/0 |
| z02-unshielded-tokens | receiveShieldedTest | 13 | 0.409 | 0.322 | 1.27 | verified | 0/32/32/1/0 |
| d02-battleship | acceptGame | 14 | 0.812 | 0.481 | 1.69 | verified | 37/64/32/1/0 |
| d03-micro-dao | vote_reveal | 14 | 0.776 | 0.469 | 1.65 | verified | 37/64/32/1/0 |
| d03-micro-dao | vote_reveal | 14 | 0.801 | 0.472 | 1.70 | verified | 37/64/32/1/0 |
| d03-micro-dao | vote_reveal | 14 | 0.772 | 0.464 | 1.67 | verified | 37/64/32/1/0 |
| d04-coracle | guess | 14 | 0.758 | 0.472 | 1.61 | verified | 37/64/32/1/0 |
| d04-coracle | guess | 14 | 0.760 | 0.479 | 1.59 | verified | 37/64/32/1/0 |
| h03-election-ctor | vote$commit | 14 | 0.773 | 0.475 | 1.63 | verified | 37/64/32/1/0 |
| h03-election-ctor | vote$commit | 14 | 0.750 | 0.477 | 1.57 | verified | 37/64/32/1/0 |
| h03-election-ctor | vote$commit | 14 | 0.759 | 0.471 | 1.61 | verified | 37/64/32/1/0 |
| h03-election-ctor | vote$reveal | 14 | 0.730 | 0.460 | 1.59 | verified | 37/64/32/1/0 |
| h03-election-ctor | vote$reveal | 14 | 0.728 | 0.468 | 1.56 | verified | 37/64/32/1/0 |
| h03-election-ctor | vote$reveal | 14 | 0.698 | 0.462 | 1.51 | verified | 37/64/32/1/0 |
| z02-unshielded-tokens | mintShieldedToContractTest | 14 | 0.699 | 0.473 | 1.48 | verified | 37/64/32/1/0 |
| z02-unshielded-tokens | mintShieldedToSelfTest | 14 | 0.743 | 0.469 | 1.58 | verified | 37/64/32/1/0 |
| z02-unshielded-tokens | mintShieldedToUserTest | 14 | 0.731 | 0.468 | 1.56 | verified | 37/64/32/1/0 |
| z04-set-qualified-coin | test_ShieldedCoinInfo | 14 | 0.720 | 0.463 | 1.56 | verified | 37/64/32/1/0 |
| d03-micro-dao | cash_out | 15 | 1.359 | 0.659 | 2.06 | verified | 38/64/32/1/0 |
| z01-zerocash | spend | 15 | 1.325 | 0.672 | 1.97 | verified | 38/64/32/1/0 |
| z01-zerocash | spend | 15 | 1.309 | 0.687 | 1.91 | verified | 38/64/32/1/0 |
| z02-unshielded-tokens | sendImmediateShieldedToContractTest | 15 | 1.406 | 0.675 | 2.08 | verified | 38/64/32/1/0 |
| z02-unshielded-tokens | sendImmediateShieldedToSelfTest | 15 | 1.397 | 0.675 | 2.07 | verified | 38/64/32/1/0 |
| z02-unshielded-tokens | sendImmediateShieldedToUserTest | 15 | 1.396 | 0.659 | 2.12 | verified | 38/64/32/1/0 |
| z02-unshielded-tokens | sendShieldedToContractTest | 15 | 1.429 | 0.662 | 2.16 | verified | 38/64/32/1/0 |
| z02-unshielded-tokens | sendShieldedToSelfTest | 15 | 1.425 | 0.673 | 2.12 | verified | 38/64/32/1/0 |
| d03-micro-dao | buy_in | 16 | 2.569 | 1.128 | 2.28 | verified | 38/64/32/1/0 |
| d03-micro-dao | set_topic | 16 | 2.540 | 1.104 | 2.30 | verified | 38/64/32/1/0 |
| d03-micro-dao | buy_in | 16 | 2.595 | 1.113 | 2.33 | verified | 38/64/32/1/0 |
| d03-micro-dao | buy_in | 16 | 2.565 | 1.112 | 2.31 | verified | 38/64/32/1/0 |
| d03-micro-dao | vote_commit | 16 | 2.548 | 1.089 | 2.34 | verified | 38/64/32/1/0 |
| d03-micro-dao | vote_commit | 16 | 2.530 | 1.089 | 2.32 | verified | 38/64/32/1/0 |
| d03-micro-dao | vote_commit | 16 | 2.550 | 1.103 | 2.31 | verified | 38/64/32/1/0 |
| d03-micro-dao | set_topic | 16 | 2.502 | 1.062 | 2.36 | verified | 38/64/32/1/0 |
| d04-coracle | start | 16 | 2.612 | 1.099 | 2.38 | verified | 38/64/32/1/0 |
| d04-coracle | start | 16 | 2.666 | 1.115 | 2.39 | verified | 38/64/32/1/0 |
| d04-coracle | concede | 16 | 2.585 | 1.081 | 2.39 | verified | 38/64/32/1/0 |
| d04-coracle | withdraw | 17 | 4.726 | 1.880 | 2.51 | verified | 38/64/32/1/0 |

### 1.4 RTX 5090 Laptop GPU

Machine: AMD Ryzen AI Max+ 395 (12 threads), WSL2, CUDA device code for
sm_120. Same builds, suite and check rule as the RTX 5080 Laptop GPU run. The
stock binary checked all 888 GPU proofs of the 148 jobs with 0 failures; no
hook fell back to the CPU.

Of the 133 published proofs, 26 ran while other processes used more than 2
cores (3 in the CPU run, 23 in the GPU run). They pass the check but are kept
out of the totals and the table below; each is listed as an `# excluded:` line
in [`compare-rtx-5090-laptop.tsv`](../../gpu-prover/bench/compact/results/compare-rtx-5090-laptop.tsv),
which also holds the per-call rows. The only k = 17 proof is among them.

| Quantity | CPU | GPU |
|---|---:|---:|
| Proofs in the totals | 107 | 107 |
| Sum of per-proof medians | 101.12 s | 75.25 s |
| Median of per-proof medians | 0.818 s | 0.723 s |
| p95 of per-proof medians | 3.524 s | 1.815 s |
| Speed-up of the sums | | 1.34 |
| Checks | | 35 `bytes-equal`, 72 `verified` |

| k | Proofs | CPU s (median) | GPU s (median) | Speed-up (sum) | Checks (bytes-equal / verified) |
|---:|---:|---:|---:|---:|---|
| 6 | 7 | 0.345 | 0.306 | 1.13 | 7 / 0 |
| 7 | 15 | 0.349 | 0.311 | 1.13 | 9 / 6 |
| 8 | 12 | 0.356 | 0.311 | 1.14 | 9 / 3 |
| 9 | 7 | 0.361 | 0.330 | 1.10 | 7 / 0 |
| 10 | 3 | 0.378 | 0.338 | 1.11 | 3 / 0 |
| 11 | 2 | 0.526 | 0.501 | 1.05 | 0 / 2 |
| 13 | 37 | 0.828 | 0.755 | 1.11 | 0 / 37 |
| 14 | 8 | 1.212 | 1.005 | 1.19 | 0 / 8 |
| 15 | 8 | 1.976 | 1.236 | 1.60 | 0 / 8 |
| 16 | 8 | 3.536 | 1.831 | 1.92 | 0 / 8 |

On this machine every prover call costs about 0.3 s more than on the RTX 5080
Laptop machine, at every k and in both builds (k = 6: 0.345 s against
0.024 s). Verification and key loading do not show it, and its cause is not
established. Because both builds pay it, it pulls the small-k speed-ups toward
1; compare GPU models at k >= 15, where it is a small part of the time.

## 2. Large circuit (pre-port, midnight-proofs 0.8.3)

**Setup.** One circuit with k = 21, measured with the hooks of this design on
midnight-proofs 0.8.3 before the port to 0.9.0-rc.1. One proof makes 23 MSMs
of 2^21 terms, 35 NTTs, 17 coset transforms and one quotient.

Each timed set is
one cold proof, then 5 warm proofs (n = 5). Each set started only after the
1-minute load of the machine was below 2 (the quiet gate). Every proof had 0
fallbacks. All values are MEASURED. The source files are
[`gpu-k21.tsv`](../../gpu-prover/bench/large-circuit/gpu-k21.tsv) and
[`cpu-gpu-k21-rtx-5080-laptop.tsv`](../../gpu-prover/bench/large-circuit/cpu-gpu-k21-rtx-5080-laptop.tsv).

### 2.1 Warm prove by GPU model

| GPU model | Platform | Bus | Warm median (min to max), n = 5 | Cold | CPU-only build, n = 1 | Device peak | Host high-water mark |
|---|---|---|---|---:|---:|---:|---:|
| RTX 5080 Laptop GPU, 16 GB | Linux | not recorded | 9.35 s (9.29 to 9.47) | 10.47 s | 43.17 s | 12.85 GiB | 18.34 GiB |
| RTX 5090 Laptop GPU, 24 GB | Linux | PCIe 5.0 x16 | 11.00 s (10.96 to 11.12) | 11.66 s | 72.04 s | 12.87 GiB | 18.33 GiB |
| RTX 5090, 32 GB | WSL2 | PCIe 5.0 x16 | 13.78 s (13.56 to 13.90) | 15.36 s | 52.72 s | 12.92 GiB | 18.15 GiB |
| RTX 5090 Laptop GPU, 24 GB | WSL2 | PCIe 4.0 x4 | 18.64 s (18.41 to 18.74) | 22.53 s | 79.40 s | 12.87 GiB | 18.15 GiB |

The four machines have different CPUs, power limits and buses, so this table
does not rank the GPU models. The CPU-only column is one proof by a build
without the CUDA toolkit on the same machine. The last row has a PCIe 4.0 x4
link, a quarter of the width of the others, and the slowest phases of the
four. The per-phase times are in the source file.

### 2.2 CPU and GPU on one machine: RTX 5080 Laptop GPU

Earlier runs on the same machine and circuit ran the CPU path and the GPU path
of one build. Each row pools 5 warm proofs from three runs. A warm proof is one made after another proof in the same
process. No quiet-gate record exists for these runs.

| Path | Warm median (min to max) | Phase 1, advice | Phase 2, trace | Phase 3, quotient | Phase 4, evaluation and opening | MSM total |
|---|---|---:|---:|---:|---:|---:|
| CPU | 51.33 s (51.31 to 52.13) | 8.53 s | 10.99 s | 20.50 s | 10.86 s | not timed |
| GPU | 13.44 s (13.14 to 14.53) | 4.94 s | 3.28 s | 0.37 s | 4.59 s | 1.67 s |

The speed-up is 3.8 for the whole proof and 55 for the quotient phase. The
later set of section 2.1 reads 9.35 s on the same GPU. Its phases take 3.26 s,
2.94 s, 0.37 s and 2.71 s. Its 23 MSMs take 1.44 s, about 63 ms for one MSM of
2^21 terms.

### 2.3 Device memory

The device peak is about 12.9 GiB on every GPU model. At k = 21 one proof holds
30 resident proving-key cosets (7.5 GiB) and 17 per-proof cosets on the
extended domain. A device with 16 GB therefore runs the whole proof on the
device. A smaller device takes the `evict` or `cpu` step of the admission
ladder.

## 3. Preview transactions

Two Compact programs were deployed and called on the Preview network on
2026-11-18 (UTC). The proofs came from the proof server 9.0.1 wrapper
(`gpu-prover/bench/compact/proof-server`) on an RTX 5080 Laptop GPU. They were
proved by the 0.8.3 hooks; the PR carries the same design on 0.9.0-rc.1. The
CPU baseline column gives the transaction of the same call proved by the stock
CPU proof server on Preview.

3 calls with GPU proofs in 5 transactions. By label: 0 GPU-proven
(msm > 0), 3 GPU below k=14, 2 CPU (deploys).

| Program | Call | k | Contract address | Transaction hash | Block | Verdict | Proof | CPU baseline transaction hash |
|---|---|---|---|---|---|---|---|---|
| a01-adt-counter | deploy | - | `90737ecb65f31b874e55c9acd841bae37fb19e24fa28f0cffed9f49953e1aab5` | `dbfb6d38ac7baa88646d6de15dabaef0e127df80bf700b267d9c9e50b82c07d2` | 166601 | SucceedEntirely | CPU (0.7.3 dust path) | `5ab1dceedf9cdbcafe15f5d00e97ee96124d716d0bf7f06826cf59915a54ca29` |
| a01-adt-counter | test_all | 8 | `90737ecb65f31b874e55c9acd841bae37fb19e24fa28f0cffed9f49953e1aab5` | `fe43448ff8e48a5ecee228c194e81c81289f64e9e08931450b3dc6ac5497edd8` | 166604 | SucceedEntirely | GPU (NTT/coset/quotient on device; MSM on CPU below k=14) | `966fec080f2fd69dcbb2f86ae51db9f6030fc3b43617de746947eecd2a10a8cb` |
| d01-example-bboard | deploy | - | `c9df0a045ea795764bb7a6ec2854691eda3408be030de669fc52e5bc03e3a8e7` | `4bdb49baafaf2e394effa7cdb86451b5ba6149a08f4dff9377be5490d61ba72c` | 166640 | SucceedEntirely | CPU (0.7.3 dust path) | `66d122bccd04b00ab9070fa3a366f064bf647bb21d68b7ace24a3f6453602bea` |
| d01-example-bboard | 01-alice-post | 13 | `c9df0a045ea795764bb7a6ec2854691eda3408be030de669fc52e5bc03e3a8e7` | `53210d3b35382dbbc1a804bc1981bae9c0d99b4d53a41657f679f8ef38a45792` | 166644 | SucceedEntirely | GPU (NTT/coset/quotient on device; MSM on CPU below k=14) | `8d24f5c1be933788570133e6a3760d9515d370d8eb6b14d250428fe2b152ba06` |
| d01-example-bboard | 04-alice-takedown | 13 | `c9df0a045ea795764bb7a6ec2854691eda3408be030de669fc52e5bc03e3a8e7` | `306ccce8e41cef214c05b57c8028fda0e8358df58e054ca473a50c6269aafcec` | 166648 | SucceedEntirely | GPU (NTT/coset/quotient on device; MSM on CPU below k=14) | `faa888bb2c605b19aaf920108444d16fdcbbca44ccb8e7f571d347ed65b7507c` |

Counter line of each contract-call proof (device calls of the hooks; the
server prints a line every 200 ms while the counts change):

| Call | Counter lines in the call's `/prove` request | Total |
|---|---|---|
| a01 test_all | `msm 0 ntt 26 coset 26 quotient 1 fallbacks 0` | msm 0, ntt 26, coset 26, quotient 1, fallbacks 0 |
| d01 01-alice-post | `msm 0 ntt 3 coset 3 quotient 0 fallbacks 0`, `msm 0 ntt 43 coset 43 quotient 0 fallbacks 0`, `msm 0 ntt 32 coset 32 quotient 1 fallbacks 0` | msm 0, ntt 78, coset 78, quotient 1, fallbacks 0 |
| d01 04-alice-takedown | the same three lines | msm 0, ntt 78, coset 78, quotient 1, fallbacks 0 |

- Below k=14 the device runs the transforms and the quotient but not the MSM:
  the MSM hook takes only MSMs of 2^14 terms or more.
- The counters come from the 0.8.3 hook set in the wrapper, which still has a
  coset hook. The PR's 0.9.0-rc.1 hooks fold the coset step into the device
  quotient.
- The last d01 line (ntt 32, coset 32, quotient 1) is the count that the
  Compact bench records for these calls. The two lines before it come from the
  same request before that step and also ran on the device.
- Each GPU row shows the hooks-installed line naming the RTX 5080 Laptop GPU
  (sm_120) at the start of its session.
- Why the deploys and the dust spends stay on the CPU: in proof-server 9.0.1
  the zswap and dust keys come from `midnight-transient-crypto` 2.2.0 on
  midnight-proofs 0.7.3, which the hooks do not cover. A deploy carries only a
  dust-spend proof. Each call transaction carries a contract-call proof on the
  GPU and a dust-spend proof on the CPU. Each deploy and each dust spend made
  one `/prove` request with no counter line.
- The ledger verified every proof with the stock verifier when it included the
  transaction. The public transcript of each call matches the scenario's reference
  transcript.
- No other device job ran on the GPU machine while these rows ran, so no row
  is contended.
- Wallet lock held (UTC): a01 deploy 15:24:04-15:24:20, test_all
  15:24:21-15:24:39; d01 deploy 15:27:56-15:28:13, 01-alice-post
  15:28:17-15:28:37, 04-alice-takedown 15:28:40-15:29:01.
- An earlier d01 attempt failed with a Preview infrastructure fault. Between
  15:03:51Z and 15:08:51Z, wallet balancing of the deploy failed with
  `Wallet.Other: Encountered unexpected error <- ServerError: An unknown error
  occurred` from the Preview indexer, and the wallet logged `Failed to record
  dust tx-history section`. No proof request reached the GPU server and nothing
  was submitted (0 transactions). The retry above ran after a fresh wallet sync.

Data: [`results/preview-rtx-5080-laptop.tsv`](../../gpu-prover/bench/compact/results/preview-rtx-5080-laptop.tsv)
(one row per transaction) and
[`results/preview-rtx-5080-laptop.hooks.txt`](../../gpu-prover/bench/compact/results/preview-rtx-5080-laptop.hooks.txt)
(the server's hook and request lines; no witness data).

## 4. midnight-proofs 0.9.0-rc.1 numbers

These numbers come from the code of this pull request on midnight-proofs
0.9.0-rc.1. The Compact suite cannot run on 0.9.0-rc.1, because the Compact
toolchain and the proof server pin earlier midnight-proofs releases. The
rc.1 measurement therefore uses a public k = 21 circuit built into the
benchmark, described in
[`gpu-prover/bench/rc1/README.md`](../../gpu-prover/bench/rc1/README.md).
That circuit differs from the private k = 21 circuit of section 2, so the two
sets of times are not comparable with each other.

Each mode ran three processes, each with one cold and one warm proof, with 8
Rayon threads and a one-minute load below 2 at the start of each proof. Every
proof was checked by the stock CPU verifier. Times are medians of three, in
seconds, with the range in brackets.

| GPU | CPU cold | CPU warm | GPU cold | GPU warm | Warm speed-up |
|---|---|---|---|---|---|
| RTX 5090 Laptop GPU (sm_120) | 23.25 (23.23 to 23.28) | 23.38 (23.28 to 23.43) | 3.99 (3.91 to 4.05) | 3.75 (3.75 to 3.75) | 6.2x |
| RTX 5080 Laptop GPU (sm_120) | 14.28 (14.25 to 14.31) | 14.21 (14.20 to 14.24) | 4.86 (4.84 to 4.87) | 4.63 (4.59 to 4.73) | 3.1x |

The CPU times differ between the two rows because the host CPUs differ; each
row compares CPU and GPU on the same machine.

Device work per proof, the same on both GPUs: 11 MSM calls, 7 NTT calls
(forward and inverse) and 1 quotient call, with 0 device errors and 0
fallbacks. A warm proof copies 4.29 GB to the device and 0.60 GB back, plus
1.08 GB of MSM bucket read-backs, which are zeroed after use. Peak tracked
device memory is 1.97 GB.

Data: [`gpu-prover/bench/rc1/results/`](../../gpu-prover/bench/rc1/results/)
(raw rows, summaries, load samples and the device record of each machine).

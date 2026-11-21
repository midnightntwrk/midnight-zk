# Results

Toolchains: Lean 4 v4.35.0 (no Mathlib), Quint 0.32.0, Python 3. Rerun with
the commands of `README.md`.

## Requirements

85 EARS requirements, GPU-001 to GPU-085. Strict EARS lint: 0 defects,
0 warnings. Every requirement names its verification in `requirements.md`:
an oracle declaration, a Quint invariant or test, the golden vectors, or a
Rust, harness, container or review check for the parts that the models do not
state (build, kernels on a real device, sockets, files, records).
`COVERAGE.md`, written by the conformance lane, maps each requirement to its
executable checks. `scripts/check_refs.py` checks that every oracle, Quint and
vector name in the verification column exists.

## Audit of 2026-11-17 and what changed

An independent audit and a mutation run of the first oracle found that it
could agree with the Quint model and with every golden file while the code
did something else. The confirmed findings and their fixes:

| Finding | Fix |
|---|---|
| Two invariants read counters that no transition wrote (`badReadbacks`, `unverifiedReturned`). | The read-back transition and the served branch now write them; a machine without the refusal or without the verifier check breaks the invariant proof (mutants 05, 07, 30, 31). `served <= verifyAccepts` is a second, independent statement of GPU-039. |
| FFT = DFT was proved only for length 4 over F_5; the device MSM had `#guard`s only. | General theorems (below). The F_5 statement stays as a pin. |
| GPU-038 was a label on a service op. | `DataMove`: the rule is a theorem over every plan of copies; the old port's plan violates it. |
| Acceptance mode served a degraded proof. | GPU-078, in both models. |
| The client breaker, the decline reasons and the per-request MSM-context release were not modelled. | GPU-073 to GPU-077, GPU-081, GPU-082, in both models. |
| Every decline was a fallback, so a proof with one MSM below the threshold was degraded (second audit). | GPU-012 reworded, GPU-085: expected declines are counted and are not fallbacks. |
| The bucket-sum rule accepted a free in place of a zero; a finite window stood in for a container lifetime (second audit). | Erasure is observable in `DataMove`; a window of 0 means no window. |
| A verifier accept was credited on paths where the daemon never runs the verifier; two wrong quotient references survived every gate; zeroing bucket sums before reducing them met the rule (third audit). | The accept is counted in the served branch (`verify_counted_only_when_served`); hand pins and two vector cases; a host operation cannot consume a zeroed buffer; `Rule038` joins executability and the copy rule. |
| The vector gate exited 0 on a stale file. | Each check is its own command; `check_vectors.test.sh` is the negative test. |
| No golden case for one element, the empty input, infinity bases, the threshold or a non-power-of-two length; no expected decision. | Vectors v2. |
| The shift-7 coset cases asked the kernel for a shift it does not take. | The kernel contract is a cube root of unity (GPU-010); the shift-7 cases expect a decline. |

Rulings on the read-back set (base-domain transform outputs and the vendored
MSM's bucket sums are permitted; no extended-domain vector), the restart cap
under systemd and in a container, the fuzz counts and the harness scope are
in the requirement sentences. Two audit findings are not fixed in the models,
with these reasons: socket-level timing (which bytes are read before a busy
answer) is below the state machine and is a Rust test; the free-memory
reading after an eviction is the supplied reading `b`, which under the
default policy is the observation itself.

## Lean oracle

`lake build --wfail` passes: 536 theorems in 19 modules, no `sorry`. Every
table theorem has its `#print axioms` pinned with `#guard_msgs` (`Audit.lean`,
`AuditNtt.lean`, `MsmProofs.lean`, `PinsExt.lean`, `VectorPins.lean`): each
uses a subset of `propext`, `Classical.choice` and `Quot.sound`. No
`native_decide`, no `implemented_by`, `extern`, `partial`, `unsafe`, `opaque`
or `axiom` declaration (`#audit_ns GpuSpec` = `[]`, rerun with every module
imported).

General theorems. `p` is any modulus above 0 unless a bound is named. No
theorem assumes that `p` is prime. The transform and bucket theorems take any
input; the signed-digit theorems need scalars below `p`, as the kernel does
(an unreduced input is a decline).

| Theorem | Statement | Requirements |
|---|---|---|
| `fft_eq_ntt` | the radix-2 FFT equals the DFT for every size `2^m` and every root `w` with `w^(2^(m-1)) = -1` | GPU-007 |
| `intt_ntt`, `ntt_intt` | the inverse transform inverts the transform, in both orders, when `w` and `2^m` have inverses | GPU-007 |
| `ifft_eq_intt` | the device inverse equals the reference inverse | GPU-007 |
| `cosetExt_eq_ntt_scaled` | the coset transform is the NTT of the scaled, zero-padded polynomial | GPU-007 |
| `fftCosetExt_eq`, `fftCosetToCoeff_eq`, `cosetToCoeff_cosetExt` | the device coset transforms equal the reference; the round trip returns the coefficients | GPU-007 |
| `bls_size_ok`, `*_bls` | every hypothesis holds at BLS12-381 Fr for the sizes `2^1` to `2^32` and both coset shifts (kernel-checked tables), so each theorem above applies to the vectors | GPU-007 |
| `msmBucket_eq_msm_trunc`, `msmBucket_eq_msm` | the bucket method equals the plain sum for every window width; with no hypothesis at all it equals the sum of the truncated scalars | GPU-007 |
| `msmBooth_eq_msm`, `msmBoothBy_eq_msm` | the signed-digit method of the vendored MSM (fold above `r/2`, Booth digits, `2^(c-1)` buckets per window, the kernel's window count) equals the plain sum for every width `c >= 1` | GPU-007 |
| `msmBoothBy_blsR_topLimb` | the same with the kernel's own fold test (top limb) at BLS12-381 Fr, widths 10 to 18 | GPU-007 |
| `msmBatch_eq`, `msmBucketBatch_eq` | a batch of MSMs over one base table in a single pass equals the separate MSMs | GPU-080 |
| `msm_zero_scalar`, `msm_infinity_base`, `msm_append` | a zero scalar or an identity base changes no result; an MSM splits at any point | GPU-007 |
| `msmMasked_eq` | `MSM(s + r) - MSM(r) = MSM(s)` | GPU-013 |
| `compile_correct`, `deviceNumerator_eq` | the compiled program computes the expression tree at every point | GPU-007, GPU-071 |
| `numeratorTiled_eq`, `deviceNumeratorTiled_eq` | the numerator evaluated in tiles of any size above 0 equals the untiled one (`quotientCoeffs_tiled` is the corollary for anything computed from it) | GPU-079 |
| `gpu038_iff`, `gpu038_append` | a plan of copies meets GPU-038 exactly when each download it executes has a permitted kind | GPU-038 |
| `kind_determined`, `extended_only_from`, `mislabel_impossible` | the kind of a buffer follows from the operation that made it and its inputs; only the coset, numerator and extended-inverse operations make an extended-domain vector; no executable plan can download such a vector and meet the rule | GPU-038 |
| `specPlan_gpu038`, `oldPortPlan_violates`, `oldPort_stripped_not_executable` | the fixed port's plan meets the rule; the old port's plan is executable and violates it with three extended-domain copies and one zeroed-region copy; without those copies it cannot run | GPU-038, GPU-036 |
| `msmBucketPlan_gpu084`, `msmBucketPlanFreeOnly_violates`, `msmBucketPlanNoZero_violates`, `gpu084_unzeroed_free_violates` | the vendored MSM's host bucket sums are zeroed before their memory is released: a plan that frees them without zeroing, or leaves them, violates the rule | GPU-084 |
| `declines_all_counted`, `count_one_reason`, `fallbacks_by_reason` | every decline is counted once, under one class and one reason; the fallbacks are exactly the declines with a fallback reason, and the expected declines (no device, below the threshold) are the rest | GPU-073, GPU-012, GPU-085 |
| `gate_none_iff`, `gate_shape`, `gate_below_min_k`, `gateMsm2_mismatch`, `gate_declines_before_write` | the entry gate: when the kernel runs, the shape and below-min-k declines, and a gated decline leaves the buffer unchanged | GPU-010, GPU-074 |
| `draws_independent_of_device` | with two random sources (the caller's and the OS source), the draws from each and both remaining streams are the same for any two devices, honest or not: no hook answer can add, skip or move a draw | GPU-014, GPU-016 |
| `prove_any_schedule`, `prove_any_reasons`, `runInPlace_eq`, `resolve_eq` | consequences of the hook contract: a device that returns the reference value or declines gives the CPU proof, whatever it declines and why, also when it answers one call and declines the same call later (the device answer may depend on the position). The contract itself is checked on the real hooks by the Rust vector and fault tests. | GPU-008, GPU-009, GPU-014 to GPU-016 |
| `inv_init`, `inv_step`, `inv_run` | every reachable state of the service machine satisfies `Inv` | below |
| `breaker_opens_at_limit`, `arrive_failure_classes`, `breaker_open_skips`, `served_clears_failures`, `served_then_restart`, `busy_no_failure` | the client breaker: exactly when a recorded failure opens it, which arrivals record one, the skip while open, the reset | GPU-075 to GPU-077 |
| `verify_counted_only_when_served`, `acceptance_no_degraded_proof`, `acceptance_degraded_refused`, `decline_counted`, `expected_decline_no_fallback`, `wipe_frees_tables`, `wipe_fail_retires`, `restart_cap`, `lifetime_cap` | acceptance mode, decline counts and fallbacks, MSM contexts, retirement, the restart cap with a window and for a lifetime | GPU-078, GPU-073, GPU-085, GPU-082, GPU-035, GPU-048, GPU-083 |

Each logically needed bound in a theorem has a counterexample without it,
kept as a guard or a theorem (the width range 10 to 18 of the BLS corollaries
describes the vendored kernel and is not needed) (`p0_counterexample`, the `#guard`s at the end of `MsmProofs.lean`,
`gate_below_min_k_needs_config`, `pin_served_then_overbound`). Pins
(`decide +kernel` and `#guard`) written from the requirement sentences cover
the reference numerator (`rotIndex`, the Horner fold, by hand over F_17), each
admission step, the breaker boundaries, acceptance mode, each decline reason
and the read-back kinds. `VectorPins.lean` runs every device model on every
golden value case and pins the case counts and the expected decisions.

## Service invariants

The same invariants are stated in the oracle (`GpuSpec.Service.Inv`, proved)
and in the Quint model (`inv`, simulated). The model was written from the
requirements, `design.md` and `vectors/README.md` only, by an author who did
not open the oracle.

| Quint invariant | Oracle | Requirements |
|---|---|---|
| `inv_queue` | `invQueue` | GPU-045 |
| `inv_wipe` | `invWipe` | GPU-034 |
| `inv_admit` | `invAdmit` | GPU-029 |
| `inv_need` | `invNeed` | GPU-025 |
| `inv_evict_step` | `invEvictStep` | GPU-027 |
| `inv_evict_policy` | `invEvictPolicy` | GPU-030, GPU-081 |
| `inv_tables` | `invTables` | GPU-082 |
| `inv_lease` | `invLease` | GPU-037, GPU-057, GPU-061 |
| `inv_wsl_idle` | `invWslIdle` | GPU-060 |
| `inv_wsl_keep` | `invWslKeep` | GPU-059 (a configuration check: it cannot fail after a start) |
| `inv_ctx` | `invCtx` | GPU-020, GPU-031 |
| `inv_restart` | `invRestart` | GPU-048, GPU-049, GPU-083 |
| `inv_accounted` | `invAccounted` | GPU-021, GPU-022 |
| `inv_errors` | `invErrors` | GPU-021 |
| `inv_verified` | `invVerified`, `invVerifyPending` | GPU-039 |
| `inv_readback` | `invReadback` | GPU-038 |
| `inv_bench` | `invBench` | GPU-024 |
| `inv_down` | `invDown` | GPU-035 |
| `inv_breaker` | `invBreaker` | GPU-075 |
| `inv_skips` | `invSkips` | GPU-075 |
| `inv_declines` | `invDeclines` | GPU-073 |
| `inv_acceptance` | `invAcceptance` | GPU-078 |
| `inv_busy`, `inv_cpu_step`, `inv_stopped`, `inv_refused`, `inv_wipe_error`, `inv_degraded`, `inv_overbound`, `inv_reset`, `inv_failures`, `inv_fallback` | theorems and pins of the same requirements (`busy_no_failure`, `served_clears_failures`, `wipe_fail_retires`, `decline_counted`, ...) | GPU-046, GPU-028, GPU-022, GPU-040, GPU-035, GPU-023, GPU-050, GPU-076, GPU-077, GPU-012 |
| (none) | `invPhase`, `invFresh` | helper invariants for the induction |

## Quint simulation

`quint run --invariant inv`, 10,000 samples of 40 steps, seed 20261117, for
each of 20 instances: `[ok]`, no violation. The instances are the ten of the
first model (default, keep, bench, no device, WSL2, WSL2 with a tight budget,
restart limit 1, and three flow instances without crashes) and ten new ones:
acceptance mode (plain, keep, flow, WSL2), breaker limits 1 and 0, a short
breaker window and cooldown (5 s and 7 s with time steps of at most 3 s), a
cooldown of 0, and two containers (a restart window of 0: no window; limits 3
and 1). 49 witnesses show that the interesting states are reached; a witness count of 0
is by configuration in every case (for example no device step without a
device, no acceptance refusal outside acceptance mode, no breaker opening with
a cooldown of 0). Under frequent crashes the breaker is open in about 92 % of
the traces of the chaos instances, so the flow instances carry the coverage of
the reply path.

Directed tests (`quint test`): 108 runs in 17 modules, all passing; 78 are
replayed, 30 are refusal tests (a refused step is not a transition; they
include the guarded parameters: a read-back kind above 3, a decline reason
above 6).

The model's invariants were shown able to fail, except `inv_wsl_keep`, which
is a configuration check (the start refusal is pinned in the oracle): 28 one-line bugs
planted in a copy of the model each violate a named invariant or fail a named
directed test. Three are caught by tests only, because the invariant uses the
same predicate as the transition: the keep policy ignored at the wipe, the
fallback split moved by one reason, and the window-0 rule applied to every
window.

## ITF replay through the oracle

Every exported trace is replayed transition by transition through
`oracle --step`, comparing the whole state record.

| Source | Traces | Transitions agreed |
|---|---|---|
| 20 instances, 50 traces of 40 steps each | 1,000 | 40,000 |
| directed tests (14 modules) | 78 | 473 |

No disagreement, no excused transition (40,473 transitions). All 1,078
traces start at the oracle's start state. Negative
control: the traces of `svc_default` with `resident` changed by 1 give
`DISAGREE`, so the replay can fail. Every `[ok]` and every replay line above
is from one run of `scripts/quint_check.sh` on the committed model and oracle.
The gate also compares frame 0 of every trace with the oracle's start state
for that configuration (`scripts/check_initial_states.py`), because the replay
compares transitions only; a trace set with the clock moved by 1 fails it.

The oracle's `--step` refuses any state outside `Inv`, so the replay also
checks that each simulated state satisfies the oracle's invariant, including
the helper invariants that the model does not state.

Ambiguities that the two authors met and how the text now decides them
(`design.md` section 7): the fields of the acceptance short-cut; a degraded
error counts as an error and sets no failed-run mark; a crash of an idle
daemon records no failure; a failure during an open cooldown can extend it;
the breaker acts on arrivals only; every read-back counts in `readbacks` and
one of a kind above 3 also in `badReadbacks`; the preconditions of each
event; the counters survive a restart; an expected decline leaves an existing
degraded mark as it is. One requested property was false and
is stated as it holds: a served proof clears the failure record, and a
waiting caller that fails over at an over-bound exit then records one new
failure (`served_then_restart`, `inv_reset`).

## Mutants

`scripts/mutants.py` applies 67 one-line wrong changes to the oracle, one at a
time, in a scratch copy: the 19 of the first audit (of which 6 survived the
first oracle's build) and 48 for the new definitions (the breaker, acceptance
mode, the decline split, the written counters, the signed-digit and batch
MSM, tiles, the entry gate, the copy rule, the two random sources, the
lifetime cap, and the two wrong quotient references that the third audit
found alive, an instance read from column 0 always and the vanishing
exponent `N/n`, and the challenge lookup `k mod 2` of the final audit). A mutant is killed by the build (a theorem, a pin or a guard
fails), by the vector gate or by the replay of the Quint traces.

Result: 66 killed, all by the build; the unchanged control (mutant 00)
survives the build, the vector gate and the replay, so a kill is not an
accident of the environment. The runs were made as the oracle grew: mutants
00 to 62 on the oracle of f8aabf89, and mutants 07, 29 to 31 and 63 to 67
again on the later oracle with this script. One survivor, with its
equivalence argument:

- **47** (the `a.length <= 1` branch of `fftAux` returns the input unreduced).
  `fft` calls `fftAux` with `fuel = log2 (length)`. A list of length 0 or 1
  gets fuel 0 and is answered by the fuel-0 case, which reduces. In the
  recursion a list of length `n >= 2` with fuel `f + 1 = log2 n` passes
  halves of length at least 1 with fuel `f`; a half of length 1 arises only
  from `n <= 3`, where `f = 0`. So the branch is never reached from `fft`, and
  the mutant computes the same `fft`, `ifft` and coset transforms on every
  input. It differs only for a direct call of `fftAux` with more fuel than
  levels, which nothing makes.

The two counters that the first audit found inert are covered by mutants 05,
07, 30 and 31: dropping the read-back refusal or the verifier check breaks the
invariant proof (`stepRefusals_nil`, `b_reply`); dropping the counter writes
breaks pins and proofs (`pin_readback_kinds`, `b_reply`, `reply_served`).

## Fidelity gaps of the models

Three independent audits judged the oracle by one standard: could the code
differ from it while every gate here passes? Their theorem and coverage
findings are fixed (above). What remains is what the models leave out. Each
row names the check that covers it outside the models.

| Gap | Why the model stops there | Covered by |
|---|---|---|
| The quotient hook also evaluates permutation, lookup and trash terms, runs a register program per thread, and returns the first `(n-1) * degree` coefficients | The oracle grammar is the gate expression tree; `quotient_coeffs` is the full inverse transform | Rust: quotient fuzz against the stock quotient, 10,000 systems in the GPU gate (GPU-071); `quotient_coeffs` vectors against the hook where the harness can build the job |
| Admission after an eviction reads the free memory and the held resources again; the model adds the nominal resident size to reading `b` | Two readings per admission are the wire contract; under the default policy `b` is that observation | Rust: admission tests with a fake device, a post-eviction reading below the prediction; the adapter maps `b` (WIRE notes) |
| The phase mask, the safety margin, the per-table need and the wait deadline | Configuration and timing below the abstract units | Rust: `need.rs` and `admission.rs` tests; need at least the kernel's own gate |
| systemd counts starts, the first included; compose has no window | GPU-048 is an upper bound; the model counts restarts | `restart-cap.test.sh` on the real supervisors; GPU-083 for the container |
| Which bytes the daemon reads before a busy reply; a disconnect between two device phases | Socket and thread timing | Rust daemon tests (GPU-046, GPU-037) |
| Context creation at device detection; when key copies are really uploaded | `ctx` and `devUsed` are set at admission | Rust: no compute context during detection and key generation (GPU-031) |
| A CPU fallback that fails or is disabled; record fields (label, reason, request id); timing rows | `clientCpu` counts the fallback; records are not state | Rust client and record tests (GPU-021, GPU-023, GPU-053); harness (GPU-024) |
| Which copy site moved which bytes; which hook call declined with which class | Ops 3 and 4 carry the reason and the kind that the adapter reports | Rust: counted read-back over two proofs (extended copies 0), the decline map by class and reason (GPU-038, GPU-073) |
| The hook contract itself: an accepted value equals the stock value; a decline leaves the caller buffer unchanged; the real order of draws and transcript writes | The schedule theorems assume the contract | Rust: golden vectors through the CPU routine, the stub and the GPU hook; fault injection after upload and after launch; seeded proof identity; transcript and RNG log (GPU-007 to GPU-009, GPU-014 to GPU-017) |
| A wrong root, a `log_n` that does not match the length, the quotient job shape | The gate table has lengths, the threshold, the device and the reduced flag | Rust decline tests for root and shape (GPU-010) |
| The mask vector is public and fixed; G1 arithmetic; the table cache | The MSM runs over `Z_r`; `msmMasked_eq` holds for every mask | Rust: device MSM against `result * G` for every vector case; mask construction review (GPU-013) |
| A transform with a nonstandard divisor | Outside the stock hook contract | Rust device test with divisor 3 |
| Which regions the wipe zeroes and checks; a zeroed buffer uploaded and read back | `DataMove` tracks kinds and copies, not contents; the wipe is the `dirty` flag of the service machine | Rust: zero-check mode reads every wiped region as zero, with a deliberately dirty control (GPU-034, GPU-036) |
| A device lock configured on a native host; a key the device quotient does not take, or fewer phases taken than admitted, as a degraded reason | The lock rule is the WSL2 rule of GPU-057; the phase set is configuration | Rust daemon tests for the lease and for `begin_request` taking fewer phases |
| The client's breaker record when its state file cannot be opened, locked or written | The models keep an infallible record | Rust client test with an unusable state path (code finding sent: the breaker never opens then) |
| A verified proof whose output file cannot be written | `verifyAccepts` counts accepts of served proofs | Rust daemon test of a failed proof write |
| A coset transform on a base domain of one element; a counter read while proved on a host that never had a device | The gate checks the extended length; the counter read is not tied to device use | Rust decline test at `k = 0`; `NoDevice` returns a default report in host code |
| The thread schedule of the quotient kernel (`i = round * stride + tid`, scratch per thread); sppark's separate ones path, sorting and partial rows | Tiles are contiguous ranges; the signed-digit model fills mathematical bucket rows | Rust quotient fuzz with more rows than threads; device MSM against the vectors with more than one chunk |
| When the cold label clears (the models: at the first served proof; the daemon: by request number) | `cold` is a label of the record | Rust record test of a failed first request followed by a served one (ruled: the spec is right, the daemon changes) |

## Findings

1. **A wipe is not a device phase (Quint counterexample).** The first model
   kept `devWork` set in the `proved` phase, and released the WSL2 device lock
   there. `inv_lease` failed: device work without the lock. The wipe zeroes
   and frees buffers; it runs no kernel of the request. Resolution: the end of
   the proof clears `devWork`, and GPU-037, GPU-057 and GPU-061 now say "run no
   (further) device phase", with *device phase* defined in `requirements.md`
   to exclude zeroing and freeing.
2. **The reduced need must be part of the full need (proof finding).**
   `invNeed` (GPU-025) could not be proved for the evict step when the
   reduced need exceeds the per-proof need. The oracle now refuses such a
   configuration (`bad-config`). The Rust need computation must compute the
   reduced need as a part of the full per-proof need.
3. **Helper invariants (proof finding).** The induction needed facts that the
   requirements imply but no single requirement states: a request in phase
   `idle` or `accepted` has no fallback count, lease loss, degraded mark,
   over-bound mark, admission step or device work left from the previous
   request (`invFresh`); after a confirmed wipe nothing is dirty, and under
   the evict policy or WSL2 nothing is resident (`invPhase`); `invEvictPolicy`
   and `invWslIdle` hold in `accepted` as well as `idle`. Every simulated
   state satisfies them.

## Open items

1. **Crash before the wipe.** When the daemon process dies, the driver frees
   its device memory without zeroing it (design.md, section 12). No
   requirement can close this from inside the daemon. A host that shares the
   device between users needs a policy: for example a supervisor that zeroes a
   reserved region before restart, or accepting the risk.
2. **Zero-check and the read-back set.** GPU-036 checks zeroed regions on the
   device and reports a count. That count is a counter, so it is inside the
   permitted set of GPU-038. A zero-check that copied regions back would not
   be. The Rust code must keep the check on the device.
3. **Planned restarts and the restart limit.** GPU-050 restarts the daemon
   after an over-bound request. The model counts that restart toward the limit
   of GPU-048, so repeated over-bound requests can stop the daemon. The
   requirements do not say whether a planned restart counts.
4. **The wipe after a lost WSL2 lock.** Under finding 1 the wipe may run after
   the device lock is released, because it is not a device phase. If zeroing
   on a shared device must also hold the lock, GPU-057 needs a separate
   statement for the wipe.
5. **Scope of the models.** The oracle and the Quint model state the
   request state machine and the hook contract. Build behaviour, real kernels,
   sockets, file modes, records and the container are checked by the Rust,
   harness, container and review checks named in `requirements.md`. Quint ran
   bounded random simulation (`quint run`), not exhaustive model checking.

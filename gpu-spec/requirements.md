# GPU prover requirements

Generated from `requirements.json` by `scripts/gen_requirements_md.py`. The JSON is
authoritative. Each statement is one EARS sentence. The verification column names the
Lean oracle declaration, the Quint artifact, the golden vectors or the Rust, harness or
container check that covers it. `design.md` gives the context.

Terms: a *device phase* is an upload, MSM, NTT or quotient kernel of a
request. Zeroing and freeing buffers is not a device phase. *Configured* values have
documented defaults and come from an environment variable or a config file.
The *resident policy* is `evict` by default: the resident proving-key copies and the MSM
tables are freed before each reply and uploaded again at the next request. `keep` is an
opt-in for a card with no other user; it holds the key copies between requests. The MSM
device contexts are freed at the end of every request under either policy.


## Build and feature

| ID | Requirement | Verification |
|---|---|---|
| GPU-001 | Where the gpu feature of the midnight-proofs crate is disabled, the midnight-proofs crate shall compile the prover code of the release without the feature and produce byte-equal keys and proofs for equal inputs and equal random streams. | rust: feature-off build gives byte-equal keys and proofs to the release |
| GPU-002 | Where the gpu feature of the midnight-proofs crate is enabled and no hook is installed, the midnight-proofs crate shall produce keys and proofs byte-equal to the build without the feature for equal inputs and equal random streams. | rust: feature-on build without installed hooks gives byte-equal keys and proofs |
| GPU-003 | If the CUDA toolkit is absent at build time, then the midnight-gpu crate shall build without error a stub library whose every device operation declines. | ci: cargo build and clippy with --all-features on a runner without nvcc |
| GPU-004 | The midnight-gpu build script shall take the CUDA root from CUDA_PATH or CUDA_HOME and the device architectures from a configured list or the detected device, and contain no default that names a path of a particular machine. | review: build.rs reads CUDA_PATH, CUDA_HOME and the architecture list; scripts/check-generic.sh |
| GPU-005 | Where a binary runs on more than one GPU architecture, the midnight-gpu build script shall embed device code for every architecture of the configured list. | ci: cuobjdump lists every configured architecture |
| GPU-006 | The midnight-gpu crate shall hold its vendored third-party GPU source at a recorded upstream commit, with its licence file and a list of every local patch. | review: vendored source digest and licence file |

## Hook contract

| ID | Requirement | Verification |
|---|---|---|
| GPU-007 | The midnight-gpu crate shall answer each MSM, forward NTT, inverse NTT and quotient request with the value of the stock CPU function on the same input or with a decline. | oracle: GpuSpec.fft_eq_ntt, GpuSpec.intt_ntt, GpuSpec.ntt_intt, GpuSpec.ifft_eq_intt, GpuSpec.fftCosetExt_eq, GpuSpec.cosetToCoeff_cosetExt, GpuSpec.fftCosetToCoeff_eq and their _bls forms, GpuSpec.msmBucket_eq_msm, GpuSpec.msmBooth_eq_msm, GpuSpec.msmBoothBy_blsR_topLimb, GpuSpec.compile_correct, GpuSpec.deviceNumerator_eq; consequence of the contract: GpuSpec.resolve_eq<br>vectors: ntt.json, coset.json, msm.json, quotient.json, threshold.json<br>rust: device results equal the vectors |
| GPU-008 | When a hook declines, the midnight-proofs crate shall compute that operation with the stock CPU code on the unchanged input. | oracle (consequence of the hook contract of GPU-007, which the Rust vector and fault tests check on the real hooks): GpuSpec.resolve_eq, GpuSpec.prove_any_schedule |
| GPU-009 | If a device operation fails after its upload or after its kernel launch, then the midnight-gpu crate shall leave the caller buffer unchanged and decline. | oracle (consequence of the hook contract of GPU-007, which the Rust vector and fault tests check on the real hooks): GpuSpec.runInPlace_eq, GpuSpec.dirtyDecline_breaks<br>rust: fault injection after upload and after launch |
| GPU-010 | If an input size, a domain root, a coset shift or a quotient shape is outside what a device kernel supports, then the midnight-gpu crate shall decline before it changes any caller buffer. | oracle: GpuSpec.gate_shape, GpuSpec.gate_none_iff, GpuSpec.gate_none_iff_deviceSize, GpuSpec.gateShift, GpuSpec.gateMsm2_mismatch, GpuSpec.gate_declines_before_write, GpuSpec.deviceSize pins<br>vectors: gate.json, decline cases of ntt.json, coset.json and msm.json<br>rust: decline tests for size and root |
| GPU-011 | If the hooks are installed a second time in one process, then the midnight-proofs crate shall reject the second installation and keep the first. | oracle: GpuSpec.install_twice<br>rust: second install rejected |
| GPU-012 | When a hooked operation declines with the reason shape, unreduced, memory, fault or device-error during a proof, the midnight-gpu-prover daemon shall count one fallback for that operation. | oracle: Service.decline_counted, Service.fallback_decline, GpuSpec.fallbacks_by_reason, GpuSpec.service_fallbacks_eq_fallbackOps<br>quint: inv_fallback, test_default::declineTest, replayed<br>vectors: service/decline-reasons.json |
| GPU-085 | When a hooked operation declines with the reason no-device or below-min-k during a proof, the midnight-gpu-prover daemon shall count the decline, count no fallback for it and leave the proof unmarked. | oracle: Service.decline_counted, Service.expected_decline_no_fallback, GpuSpec.fallbacks_by_reason<br>quint: inv_fallback, expected-decline test, replayed<br>vectors: service/decline-reasons.json, service/expected-decline-accepted.json<br>rust: below-min-k and no-device declines give fallback_count 0 |
| GPU-013 | The midnight-gpu crate shall compute a masked MSM as MSM(s + r) - MSM(r) with a fixed public vector r and return the group element of the unmasked MSM. | oracle (the identity for every mask; that the mask is public, fixed and independent of the witness is a review item): GpuSpec.msmMasked_eq<br>vectors: msm.json mask fields |
| GPU-073 | When a device operation declines, the midnight-gpu crate shall add one to the decline count of its operation class and of exactly one reason out of no-device, below-min-k, shape, unreduced, memory, fault and device-error. | oracle: GpuSpec.declines_all_counted, GpuSpec.count_one_reason, GpuSpec.countDeclines_cell, Service.decline_counted, Service.invDeclines<br>quint: inv_declines, decline tests, replayed<br>vectors: service/decline-reasons.json<br>rust: decline map by class and reason equals the hook outcomes |
| GPU-074 | If an MSM input of at least one element or a transform input of a power-of-two length of at least two elements holds fewer than 2^min_k elements for the configured min_k, by default 14, then the midnight-gpu crate shall decline with the reason below-min-k before it changes any caller buffer. | oracle: GpuSpec.gate_below_min_k, GpuSpec.gateMsm_below_min_k, GpuSpec.gate_declines_before_write, pin_gate_14<br>vectors: gate.json, threshold.json, min_k of every case<br>rust: threshold tests at 2^14 - 1, 2^14 and 2^14 + 1 |
| GPU-079 | Where the quotient kernel evaluates the extended domain in tiles, the midnight-gpu crate shall return the quotient coefficients of the untiled evaluation for every tile size. | oracle: GpuSpec.numeratorTiled_eq, GpuSpec.deviceNumeratorTiled_eq, GpuSpec.quotientCoeffs_tiled, pin_tile_border_ex8<br>vectors: quotient.json quotient_coeffs<br>rust: tiled kernel against the vectors for two tile sizes |
| GPU-080 | Where the midnight-gpu crate computes two or more MSMs over one base table in one batch, the midnight-gpu crate shall return for each scalar vector the group element of its separate MSM. | oracle: GpuSpec.msmBatch_eq, GpuSpec.msmBucketBatch_eq<br>vectors: msm.json cases over one base vector<br>rust: batched MSM equals the separate MSMs |

## Randomness and transcript

| ID | Requirement | Verification |
|---|---|---|
| GPU-014 | The midnight-proofs crate shall draw the same number of random bytes in the same order from each random source whether each hook accepts or declines. | oracle (consequence of the hook contract of GPU-007, which the Rust vector and fault tests check on the real hooks): GpuSpec.prove_any_schedule (drawn count and remaining stream), GpuSpec.draws_independent_of_device (two random sources)<br>rust: random-stream byte count and hash equal |
| GPU-015 | The midnight-proofs crate shall perform the same transcript writes and squeezes in the same order whether each hook accepts or declines. | oracle (consequence of the hook contract of GPU-007, which the Rust vector and fault tests check on the real hooks): GpuSpec.prove_any_schedule (transcript)<br>rust: transcript log equal |
| GPU-016 | The midnight-proofs crate shall draw every blinding value on the CPU, from the random source and at the point of the proof where the stock prover draws it. | oracle (consequence of the hook contract of GPU-007, which the Rust vector and fault tests check on the real hooks): GpuSpec.prove_any_schedule (blinding drawn by proveStep only), GpuSpec.draws_independent_of_device<br>review: hook patch adds no random draw; quotient limb blinding stays after the quotient hook |
| GPU-017 | Where the build has the test-seed feature, the midnight-gpu-prover daemon shall produce at one fixed thread count a seeded proof byte-equal to the seeded CPU proof for every set of enabled device phases. | rust: seeded identity at a fixed thread count, thread-count control differs |
| GPU-018 | If a seed variable or a test switch is set at run time in a build without the test-seed feature, then the midnight-gpu-prover daemon shall exit with an error and write no proof. | rust: binary built without test-seed exits on a seed variable |
| GPU-019 | Where key generation runs with the hooks installed, the midnight-gpu-prover daemon shall produce proving and verifying keys byte-equal to the CPU keys. | rust: hooked key generation equals CPU key generation |

## CPU fallback

| ID | Requirement | Verification |
|---|---|---|
| GPU-020 | If no CUDA device is present at start or the configuration disables the device, then the midnight-gpu-prover daemon shall run every phase on the CPU and report device false in its start record. | oracle: Service.invCtx, Service.admit (device false)<br>quint: inv_ctx, test_nodevice::noDeviceTest |
| GPU-021 | If the daemon is absent, refuses a request, answers busy or returns an error, then the midnight-gpu-prover client shall prove the request on the CPU and label the result as a CPU fallback. | oracle: Service.invAccounted, Service.inv_run<br>quint: inv_accounted, test_default::verifyRefusedTest |
| GPU-022 | While the daemon supervisor has stopped restarting the daemon, the midnight-gpu-prover client shall prove every request on the CPU. | oracle: Service.arrive<br>quint: test_default::restartLimitTest |
| GPU-023 | If a proof in production mode completes with a fallback count above zero or an admission step of evict or cpu, then the midnight-gpu-prover daemon shall serve the proof marked degraded with the phase, the reason and the request id. | oracle: Service.reply, Service.onDevice, Service.onCpu<br>quint: test_default::declineTest, ladderEvictTest, ladderCpuTest |
| GPU-024 | Where the run mode is bench or acceptance, the benchmark harness shall fail a run in which any proof is marked degraded and record no timing row for it. | oracle: Service.invBench<br>quint: inv_bench, test_keep::benchTest |
| GPU-075 | If the configured number of daemon failures, by default 3, occurs within the configured window, by default 600 s, then the midnight-gpu-prover client shall prove every request on the CPU without contacting the daemon until the configured cooldown, by default 600 s, has passed. | oracle (the transition to open at the limit, the skip while open and the closed-daemon failure classes; persistence of the client's record is a Rust client test): Service.invBreaker, Service.invSkips, Service.breaker_open_skips, Service.breaker_opens_at_limit, Service.arrive_failure_classes, breaker pins<br>quint: inv_breaker, inv_skips, breaker tests, replayed<br>vectors: service/breaker-open-cooldown.json, service/breaker-window-expiry.json<br>rust: client breaker replay through the adapter |
| GPU-076 | When the daemon serves a proof to the client, the midnight-gpu-prover client shall clear its record of daemon failures. | oracle: Service.served_clears_failures, Service.served_then_restart<br>quint: breaker reset test, replayed<br>vectors: service/breaker-reset-on-served.json |
| GPU-077 | The midnight-gpu-prover client shall count as a daemon failure only an absent daemon, a lost connection, a prove error, a verify error and a retired reply. | oracle: Service.busy_no_failure, Service.recordFailure call sites, breaker pins<br>quint: busy and degraded-error tests, replayed<br>rust: is_daemon_failure classes |
| GPU-078 | If a request in acceptance mode is admitted at step evict or cpu or completes with a fallback count above zero, then the midnight-gpu-prover daemon shall reply with a degraded error and write no proof. | oracle: Service.invAcceptance, Service.acceptance_no_degraded_proof, Service.acceptance_degraded_refused, acceptance pins<br>quint: inv_acceptance, acceptance tests, replayed<br>vectors: service/acceptance-evict.json, service/acceptance-decline.json<br>rust: acceptance replay through the adapter |

## Device memory and admission

| ID | Requirement | Verification |
|---|---|---|
| GPU-025 | When a prove request arrives, the midnight-gpu-prover daemon shall compute its device memory need from the loaded proving key and count every resident buffer once. | oracle (an upper bound on the recorded need and the once-only count of the resident copies; the need computation from the key is the Rust need test): Service.fullNeed, Service.invNeed, Service.pin_keep_need<br>quint: inv_need, test_keep::keepNeedTest |
| GPU-026 | If the free device memory is below the computed need, then the midnight-gpu-prover daemon shall wait at most the configured wait time, by default 20 s, for the free memory to cover the need. | oracle (the two readings and the step taken; the wait deadline is a Rust admission test): Service.pin_wait<br>quint: test_default::ladderWaitTest |
| GPU-027 | If the free device memory is below the need after the wait and covers the reduced need once the resident copies are freed, then the midnight-gpu-prover daemon shall free its resident proving-key copies, run the quotient numerator of the request on the CPU and run the MSM and NTT phases of the request on the device. | oracle: Service.pin_evict<br>quint: inv_evict_step, test_default::ladderEvictTest |
| GPU-028 | If the free device memory after the eviction is below the reduced need, then the midnight-gpu-prover daemon shall free its MSM tables and run every phase of the request on the CPU. | oracle: Service.pin_cpu<br>quint: test_default::ladderCpuTest |
| GPU-029 | The midnight-gpu-prover daemon shall start no device phase whose computed need exceeds the free device memory at the admission decision. | oracle: Service.invAdmit, Service.inv_run<br>quint: inv_admit |
| GPU-030 | Where the resident policy is evict, the midnight-gpu-prover daemon shall free its resident proving-key copies and its MSM tables before it writes each reply. | oracle: Service.invEvictPolicy, Service.pin_evict_policy<br>quint: inv_evict_policy, test_default::evictPolicyTest |
| GPU-031 | The midnight-gpu-prover daemon shall create the CUDA context no earlier than its first device operation. | oracle: Service.invCtx, Service.pin_ctx_at_start<br>quint: inv_ctx<br>rust: no compute context during key generation |
| GPU-032 | If the host memory of a registered SRS base slice is freed, moved or changed, then the midnight-gpu crate shall serve no MSM from the device table of that slice. | rust: table keyed by SRS handle; a dropped handle serves no MSM |
| GPU-033 | Where transfers use page-locked host memory, the midnight-gpu crate shall keep the page-locked total at or below the configured bound. | rust: page-locked total reported and bounded |
| GPU-081 | Where the configuration names no resident policy, the midnight-gpu-prover daemon shall use the resident policy evict. | oracle: Service.defaultConfig pin (keep = false)<br>vectors: service/default-policy.json<br>rust: ResidentPolicy default |
| GPU-082 | When a prove request ends, the midnight-gpu-prover daemon shall free every MSM device context under either resident policy. | oracle: Service.wipe_frees_tables, Service.wipe_frees_tables_step, Service.invTables<br>quint: keep-policy test, replayed<br>vectors: service/keep-tables-freed.json<br>rust: end_request frees every MSM context |

## Witness erasure

| ID | Requirement | Verification |
|---|---|---|
| GPU-034 | When a prove request ends, the midnight-gpu-prover daemon shall zero and free every device buffer and host staging buffer that held witness-dependent values before it reads the next request. | oracle (the state consequence, nothing dirty between requests; the order of socket reads is a Rust daemon test): Service.invWipe, Service.invPhase, Service.inv_run<br>quint: inv_wipe<br>rust: zero-check mode reads every region as zero |
| GPU-035 | If a wipe or a release of a request is not confirmed, then the midnight-gpu-prover daemon shall reply with an error and exit before it reads another request. | oracle (the state consequence, error reply then exit; what the daemon has read from a waiting connection by then is a Rust daemon test): Service.wipe_fail_retires, Service.pin_wipe_fail, Service.pin_wipe_fail_no_verify<br>quint: test_default::wipeUnconfirmedTest |
| GPU-036 | Where zero-check mode is requested, the midnight-gpu-prover daemon shall check on the device that every zeroed region reads as zero before it frees the region and report the count of non-zero regions. | oracle (the result of the check crosses as a counter and never as region contents; which regions are checked and the count they give is the Rust zero-check test): GpuSpec.DataMove.zeroCheck_readback_violates, zeroCheck_onDevice_ok<br>rust: zero-check control (a loaded buffer is not zero) |
| GPU-037 | If the client disconnects during a request, then the midnight-gpu-prover daemon shall run no further device phase of that request and still zero and free its buffers. | oracle: Service.leaseLoss, Service.invLease<br>quint: inv_lease, test_default::leaseLossTest |

## Device-to-host traffic

| ID | Requirement | Verification |
|---|---|---|
| GPU-038 | The midnight-gpu crate shall copy from device memory to host memory only base-domain transform outputs, MSM result points, the partial bucket sums of the vendored MSM, quotient coefficients and counters, and no vector on the extended domain. | oracle: GpuSpec.DataMove.gpu038_iff, specPlan_gpu038, oldPortPlan_violates, extended_readback_violates, mislabel_impossible, msmBucketPlan_gpu038, Service.invReadback, Service.pin_readback_kinds<br>quint: inv_readback<br>vectors: datamove.json, service/readback-kinds.json<br>rust: readback_is_base_transforms_and_quotient (size of every device-to-host result copy of one proof) |
| GPU-084 | When the vendored MSM has reduced its partial bucket sums on the host, the midnight-gpu crate shall zero the host copy of those sums before it releases that memory. | oracle: GpuSpec.DataMove.msmBucketPlan_gpu084, msmBucketPlanFreeOnly_violates, msmBucketPlanNoZero_violates, gpu084_unzeroed_free_violates<br>rust: PATCHES.md wipe patches; host bucket rows read as zero after an MSM |

## Verification and keys

| ID | Requirement | Verification |
|---|---|---|
| GPU-039 | The midnight-gpu-prover daemon shall verify every proof with the stock midnight-proofs verifier before it returns the proof. | oracle: Service.invVerified, Service.invVerifyPending<br>quint: inv_verified |
| GPU-040 | If the verifier refuses a proof, then the midnight-gpu-prover daemon shall return an error, write no proof and log the request id. | oracle (error, no proof, CPU fallback; the logged request id is a Rust test): Service.pin_verify<br>quint: test_default::verifyRefusedTest<br>rust: corrupted numerator gives an error and no proof |
| GPU-041 | If the verifying key that the daemon generates or loads differs from the configured expected verifying key, then the midnight-gpu-prover daemon shall exit before it opens its socket. | rust: daemon refuses a mismatched expected verifying key |
| GPU-042 | If a request names a circuit size k above the configured maximum, then the midnight-gpu-prover daemon shall refuse it before any SRS load, key generation or device allocation. | rust: k above the maximum refused before allocation |

## Service

| ID | Requirement | Verification |
|---|---|---|
| GPU-043 | The midnight-gpu-prover daemon shall accept requests only on a local Unix socket that its own user alone can read and write. | rust: socket mode 0600 in a 0700 directory |
| GPU-044 | If a request names an input file that group or other can read, then the midnight-gpu-prover daemon shall refuse the request before it reads a byte of the file. | rust: group-readable input refused |
| GPU-045 | The midnight-gpu-prover daemon shall serve one prove request at a time and hold at most one waiting connection. | oracle: Service.invQueue, Service.pin_busy<br>quint: inv_queue, test_default::queueTest |
| GPU-046 | If a connection arrives while one request is served and one connection waits, then the midnight-gpu-prover daemon shall answer busy at once and read nothing from the connection. | oracle (the state consequence, busy counted and the caller on its CPU; which bytes are read before the busy reply is a Rust daemon test): Service.pin_busy<br>quint: test_default::queueTest |
| GPU-047 | If a request line exceeds the configured maximum size or does not arrive within the configured read deadline, then the midnight-gpu-prover daemon shall refuse the request. | rust: oversized and slow request lines refused |
| GPU-048 | If the daemon exits under systemd, then the daemon supervisor shall restart it at most the configured restart limit of times in the configured window, by default 3 restarts in 600 s. | oracle: Service.restart_cap, Service.invRestart, Service.pin_restart_window<br>quint: inv_restart, test_default::restartWindowTest |
| GPU-049 | If the daemon exits after the restart limit is reached in the window, then the daemon supervisor shall leave the daemon stopped. | oracle: Service.pin_restart_limit<br>quint: test_default::restartLimitTest |
| GPU-050 | If the device peak or the host high-water mark of a request exceeds its configured bound, then the daemon supervisor shall restart the daemon after the current request and label the next request cold. | oracle: Service.afterReply<br>quint: test_default::overBoundTest |
| GPU-051 | Where two or more daemons run on one host, the daemon supervisor shall give each daemon a disjoint CPU set and thread budget. | harness: two workers report disjoint CPU sets |

## Reporting

| ID | Requirement | Verification |
|---|---|---|
| GPU-052 | When the daemon starts, the midnight-gpu-prover daemon shall write a start record with the constraint degree, the extended k, the column, lookup and permutation counts, the resident polynomial count, the CUDA release, the device architecture, the driver version, the features, the phase mask, the resident policy, the computed need, the wsl flag and the binary sha256. | rust: start record fields |
| GPU-053 | The midnight-gpu-prover daemon shall report for every proof the prove time, the phase times, the device call counts, the fallback count, the admission step, the device peak and the host high-water mark. | rust: reply record fields |
| GPU-054 | The midnight-gpu-prover daemon shall write no witness value, key material or seed to any reply or log. | rust: log scan finds no witness, key or seed bytes |
| GPU-055 | The midnight-gpu-prover daemon shall change no GPU clock, power, mode or confidential-computing setting and make no confidential-computing query. | review: scripts/check-generic.sh and a source scan |

## WSL2 profile

| ID | Requirement | Verification |
|---|---|---|
| GPU-056 | When the daemon starts, the midnight-gpu-prover daemon shall detect WSL2 from the presence of /dev/dxg or a kernel version string that names Microsoft. | rust: is_wsl unit test |
| GPU-057 | While the caller of a request on a WSL2 host does not hold the configured device lock, the midnight-gpu-prover daemon shall run no device phase of that request. | oracle: Service.admit, Service.pin_wsl_nolock, Service.invLease<br>quint: inv_lease, test_wsl::noLockTest |
| GPU-058 | Where the host runs under WSL2, the midnight-gpu-prover daemon shall admit a request against a budget of the card total minus the configured reserve in place of the free-memory query. | oracle (the budget replaces both readings; card total minus reserve is a Rust test): Service.pin_wsl_budget<br>quint: test_wsl::budgetTest |
| GPU-059 | Where the host runs under WSL2, the midnight-gpu-prover daemon shall refuse to start with the keep resident policy. | oracle (the start refusal, Service.pin_wsl_keep; the invariant is a configuration check that cannot fail after a start): Service.configRefusals, Service.pin_wsl_keep<br>quint: inv_wsl_keep |
| GPU-060 | Where the host runs under WSL2, the midnight-gpu-prover daemon shall hold no proving-key copy and no MSM table on the device between requests. | oracle: Service.invWslIdle<br>quint: inv_wsl_idle |
| GPU-061 | If the caller loses the device lock during a request, then the midnight-gpu-prover daemon shall run no further device phase of that request and compute the rest on the CPU. | oracle: Service.leaseLoss<br>quint: test_wsl::lockLossTest |

## Containers

| ID | Requirement | Verification |
|---|---|---|
| GPU-062 | Where the daemon runs in a container, the container image shall run the daemon as a non-root user. | container: image user check |
| GPU-063 | Where the daemon runs in a container, the container launcher shall mount the SRS read-only. | container: mount table check |
| GPU-064 | Where the daemon runs in a container, the container launcher shall pass the GPU through the CDI device name nvidia.com/gpu or the NVIDIA Container Toolkit. | container: device request check |
| GPU-065 | Where the daemon runs in a container, the container launcher shall return no key, witness or seed file to the host. | container: output directory scan |
| GPU-066 | When the NVIDIA driver directory of a WSL2 host changes, the container launcher shall refuse to start a GPU container until the CDI spec names the live driver directory. | container: launcher refuses a stale CDI spec |
| GPU-083 | Where the daemon runs in a container, the container launcher shall cap the restarts of the daemon at the configured limit, by default 3, for the lifetime of the container. | container: compose restart policy on-failure:3<br>oracle: Service.lifetime_cap, Service.pin_restart_lifetime, Service.pin_restart_lifetime_any_tick (a window of 0)<br>quint: container cap tests, replayed<br>vectors: service/container-restart-cap.json |

## Test and benchmark harness

| ID | Requirement | Verification |
|---|---|---|
| GPU-067 | The benchmark harness shall report the warm median prove time over at least 5 warm repetitions in one process, the first proof apart, the ready time, the device peak and the host high-water mark. | harness: report fields |
| GPU-068 | If a reported value exceeds its configured bound, then the benchmark harness shall fail the run. | harness: a bound breach fails the run |
| GPU-069 | The midnight-gpu kernel harness shall report the device MSM time for repeated, 90 % zero and below-2^16 scalars as a ratio to the uniform-scalar time of the same length. | harness: MSM distribution report |
| GPU-070 | The midnight-gpu kernel harness shall record a standalone microbenchmark of every device kernel, with equality to the CPU result, before an end-to-end timed set. | harness: microbenchmark before the timed set |
| GPU-071 | The midnight-gpu test suite shall check the device quotient against the CPU quotient on random constraint systems that together reach every expression node type, 10,000 systems in the GPU gate and at least 14 in the default test run. | oracle (properties of the arithmetic oracle, not of the test suite; the counts are the GPU gate's): GpuSpec.compile_correct, GpuSpec.numeratorTiled_eq, hand-derived pins of the reference numerator (PinsExt)<br>rust: random constraint system fuzz |
| GPU-072 | The midnight-gpu test suite shall check the device MSM, forward NTT, inverse NTT and the coset transform of the quotient hook against the golden vectors of gpu-spec/vectors. | rust: vector tests; vectors/README.md |

# GPU prover design

This document describes how the GPU prover adds device acceleration to the
midnight-proofs prover without changing its output. The requirements are in
`requirements.md` (GPU-001 to GPU-072). The Lean oracle in `oracle/` and the
Quint model in `quint/` make the hook contract and the request state machine
executable. Requirement IDs appear in brackets.

## 1. Goals and non-goals

The GPU prover makes proofs faster on a host with an NVIDIA device. A proof
made with the device is byte-equal to the proof the CPU prover makes from the
same inputs and the same random stream [GPU-017]. Keys are byte-equal to CPU
keys [GPU-019]. A host without a device, a build without the CUDA toolkit and
a build without the `gpu` feature all prove on the CPU with the release code
[GPU-001, GPU-002, GPU-003, GPU-020].

The design does not change the proof system, the transcript, the verifier, the
circuit format or the key format. It does not move witness generation or
blinding to the device. It adds no network service: the daemon listens on a
local Unix socket only [GPU-043].

## 2. Components

| Component | Role |
|---|---|
| `midnight-proofs` with the `gpu` feature | Defines the hook points and the hook-installation API. Calls a hook where one is installed and the stock CPU function otherwise. |
| `midnight-gpu` | Device kernels (the vendored sppark MSM and NTT, the coset transforms and the quotient), the device memory layer, the wipe and the CPU stub for builds without CUDA. Installs the hooks. |
| `midnight-gpu-prover` | The resident daemon, its client, the admission ladder, the wipe, the report records and the supervisor configuration. |
| Container files | An image that runs the daemon as a non-root user, with the GPU passed through CDI. |

The feature is off by default. With the feature off, `midnight-proofs`
compiles the release prover code [GPU-001].

## 3. Pipeline and hook points

The prover runs the stock phases in the stock order: commit to the advice
columns, draw the lookup and permutation challenges, commit to the lookup,
permutation and trash polynomials, compute the quotient polynomial `h`,
commit to its limbs, evaluate, and run the multi-open argument. Every
transcript write and every challenge squeeze stays on the CPU and in the same
order [GPU-015].

With the `gpu` feature, four operations are offered to an installed hook
before the stock code runs. Only the BLS12-381 scalar field and its G1 group
reach a hook; each entry point checks the type first.

| Hook field | Hook point | Stock code on decline | Result to the host |
|---|---|---|---|
| `msm_g1` | `commit_msm` (`proofs/src/poly/kzg/mod.rs`) and `msm_specific` (`proofs/src/poly/kzg/msm.rs`) | `msm_pippenger` (commitments), blstrs `multi_exp_affine` (`msm_specific`) | one G1 point |
| `fft` | `best_fft_with_twiddles` (`proofs/src/poly/domain.rs`) | the stock FFT | the base-domain vector, written into the caller's buffer |
| `ifft` | `EvaluationDomain::ifft` | the stock FFT at the inverse root, then the scaling | the base-domain vector, written into the caller's buffer |
| `quotient` | `finalise_proof` (`proofs/src/plonk/prover.rs`), through `gpu::quotient_coeffs` | `compute_nu_poly`, `divide_by_vanishing_poly`, `extended_to_coeff` | the first `len` coefficients of `h` |

The `fft` and `ifft` hooks take base-domain sizes only: a size `n` with the
standard root of that size or its inverse. There is no coset hook and no
standalone hook for a transform on the extended domain. The coset transforms
to the extended domain, the division by `X^n - 1` and the inverse extended
transform run on the device inside an accepted quotient call, so no
extended-domain vector reaches the host. When the quotient hook declines, the
stock code computes the quotient with its cosets on the CPU.

The quotient hook gets one job: the proving key's flat expression evaluator
lowered to a device program (gates, permutation, LogUp lookups, trash), the
challenges, and the extended-domain constants that the division by the
vanishing polynomial, the inverse extended transform and the truncation use.
It returns the first `len` coefficients of `h`; the prover then commits to
them. The lowered program runs the same field operations in the same order as
the stock evaluator.

Each hook has one contract [GPU-007]: it returns the value of the stock
function on the same input, or it declines. A decline returns control to the
stock CPU code with the input unchanged [GPU-008]. A hook never draws random
bytes and never touches the transcript [GPU-014, GPU-016]. The random draws
stay where the stock prover makes them [GPU-016]. The advice and lookup
blinding values come from the caller's RNG before any hooked call that uses
them. The quotient limb blinding (`blind_quotient_limbs`) draws from `OsRng`
after the quotient hook returns, on the CPU, in the stock order. A decline
therefore cannot shift any random stream.

Hooks are installed once per process. A second installation is rejected, and
the first stays in place [GPU-011]. With no hook installed, the `gpu` feature
changes no output [GPU-002].

### Why the output cannot change

The oracle states the prover as a fold over a list of events: hooked
operations, blinding draws and transcript squeezes (`GpuSpec.Hooks.prove`).
`prove_any_schedule` proves that for any two devices that obey the contract
(each answer is the reference value or a decline), the transcript and the
number of random draws are equal. The CPU-only device is one such device, so
every device schedule gives the CPU proof. `runInPlace_eq` proves the in-place
variant, provided that a decline leaves the buffer unchanged [GPU-009], and
`dirtyDecline_breaks` shows the counterexample when a decline writes to the
buffer first.

## 4. Device kernels

**MSM.** The Pippenger MSM of sppark (`msm/pippenger.cuh`). sppark is
vendored unmodified at a recorded upstream commit, with its Apache-2.0
licence, in `gpu/third_party/sppark/` [GPU-006]. The CUDA core redirects the
sppark device allocations to its own zero-before-free wrappers by macro, in its
own translation unit, so no sppark file changes. A registered SRS slice is
uploaded into an MSM context at its first MSM, keyed by the slice handle; a
slice that fails the check against the stored points drops its table
[GPU-032]. The MSM contexts are freed at the end of every request, under either
resident policy, because a context holds the bucket sums of its last MSM; the
next request uploads the points again.

sppark sums each bucket in one thread, so a scalar that repeats many times
would send most points of a window to one bucket. The MSM is therefore
computed as `MSM(s + r) - MSM(r)`, with `r` a fixed public pseudo-random vector
that depends only on the length [GPU-013]. This is a load-balance measure, not
a blinding value. The oracle proves `MSM(s + r) - MSM(r) = MSM(s)` for every input
(`msmMasked_eq`), and proves the bucket method and the signed-digit method of
the vendored kernel equal to the plain sum for every window width
(`msmBucket_eq_msm`, `msmBooth_eq_msm`).

**NTT.** The forward and inverse NTT are the sppark NTT in natural order. The
inverse transform of sppark includes `1/n`; the hook corrects for any other
divisor. A size or root the device does not take is declined before any buffer
is touched [GPU-010]. Calls below `2^min_k` elements (default `min_k` 14)
decline, because the transfer costs more than the CPU work.

**Coset transforms.** Inside the quotient hook only. The forward transform
multiplies coefficient `i` by `zeta^(i mod 3)` (`zeta` a cube root of unity),
pads with zeros to the extended size and runs the forward NTT. The inverse runs
the inverse extended NTT and removes the coset factors.

**Quotient.** The quotient hook moves the proof's polynomials to the extended
coset, runs the numerator kernel, divides by the vanishing polynomial, runs the
inverse extended transform, removes the coset factors and reads the first
`len` coefficients into the caller's buffer. In the oracle, the gate, lookup,
permutation and trash expressions are compiled into a flat stack program (`GpuSpec.Quotient.compile`)
over column reads with rotations, challenges, constants, negation, sum,
product and scaling. One device thread evaluates the program at one point of
the extended domain. A rotation `rot` reads index `(i + rot * ratio) mod N`.
The gate values are folded with Horner's rule in `y`. The oracle proves the
compiled program equal to the tree evaluation for every expression
(`compile_correct`) and every point (`deviceNumerator_eq`). An unsupported
expression shape is declined [GPU-010]. The oracle states the numerator and
`quotientCoeffs` (division and transform back) as reference definitions.

**Field arithmetic.** The kernels work on the BLS12-381 scalar field in the
Montgomery form that the CPU code uses. The golden vectors carry canonical
integers, so a kernel test converts at the boundary.

The build script reads the
CUDA root from `CUDA_PATH` or `CUDA_HOME` and the architecture list from
configuration or the detected device [GPU-004], and embeds code for every
listed architecture [GPU-005]. Without the CUDA toolkit it builds a stub
whose every operation declines [GPU-003].

## 5. Memory and admission

Device memory holds three kinds of buffers:

- **Per-proof buffers**: the extended columns of the request, scratch space
  and the staging copies. They exist only during a request.
- **Resident proving-key copies**: the fixed and permutation polynomials on
  the extended domain.
- **MSM tables**: the uploaded SRS bases.

Under the default resident policy `evict`, the key copies and the MSM tables
live for one request: they are uploaded at the first device phase that needs
them and freed before the reply [GPU-030]. The policy `keep` is an opt-in for a
card with no other user; it holds the key copies between requests. The MSM
tables are freed at the end of every request under either policy.

At each request the daemon computes the need from the loaded proving key and
counts each resident buffer once [GPU-025]. The *full need* is the per-proof
part plus the resident part that is not already on the device. The *reduced
need* is the need of the MSM and NTT phases alone, with the quotient on the
CPU. The reduced need is part of the full need, so the
configuration refuses `reduced > perProof` (a finding of the oracle proofs;
see `RESULTS.md`).

The admission ladder decides once per request, before any device phase:

1. **gpu**: free memory covers the full need. All enabled phases run on the
   device.
2. **wait**: free memory is short. The daemon waits at most the configured
   time [GPU-026], then goes to step 1 or step 3.
3. **evict**: the daemon frees the resident key copies, moves the quotient
   to the CPU and checks the free memory again against the reduced need. When
   it fits, the MSM and NTT phases run on the device
   [GPU-027]. Freeing the copies alone cannot make the full-device proof fit:
   the full need of a request counts the key copies that are not on the device,
   so the memory they return is needed again to upload them.
4. **cpu**: even the reduced need does not fit. The daemon frees its MSM
   tables and runs every phase on the CPU [GPU-028].

No device phase starts whose need exceeds the free memory at the decision
[GPU-029]. Steps evict and cpu mark the proof degraded [GPU-023]. The resident
policy `evict` (the default) frees the key copies and the MSM tables before each
reply [GPU-030]. The opt-in policy `keep` holds the key copies for the next
request. The CUDA context
is created at the first device operation, not at start, so key generation and
CPU-only runs never hold one [GPU-031]. Page-locked host memory stays below a
configured bound [GPU-033].

## 6. Wipe

When a request ends, for any reason, the daemon zeroes and frees every device
buffer and host staging buffer that held witness-dependent values before it
reads the next request [GPU-034]. Freeing alone is not enough: device memory
is not cleared between allocations and can be read by the next process that
allocates it. If the zeroing or the release is not confirmed, the daemon
replies with an error and exits [GPU-035]. The supervisor restarts it with a
clean context. In zero-check mode the daemon checks on the device that every
zeroed region reads as zero and returns only the count of regions that do not
[GPU-036]; no zeroed region is copied to the host.

Five kinds of values cross from the device to the host on the proving path
[GPU-038]: base-domain transform outputs (`2^k` values, written into the
caller's buffer; the CPU prover holds these values at that point too), MSM
result points, the partial bucket sums of the vendored MSM (the host finishes
the reduction; the copies are counted, and the host copy is zeroed before its
memory is released [GPU-084]), the quotient coefficients once per proof, and
counters. No vector on the extended domain is copied back. The oracle states
this rule over every plan of copies (`GpuSpec.DataMove`). A disconnect stops
further device phases of the request, and the wipe still runs [GPU-037].

## 7. Service

The daemon loads one circuit, its SRS slice and its keys at start, checks the
verifying key against the configured expected key [GPU-041], and then serves
prove requests on a Unix socket with mode `0600` in a `0700` directory
[GPU-043]. It serves one request at a time and holds at most one waiting
connection. A third connection gets `busy` at once [GPU-045, GPU-046]. Request
lines have a size limit and a read deadline [GPU-047]. Input files that group
or other can read are refused [GPU-044]. A circuit size above the configured
maximum is refused before any allocation [GPU-042].

Every proof is checked with the stock verifier before it is returned
[GPU-039]. A refused proof is an error, and no proof is written [GPU-040].

The client falls back to the CPU prover when the daemon is absent, refuses,
answers busy or returns an error, and labels the result as a CPU fallback
[GPU-021, GPU-022].

A supervisor (a systemd unit or the container restart policy) restarts the
daemon after an exit, at most `limit` times in a sliding window of `window`
seconds, by default 3 in 600 s [GPU-048]. When the limit is reached, the
daemon stays stopped and every request runs on the client's CPU [GPU-049].
When a request exceeds its device or host memory bound, the daemon restarts
after the reply and the next request is cold [GPU-050].

### Run mode, decline counts and the client breaker

The daemon runs in one of two modes. In `production` (the default) a degraded
proof is served with its mark [GPU-023]. In `acceptance` a degraded request is
an error: when the admission step is evict or cpu the daemon starts no phase
of the request, and when a proof completes with a fallback count above zero
the daemon writes no proof; in both cases it replies with a degraded error
[GPU-078]. The degraded check comes before the verifier's answer is used. The
client proves a request that got a degraded error on its own CPU [GPU-021].

Every decline of a device operation is counted once, under its operation
class (`msm`, `fft`, `ifft` or `quotient`) and under exactly one reason of a
closed set: `no-device`,
`below-min-k`, `shape`, `unreduced`, `memory`, `fault`, `device-error`
[GPU-073]. An input below `2^min_k` elements (default `min_k = 14`) is declined
as `below-min-k` before any buffer changes [GPU-074].

The client keeps a circuit breaker. A *daemon failure* is an absent daemon, a
lost connection, a prove error, a verify error or a retired reply; a busy
reply, a refusal and a degraded error are not failures [GPU-077]. To record
a failure at time `now`, the client first drops every record `t` with
`now - t >= brWindow`, then appends `now`. When the record then holds `brLimit`
failures (a `brLimit` of 0 counts as 1),
the client clears the record and sets `brOpenUntil = now + brCooldown`. The
breaker is open while `clock < brOpenUntil`. While the breaker is open the client proves every request
on its CPU and does not contact the daemon [GPU-075]. A served proof clears the
record; it does not shorten an open cooldown [GPU-076]. Defaults: 3 failures,
600 s, 600 s.

The MSM device contexts are freed at the end of every request under either
resident policy [GPU-082]. With no policy named, the policy is `evict`
[GPU-081]. Under systemd the restart limit has a window [GPU-048]; a container
runtime caps restarts for the lifetime of the container, with no window
[GPU-083], and the client breaker is the windowed guard in both cases. In the
state machine a `window` of 0 means "no window": every restart since the start
counts, whatever the clock says. systemd counts starts, the first one
included, so it permits fewer restarts than the limit in the first window;
that meets "at most".

### Request state machine

The oracle (`GpuSpec.Service`) and the Quint model (`quint/gpu_service.qnt`)
state the same machine. Phases: `idle`, `accepted`, `proving`, `proved`,
`wiped`. The op encoding and the state fields are in `vectors/README.md`. The
events and their effects:

- **Arrival** (op 1). The request count rises. If the breaker is open
  (`clock < brOpenUntil`), the client proves on its CPU, counts a breaker skip
  and does not contact the daemon [GPU-075]. Otherwise, if the daemon is down
  or stopped, the client proves on its CPU and records one daemon failure
  [GPU-021, GPU-022, GPU-077]. Otherwise the daemon accepts the request when it
  is idle, holds it when nothing waits, and answers busy when one request is
  served and one waits; the busy caller proves on its CPU and records no
  failure [GPU-045, GPU-046].
- **Admission** (op 2, readings `a` = free memory at the decision, `b` = free
  memory after the wait). The ladder of section 5. Without a device: step
  none, every phase on the CPU [GPU-020]. On WSL2 without the lock: step cpu
  [GPU-057]; with the lock both readings are the budget and there is no wait
  [GPU-058]. In acceptance mode a result of step evict or cpu applies the
  frees of that step, marks the request degraded, starts no phase and moves
  the request straight to `wiped` with a confirmed (empty) wipe [GPU-078]. The
  step, the need and the free reading are recorded as the ladder computed
  them. Step none (no device) is not a degraded step and proves as usual.
- **Decline** (op 3, `a` = reason 0 no-device, 1 below-min-k, 2 shape,
  3 unreduced, 4 memory, 5 fault, 6 device-error). The count of that reason
  and the total decline count rise by one [GPU-073]. Reasons 2 to 6 mean the
  device was asked and the CPU code ran in its place: one fallback for the
  request, and the request is degraded [GPU-012]. Reasons 0 and 1 are by
  design (no device; an input below the threshold): no fallback, and the
  request stays unmarked [GPU-085]. Without this split every proof with one
  small MSM would be degraded and acceptance mode would refuse it.
- **Read-back** (op 4, `a` = kind). Kinds 0 quotient coefficients, 1 MSM
  result points and the partial bucket sums of the vendored MSM, 2 counters
  and 3 base-domain transform output are permitted. Every read-back adds one
  to `readbacks`.
  Kind 4 (a vector on the extended domain), kind 5 (the contents of a zeroed
  region) and any higher kind are refused [GPU-038, GPU-036]. The transition
  itself also adds one to `badReadbacks` for a kind above 3, so a machine that lacks
  the refusal breaks the invariant `badReadbacks = 0`.
- **Lease loss** (op 5). No further device phase; one fallback; degraded; the
  lock is no longer held [GPU-037, GPU-061].
- **End of proof** (op 6, `a` = 1 when the verifier accepts). The device
  phases end. The verifier's answer is stored; it is not counted yet
  [GPU-039]. The daemon runs the wipe before the verifier and does not run the
  verifier at all after an unconfirmed wipe or an acceptance refusal; the
  model records the answer the verifier would give and consumes it only at
  the reply, on the path that reaches the verifier.
- **Wipe** (op 7, `a` = 1 when confirmed). A confirmed wipe leaves nothing
  dirty and no MSM context [GPU-034, GPU-082]; the key copies stay only under
  `keep` off WSL2 [GPU-030, GPU-060].
- **Reply** (op 8). In this order: an unconfirmed wipe gives an error reply
  and the daemon exits; the caller and a waiting caller prove on their CPU and
  each records a daemon failure [GPU-035, GPU-077]. Else, in acceptance mode, a
  degraded request (marked degraded or with a fallback count above zero) gets
  a degraded error; the caller proves on its CPU; no failure is recorded
  [GPU-078]. A degraded error counts as an error and as a degraded refusal; it
  does not set the failed-run mark, which belongs to a served proof of a
  bench run. Else a proof that the verifier refused gets an error; the caller
  proves on its CPU and records a failure [GPU-040]. Else the verifier
  accepted: the count of verifier accepts rises by one and the proof is served
  (the served branch adds one to `unverifiedReturned` when the verifier's
  answer is not an accept, so a machine that lacks the check before it breaks
  the invariant `unverifiedReturned = 0` [GPU-039]),
  marked degraded when it is [GPU-023], a bench run with a degraded proof is
  failed [GPU-024], and the client's failure record is cleared [GPU-076]. After
  a reply without exit: an over-bound request makes the daemon exit for a
  planned restart, and a waiting caller proves on its CPU and records a
  failure [GPU-050]; otherwise the waiting request is accepted, or the daemon
  is idle.
- **Crash** (op 9). The process ends; the driver releases the device memory.
  The caller in flight and the waiting caller prove on their CPU, and each
  records a daemon failure [GPU-021, GPU-077]. A crash of an idle daemon with
  nobody waiting records no failure; the next arrival finds the daemon absent.
- **Supervisor** (op 10), **time** (op 11), **device lock** (op 12),
  **explicit evict** (op 13) and **over-bound mark** (op 14) as their names
  say [GPU-048, GPU-049, GPU-050]. An explicit evict frees the key copies and
  the MSM contexts.

When two or more failures are recorded by one event, they are recorded one
after the other at the same clock value. A failure recorded while the breaker
is open follows the same procedure, so it can move `brOpenUntil` later. A
request that the daemon accepted before the breaker opened is still served:
the breaker acts on arrivals. The events have these preconditions, and an
event outside its precondition is refused (`not-enabled`): admission needs an
accepted request; decline, read-back and lease loss need a request that is
proving with device work allowed, and a read-back of counters (kind 2) is
also possible while the request is proved, which is when the zero-check count
is read; the end of proof needs a proving request,
the wipe a proved one, the reply a wiped one; a crash needs a running daemon;
the supervisor acts on a daemon that is down and not stopped for good; the
lock changes in any phase except proving; an explicit evict needs an idle
daemon; the over-bound mark needs a proving or proved request. The decline
counts, the verifier accepts and the other counters are counters of the run:
they survive a crash and a restart. The invariants, each tagged with its
requirements, are listed in `RESULTS.md`; the oracle proves that every event
keeps them (`inv_step`, `inv_run`).

## 8. Reporting

The start record names the circuit shape, the CUDA release, the device, the
driver, the features, the phase mask, the resident policy, the computed need,
the WSL2 flag and the binary digest [GPU-052]. Each reply reports the prove
time, phase times, device call counts, the fallback count, the admission step,
the device peak and the host high-water mark [GPU-053]. No reply or log holds a
witness value, key material or a seed [GPU-054]. The daemon changes no clock,
power or mode setting of the device [GPU-055].

## 9. WSL2 profile

Under WSL2 the device is shared with the Windows host, and the free-memory
query does not see Windows allocations. The daemon detects WSL2 at start
[GPU-056] and changes three rules:

- Admission uses a budget, the card total minus a configured reserve, in
  place of the free-memory query [GPU-058].
- A request runs device phases only while its caller holds the configured
  device lock [GPU-057]. A lock lost during a request moves the rest of it to
  the CPU [GPU-061].
- No proving-key copy or MSM table stays on the device between requests
  [GPU-060], so the `keep` policy is refused [GPU-059].

The container launcher refuses to start when the CDI spec names a stale
driver directory [GPU-066].

## 10. Test and benchmark harness

The golden vectors (`vectors/`) fix the expected values of every device
transform; the Rust tests compare the kernels with them [GPU-072]. A fuzz test
compares the device numerator with the CPU numerator on random constraint
systems that reach every node type [GPU-071]. The benchmark harness reports
the warm median over at least 5 repetitions with the first proof apart
[GPU-067], fails on a bound breach [GPU-068] and on a degraded proof
[GPU-024], reports MSM ratios for skewed scalar distributions [GPU-069], and
runs a per-kernel microbenchmark with an equality check first [GPU-070].

## 11. ZK argument

The GPU prover keeps zero knowledge because it computes the same function as
the CPU prover on the same inputs:

1. Every hook returns the stock value or declines (GPU-007, checked against
   the golden vectors and by the device-model theorems).
2. A decline changes nothing (GPU-008, GPU-009; `runInPlace_eq`).
3. Random draws and transcript operations are outside the hooks and do not
   depend on the hook answers (GPU-014 to GPU-016; `prove_any_schedule`).

So the proof is the CPU proof, bit for bit, and its distribution over the
random stream is the distribution of the CPU prover. The zero-knowledge
property of the proof system carries over unchanged. The seeded byte-equality
test [GPU-017] checks this end to end on real circuits.

The proof transcript says nothing about the device. What the device side can
leak is the witness itself, held in device memory; section 12 covers that.

## 12. Threat model

**Assets**: witness values, the intermediate polynomials derived from them,
proving-key material, the random seed.

**In scope**:

| Threat | Control |
|---|---|
| Another process on the host allocates device memory after a request and reads its contents | Zero before free [GPU-034]; an unconfirmed wipe ends the daemon [GPU-035]; zero-check mode [GPU-036] |
| Another local user connects to the daemon | Socket `0600` in a `0700` directory [GPU-043]; input files must be private [GPU-044] |
| A local client floods or stalls the daemon | One request, one waiting connection, busy replies [GPU-045, GPU-046]; size limit and read deadline [GPU-047]; circuit size limit [GPU-042] |
| A device or kernel fault produces a wrong value | The stock verifier checks every proof [GPU-039, GPU-040]; a fault declines to the CPU [GPU-009] |
| A wrong or substituted key | Expected verifying key check at start [GPU-041] |
| Witness data leaves through the host side | Read-back limited to base-domain transform outputs, MSM points, quotient coefficients and counters, no extended-domain vector [GPU-038]; no secrets in logs [GPU-054] |
| A crash loop | Restart limit and stop [GPU-048, GPU-049] |
| A shared device under WSL2 | Lock, budget and no resident data [GPU-057 to GPU-061] |

**Out of scope**: an attacker with root on the host or with control of the
NVIDIA driver; physical access to the device; side channels in timing or power
(the MSM time depends on the scalar distribution, as the CPU MSM does);
confidential-computing modes [GPU-055].

**Residual risk**: when the daemon process dies, the driver frees its device
memory without zeroing it. The wipe cannot run in that case. The next
allocation by another process can see those values until the driver or the
device clears them. Hosts that share a device between users should treat a
daemon crash as a possible disclosure. This is listed as an open item in
`RESULTS.md`.

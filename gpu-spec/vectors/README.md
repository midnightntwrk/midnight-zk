# Golden vectors

The Lean oracle (`gpu-spec/oracle`) writes these files with
`oracle --vectors DIR`. Every expected value comes from a reference definition
of the oracle (the transform formulas, the plain MSM sum, the expression tree,
the service `step`), never from a device model. The one exception is the
transform outputs of `threshold.json`, which come from the radix-2 model under
a theorem that it equals the reference. The Rust crates compare their
device code against them. Do not edit the files by hand: regenerate them and
check the diff (`scripts/check_vectors.sh` fails when they are stale).

Format tag: `"format": "midnight-gpu-vectors/2"`. Every file has a `kind`; a
test loads `vectors/*.json` and `vectors/service/*.json` by glob and dispatches
on `kind`.

## Encoding

- Field elements are canonical decimal strings (no sign, no leading zero), in
  `[0, r)` for the BLS12-381 scalar field modulus
  `r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`.
  Read them with `Fq::from_str_vartime` or an equivalent decimal parser.
  They are plain integers, not Montgomery form.
- Small integers (sizes, rotations, counts) are JSON integers.
- Every file has `field`: `{"name": "bls12-381-fr", "modulus": r, "generator": "7"}`.
- Roots of unity are `7^((r - 1) / n)`. This is the convention of halo2-style
  code (`ROOT_OF_UNITY = 7^((r-1)/2^32)`, squared down to size `n`). Each case
  states the root it uses, so a kernel can be fed exactly that value.

## Expectations (every arithmetic case)

Each case of `ntt.json`, `coset.json` and `msm.json` has:

- `expect`: `"value"` or `"decline"`.
  - `"value"`: the device operation and the stock CPU function must both give
    the listed values.
  - `"decline"`: the device operation must decline with the listed `reason`
    (`no-device`, `below-min-k`, `shape`, `unreduced`, `memory`, `fault`,
    `device-error`; GPU-073) and leave the caller buffer unchanged (GPU-010).
    The listed values are the reference values; where the stock CPU function
    takes the input, the fallback must give them.
- `min_k`: the `min_k` under which the expectation holds: 1, or 0 for an MSM
  of a single point, which `min_k = 1` declines. A `value` case is shorter than
  the default threshold `2^14` (GPU-074): run it with `set_min_k` at the
  listed value; under the default `min_k` the same input must decline with
  `below-min-k`. A `shape` decline holds under every `min_k` and lists 1.
- `reason` is present only on a decline.

The expected decision comes from the oracle's entry gate (`GpuSpec.gate`,
`GpuSpec.gateMsm2`, `GpuSpec.gateShift`) with `max_log = 28`, a device present
and a reduced input; the expected values come from the reference definitions.
For a coset case the decision is the shift test, then the transform gate on
the extended length `n·ext`. For an MSM the gate takes both lengths: a scalar
count that differs from the base count is a `shape` decline.

## ntt.json

`cases[]`: `name`, `log_n`, `omega` (a primitive `2^log_n`-th root), `input`,
`ntt` and `intt`, `expect`, `min_k`, and `reason` on a decline.

- `ntt[k] = Σ_j input[j] · omega^(j·k)`.
- `intt[k] = n⁻¹ · Σ_j input[j] · omega^(-j·k)`.

Both sequences are in natural order (not bit-reversed). Value cases: random
inputs at sizes 2^1 to 2^6, and at 2^3 the edge inputs zero, all `r - 1`, a
delta and a constant. Decline cases (`shape`): the empty input, and the
lengths 3, 6 and 7, which are not powers of two (`log_n` is then that of the
next power of two, 0 for the empty input, `omega` the root of that size, and `ntt`/`intt` are empty:
the stock function does not take such an input). The length-1 case
(`log_n = 0`, `omega = 1`) is a `shape` decline as well: a device transform
needs at least two elements (GPU-010). Its `ntt` and `intt` are the
mathematical values (the element itself); the stock function is not defined
at `log_n = 0`, so a test checks the decline only and does not call it.

## coset.json

`cases[]`: `name`, `log_n`, `ext` (extension factor), `zeta` (the coset
shift), `omega_ext` (a primitive `(n·ext)`-th root), `coeffs` (`n`
coefficients, lowest degree first), `extended`, `back_to_coeffs`, `shift`,
`expect`, `min_k`, and `reason` on a decline.

- `extended[k] = Σ_i coeffs[i] · (zeta · omega_ext^k)^i` for `k < n·ext`: the
  coefficient-to-extended-coset transform.
- `back_to_coeffs` is the inverse transform of `extended`, truncated to `n`. It
  equals `coeffs`.

Two shifts. `"shift": "zeta3"` is the cube root of unity `7^((r-1)/3)`, the
shift of the prover; the device kernel multiplies coefficient `i` by
`[1, zeta, zeta^2][i mod 3]`, which equals `zeta^i` only for such a shift.
These cases expect a value. `"shift": "generic"` is the shift 7: the values are
the reference transform, and the device kernel must decline it with `shape`
(GPU-010). The coset transform is not a hook of its own: it runs inside the
quotient hook, and a test reaches the kernel through the crate's test entry.

## msm.json

The oracle's MSM runs over a toy group: `Z_r` under addition. A base is a field
element `b_i`. The result is `Σ s_i · b_i mod r`.

To check a G1 MSM, map each base to the point `P_i = b_i · G` (G the G1
generator). Because the G1 group has order `r`, the device MSM over the points
must give `result · G`. The bases are discrete logarithms by construction, so
this is a valid differential check for any MSM implementation. The base `0`
maps to the point at infinity.

`cases[]`: `name`, `scalars`, `bases`, `result`, `mask`, `masked_scalars`
(`(s_i + mask_i) mod r`), `mask_result` (`Σ mask_i · b_i`), `expect`, `min_k`,
and `reason` on a decline. GPU-013: the skewed MSM `MSM(masked) - MSM(mask)`
must equal `result`; the oracle proves this for every input
(`GpuSpec.msmMasked_eq`). Value cases: uniform scalars, all zero, one repeated
scalar, 28 of 32 zero, scalars below 2^16, all `r - 1`, a single point,
infinity bases (every fourth base 0, and all bases 0), zero scalars mixed with
infinity bases, the scalars at the fold boundary of the signed-digit method
(`(r-1)/2`, `(r+1)/2`, `1`, `r-1`, `2^254`, and scalars whose windows are all
ones), and lengths 3, 31 and 33 (an MSM length need not be a power of two).
Decline cases (`shape`): the empty input, and a scalar vector longer than the
base vector (`result` is then the reference value of the common prefix).

## quotient.json

`cases[]`: `name`, `y`, `extended_size` (`N`), `ratio` (extension factor),
`fixed`, `advice`, `instance` (lists of columns, each `N` values on the
extended domain), `challenges`, `gates` (expression trees), `numerator`
(`N` values), `quotient_coeffs`, `n`, `zeta` (the prover's shift, the cube
root of unity) and `omega_ext`.

An expression node is one of:

| node | fields |
|---|---|
| `constant` | `value` |
| `fixed`, `advice`, `instance` | `column`, `rotation` (signed rows) |
| `challenge` | `index` |
| `negated` | `arg` |
| `sum`, `product` | `left`, `right` |
| `scaled` | `arg`, `scalar` |

A column read at point `i` with rotation `rot` reads index
`(i + rot · ratio) mod N`. The numerator at point `i` is Horner in `y` over the
gates in order: `acc = 0; for g in gates: acc = acc · y + g(i)`. The first case
reaches every node type. Further cases: a single gate, two instance columns
with different data (gates read column 1), a domain of 32 points with `n = 4`
(so that `n` differs from `N/n`), rotations +2 and −3 that wrap at both
ends of the domain, a domain of 64 points with ratio 8, a case with no gate
(the numerator is zero) and a case whose columns are zero.

`quotient_coeffs` (`N` values) is the output of the quotient pipeline on that
numerator: divide point `k` by `x_k^n − 1` with `x_k = zeta · omega_ext^k`,
apply the inverse coset transform. The hook returns a prefix of it. The
oracle proves that a numerator evaluated in tiles of any size gives the same
coefficients (`GpuSpec.quotientCoeffs_tiled`, GPU-079).

## gate.json

The entry decision of a device operation as a table, with no data:
`cases[]`: `op` (`msm`, `fft` or `ifft`), `len`, `min_k`, `max_log`, `device`
(a device is present), `reduced` (the input is reduced), `expect` (`"run"` or
`"decline"`) and `reason`. It covers the default threshold (`2^14 − 1`, `2^14`,
`2^14 + 1`, `2^13`), the largest size (`2^28`, `2^28 + 1`, `2^29`), 0, 1,
lengths 1 to 3 under `min_k` 1 and 0, non-powers of
two, no device and an unreduced input, in the order of the checks: shape,
below-min-k, no-device, unreduced.

## threshold.json

Arithmetic cases at the default threshold, too long to list. The inputs are
generated: `randoms(seed, n)` is `n` field elements from the generator below,
and a case gives the seeds. Generator: `lcg(x) = (x · 6364136223846793005 +
1442695040888963407) mod 2^64`; starting from the state `seed`, each element
takes four successive outputs `s1..s4` and is
`(s1 + s2·2^64 + s3·2^128 + s4·2^192) mod r`.

- `msm[]`: `name`, `n` (`2^14 − 1`, `2^14`, `2^14 + 1`), `scalars_seed`,
  `bases_seed`, `result`, `expect` and `reason` under the default `min_k`.
- `ntt[]`: `name`, `log_n` (13 and 14), `omega`, `input_seed`, `digest`
  (`Σ_k ntt[k] · 7^k mod r`), `first` and `last` (the first and last four
  outputs), `expect` and `reason` under the default `min_k`. The outputs are
  computed with the radix-2 model, which the oracle proves equal to the
  reference at these sizes (`GpuSpec.fft_eq_ntt_bls`).

## datamove.json

The device-to-host rule of GPU-038 as data: `permitted` and `forbidden` (the
kinds of vector, with the read-back kind code of the service op 4), and
`plans[]`: `name`, `executable`, `gpu038`, `trace` (the kinds copied to the
host, in order) and `offending`. An entry of `permitted` or `forbidden` is
`{"kind": name, "code": n}`; `code` is `null` for a kind with no read-back
code of its own (`msm-buckets` travels as code 1; `scalars`, `bases` and
`base-coeffs` are never read back). Kind names: `scalars`, `bases`,
`base-coeffs`, `base-transform`, `extended`, `quotient-coeffs`, `msm-point`,
`counter`, `zeroed-region`, `msm-buckets`. The plan `spec` is one prove under the rule;
`old-port` is the port before its fix, which violates it; `msm-buckets` is the
vendored MSM with its host reduction (GPU-084). The counted-readback test
classifies each real copy by its copy site and compares with the `spec` trace:
no kind outside `permitted` may appear.

## service/*.json

Directed traces of the request state machine (`design.md`, section
"Request state machine"). Each file has `name`, `config`, `ops`, `refused` (the
refusal codes of each op, empty when the op applies) and `states`
(`ops.length + 1` states; `states[0]` is the start state).

An op is the integer `code + 100·a + 10000·b`:

| code | event | a | b |
|---|---|---|---|
| 1 | a request reaches the client | | |
| 2 | admission | free memory at the decision | free memory after the wait |
| 3 | a hooked operation declines or fails | reason: 0 no-device, 1 below-min-k (counted, no fallback), 2 shape, 3 unreduced, 4 memory, 5 fault, 6 device-error (counted, one fallback, degraded) | |
| 4 | device-to-host copy | permitted: 0 quotient coefficients, 1 MSM points and the vendored MSM's partial bucket sums, 2 counters, 3 base-domain transform output; refused: 4 extended-domain vector, 5 contents of a zeroed region, and above | |
| 5 | the lease (connection or device lock) is lost | | |
| 6 | the proof ends; the answer the verifier gives if it runs | 1 accepts | |
| 7 | zero and free the request buffers | 1 confirmed | |
| 8 | the reply is written | | |
| 9 | the daemon process dies | | |
| 10 | the supervisor acts on a daemon that is down | | |
| 11 | time passes | seconds `a + 100·b` (at least 1) | |
| 12 | the caller sets the device lock | 1 held | |
| 13 | explicit evict request | | |
| 14 | a memory bound is exceeded | | |

The op numbering is frozen: a new event gets a new code.

Configuration keys: `perProof`, `resident`, `reduced`, `budget`, `keep`,
`wsl`, `device`, `limit`, `window` (0 = no window: restarts count for the
lifetime, as under a container runtime), `bench`, `acceptance` (run mode
acceptance), `brLimit`, `brWindow`, `brCooldown` (the client breaker).

State fields: the configuration keys; the daemon (`up`, `stopped`, `phase`
0 idle / 1 accepted / 2 proving / 3 proved / 4 wiped, `waiting`, `onDev`,
`tables`, `dirty`, `ctx`, `devUsed`, `devWork`, `step` 0 none / 1 gpu / 2 wait
/ 3 evict / 4 cpu, `admNeed`, `admFree`, `fallbacks`, `degraded`, `leaseLost`,
`overBound`, `verifyOk`, `wipeOk`, `lockHeld`, `cold`, `clock`,
`restartTimes`); the client breaker (`brFails`, the times of the recorded
failures, oldest first; `brOpenUntil`, 0 at the start); and counters
(`requests`, `served`, `clientCpu`, `errors`, `busyReplies`, `degradedServed`,
`readbacks`, `badReadbacks` (read-backs of a kind outside the permitted set; a
refused op never runs, so this stays 0 unless the refusal is missing),
`unverifiedReturned` (proofs served without a verifier accept; stays 0 unless the
reply skips the check), `verifyAccepts`, `declines` (seven counts, one per reason, in the
order of op 3), `declined` (their total), `breakerSkips`, `degradedRefused`,
`runFailed`). Memory is in abstract units.

A Rust test of the daemon's admission and supervisor logic drives its own code
with the same events and compares the fields it models (for example `step`,
`admNeed`, `onDev`, `waiting`, `busyReplies`, `up`, `stopped`). The oracle also
answers single steps (`oracle --step`, JSON Lines) and whole runs
(`kink-implementation/1` on stdin), so a test can ask it directly.

# gpu-spec

The specification of the GPU prover, in four forms that check each other:

| Path | What it is |
|---|---|
| `requirements.json`, `requirements.md` | 85 EARS requirements, GPU-001 to GPU-085. The JSON is authoritative; the Markdown is generated from it. |
| `design.md` | Pipeline, hook points, device kernels, memory and admission, wipe, fallback, the zero-knowledge argument and the threat model. |
| `oracle/` | An executable Lean 4 oracle: reference field arithmetic, transforms, MSM and quotient numerator, device models with theorems, and the request state machine with invariant proofs. |
| `quint/` | A Quint model of the request state machine, written from the requirements and the design only. |
| `vectors/` | Golden vectors written by the oracle, for the Rust tests. Format in `vectors/README.md`. |
| `scripts/` | Gates and helpers. |
| `RESULTS.md` | What the checks found and what is still open. |

## Tools

- Lean 4 through `elan`. The toolchain is pinned in `oracle/lean-toolchain`
  (`v4.35.0`); `lake` installs it on first use. No Mathlib.
- Quint 0.32.0 (`npm i -g @informalsystems/quint@0.32.0`). The gate uses
  `quint run` and `quint test` only, which need no Apalache.
- Python 3.11 or later, standard library only.

## Build the oracle

```sh
cd gpu-spec/oracle
lake build --wfail
```

This builds the library and the `oracle` executable, checks every theorem,
runs the pins of `GpuSpec/Tests.lean` (`decide +kernel` and `#guard`), and
runs the audit of `GpuSpec/Audit.lean`: the axioms of each theorem are pinned
with `#guard_msgs` (only `propext`, `Classical.choice` and `Quot.sound`
appear), and `#audit_ns GpuSpec` must list no `implemented_by`, `extern`,
`partial`, `unsafe`, `opaque` or `axiom` declaration. A `sorry` fails the build.

## Run the oracle

Set `LEAN_ABORT_ON_PANIC=1` for every oracle process.

**Whole run** (`kink-implementation/1`, one JSON request on stdin):

```sh
echo '{"protocol":"kink-implementation/1","inputs":{"config":{"perProof":6,"resident":8,
"reduced":2,"budget":0,"keep":false,"wsl":false,"device":true,"limit":3,"window":600,
"bench":false,"acceptance":false,"brLimit":3,"brWindow":600,"brCooldown":600},
"ops":[1,202002]}}' | oracle/.lake/build/bin/oracle
```

The answer is `{"end":"final","cells":{"s":{...}}}` with the end state, or
`{"end":"could-not-apply","reason":CODES}` with the sorted refusal codes of the
first refused config or op, joined by `|`.

**Single steps** (`--step`, JSON Lines): each input line is
`{"state":{"s":{...}},"op":N}`. Each output line is one of:

- `{"state":{"s":{...}}}`: the next state;
- `{"refused":[CODES]}`: the op is not enabled in the state, the op is not a
  valid op, or the state is outside the state domain (it fails an invariant).
  The state is unchanged;
- `{"error":TEXT}`: the line does not decode (unknown or missing key, wrong
  type, a fraction, a non-canonical integer, an over-long line).

Refusal codes: `not-an-operation`, `bad-argument`, `readback-not-permitted`,
`not-enabled`, `outside-state-domain`, `bad-config`, `wsl-keep-refused`. The op
encoding and the state fields are in `vectors/README.md`.

**Golden vectors**: `oracle --vectors DIR` writes `ntt.json`, `coset.json`,
`msm.json`, `quotient.json`, `gate.json`, `threshold.json`, `datamove.json` and
`service/*.json` into `DIR`. Two runs give the same bytes.

## Gates

From `gpu-spec/`:

```sh
python3 -I scripts/gen_requirements_md.py --check     # requirements.md matches the JSON
python3 -I scripts/check_refs.py                      # the names in the verification column exist
scripts/check_vectors.test.sh                         # the vector gate can fail (negative test)
scripts/check_vectors.sh                              # vectors are current; codec checks
scripts/quint_check.sh                                # Quint simulation and ITF replay
scripts/mutants.py COPY                               # mutation run on a scratch copy (hours)
```

`check_vectors.sh` rebuilds the oracle, writes the vectors into a temporary
directory twice, compares both exports with each other and with `vectors/`,
and runs `check_step_codec.py`: a round trip of a non-initial state with every
field kind through `--step`, refusal controls with their exact codes, decode
error controls, and the default mode against the end state of every service
trace. `check_vectors.test.sh` runs the gate on copies with a hand-edited
value, a stale trace, a missing file and an extra file; each must fail. CI
(`.github/workflows/gpu-spec.yml`) runs the build and these three checks.

`quint_check.sh` (about 40 minutes at the default sample count) builds the
oracle, typechecks the model, runs the assignment lint, then for each of the
20 instances:

1. `quint run` with `--invariant inv` and the witnesses at 10,000 samples of
   40 steps, seed 20261117;
2. exports 50 ITF traces and replays every transition through `oracle --step`
   with `scripts/quint_replay.py --op-var lastOp --compare s --drop prev`
   (`prev` is a ghost variable of the model).

It then runs the directed tests of `quint/gpu_service_test.qnt`, replays their
traces, runs the refusal tests (not replayed: a refused step is not a
transition), and runs a negative control: traces with a changed `resident`
constant must give `DISAGREE`. Pass a smaller sample count for a quick run:
`scripts/quint_check.sh 300 10`.

## EARS lint

Each statement is one sentence in one of three forms: `The X shall ...`,
`While/When/Where ..., the X shall ...` or `If ..., then the X shall ...`, with
one `shall`, a named system and no trailing condition. An EARS linter in strict
mode reports 85 requirements, 0 defects and 0 warnings.

## Layout of the oracle

| Module | Content |
|---|---|
| `GpuSpec/Field.lean` | Modular arithmetic, the BLS12-381 scalar modulus, roots of unity |
| `GpuSpec/Ntt.lean` | Reference NTT, iNTT and coset transforms; the radix-2 device model |
| `GpuSpec/Algebra.lean`, `GpuSpec/NttProofs.lean` | The bridge from `Nat mod p` to a commutative ring; the general transform theorems and their BLS12-381 anchors |
| `GpuSpec/Msm.lean`, `GpuSpec/MsmProofs.lean` | MSM over the toy group `Z_r`; the bucket, signed-digit and batch device models; the general MSM theorems; the masked MSM |
| `GpuSpec/Quotient.lean` | Expression AST, reference numerator, the compiled stack program, tiled evaluation, quotient coefficients |
| `GpuSpec/Hooks.lean` | Devices that answer or decline; the prover as a fold over events; schedule independence |
| `GpuSpec/Declines.lean` | Decline reasons, counts by class and reason, the entry gate |
| `GpuSpec/DataMove.lean` | Where each vector lives and every copy; GPU-038 and GPU-084 as theorems over plans |
| `GpuSpec/Service.lean` | The request state machine, its refusals and its invariants |
| `GpuSpec/ServiceProofs.lean` | Every transition keeps the invariants; the breaker, acceptance and retirement theorems |
| `GpuSpec/Vectors.lean`, `GpuSpec/VectorsExt.lean` | The golden vector cases, their expected decisions and the directed service traces |
| `GpuSpec/Tests.lean`, `GpuSpec/PinsExt.lean`, `GpuSpec/VectorPins.lean` | Pins written from the requirement sentences; device models on every vector case; case counts |
| `GpuSpec/Audit.lean`, `GpuSpec/AuditNtt.lean` | Axiom and declaration audit |
| `Main.lean` | JSON codec and the three modes; no transition logic |

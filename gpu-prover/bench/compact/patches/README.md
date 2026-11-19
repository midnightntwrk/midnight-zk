# Patches

## `suite/`

The three source patches that `fetch-suite.sh` applies after it checks the upstream sha256 of
each file. `suite.json` records the sha256 before and after each patch.

| Patch | Program | Change | Reason |
|---|---|---|---|
| `d01-example-bboard.patch` | midnightntwrk/example-bboard `bboard.compact` | `pragma language_version 0.23;` to `>= 0.23;` | compactc 0.36.0 is language 0.28.0 and refuses the exact pin |
| `d02-battleship.patch` | midnightntwrk/example-battleship `battleship.compact` | same pragma change | same |
| `h03-election-ctor.patch` | LFDT-Minokawa/compact `examples/election.compact` | adds `constructor(a: Bytes<32>) { authority = disclose(a); }` | the example has no constructor, so `authority` stays zero and no call passes setup; with the constructor the authorized circuits become provable |

h01 is the same file without the patch.

## The hooked build: midnight-proofs 0.8.3 with GPU hooks and a backend crate

The proof server 9.0.1 proves with midnight-proofs 0.8.2 (the `^0.8.2` requirement resolves
0.8.3). The two versions differ only in the MSM dispatch for more than 2^19 terms; every MSM
of this suite is smaller, so both run the same CPU code.

A GPU run needs two crate directories, given to `scripts/build.sh hooked PROOFS BACKEND`:

- `PROOFS`: midnight-proofs 0.8.3 with GPU hooks: a registry of optional device functions
  (G1 MSM, forward and inverse NTT, coefficient to extended-coset transform, the quotient
  polynomial) that `create_proof` consults; each may decline, and then the stock CPU code
  runs. With nothing registered the crate is stock 0.8.3. This is the hook design of the GPU
  prover in this repository, on the 0.8 line.
- `BACKEND`: a crate named `compact-bench-gpu` with the API of `gpu-backend-stub/`
  (`install_hooks() -> Option<String>`, `counters()`, `reset_counters()`). It registers its
  device functions in the hooks of `PROOFS` and counts device calls and fallbacks.

The script passes both as `[patch]` entries on the command line, so the tree keeps the stock
build and the stub. The run labels its rows `hooked` only when `install_hooks` reported a
device; a `gpu` build without hooks writes `hooked-inactive`.

The measured GPU results in `results/` used the hooks of this design backported to 0.8.3 and
a CUDA backend of the same design. The pull request carries the same design on midnight-proofs
0.9.0-rc.1; the 0.8.3 backport is not part of it.

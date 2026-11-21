# Container test record

This file records what was tested with the container files in this
directory, on which platform, and the result.

## Platform

| Item | Value |
| --- | --- |
| GPU | NVIDIA GeForce RTX 5090 Laptop GPU, 24 GB |
| Platform | WSL2 (kernel 6.18, x86_64) |
| NVIDIA driver | 616.92 (Windows), CUDA UMD 13.4 |
| Docker | 29.1.3, CDI enabled (`/etc/cdi`, `/var/run/cdi`), no buildx plugin |
| NVIDIA Container Toolkit | 1.19.0 |

## Status

| Test | Result |
| --- | --- |
| Image build (amd64, CPU stub) | pass |
| CPU end to end (health, prove, CPU fallback) | pass |
| Docker HEALTHCHECK | pass |
| Restart cap with the real image | pass (CPU image and CUDA image with CDI) |
| `check-cdi.sh` on WSL2 | pass, after a fix |
| CDI start gate `run-gpu.sh` (`check-cdi.test.sh`) | pass, hermetic and WSL2 host cases |
| CUDA image build, all default archs | pass |
| `check-no-test-seed.sh` on both images | pass (release clean, test image refused) |
| GPU end to end with CDI (WSL2, RTX 5090) | pass for the daemon path; at the example's k = 6 no call reached the device (see below) |
| Device tests `tests/gpu.rs` in the container with CDI | pass, 3 of 3 (seeded byte equality, zero-check, injected faults) |
| Seeded `seeded_prove`: GPU container vs CPU-only container | equal SHA-256, but at k = 6 with no device call |
| arm64 build | not run |

## GPU end to end (CUDA image, CDI, WSL2)

Platform: NVIDIA GeForce RTX 5090 (32 GB), WSL2, Windows driver 616.92,
CUDA 13.4, Docker 29.7 with CDI (`/var/run/cdi/nvidia.yaml`, device
`nvidia.com/gpu=all`), NVIDIA Container Toolkit 1.19.1. Tree: integration
branch at 9f966bbc.

- Build: release image 286 s cold, with kernels for sm_80, sm_86, sm_89,
  sm_90, sm_100, sm_120 and sm_121 (`MIDNIGHT_GPU_REQUIRE_CUDA=1`); content
  210 MB. The daemon links `libcudart.so.13` from the base image. The
  `gpu-test` image (`cuda test-seed`, sm_120 only) built in 57 s.
- `check-no-test-seed.sh`: the release image is clean (exit 0); the
  `gpu-test` image is refused (exit 1: `seeded_prove` and the test-seed
  marker).
- Every container ran with `--read-only --cap-drop ALL --security-opt
  no-new-privileges --network none` and was started through `run-gpu.sh`
  (`check-cdi.sh` passed first).
- Start record: device "NVIDIA GeForce RTX 5090", sm_120, features `cuda`
  and `midnight-gpu-linked`, `wsl: true`; health `device: true`, phases
  msm, fft, ifft and quotient.
- Device lock: a lock file on the socket volume
  (`MIDNIGHT_GPU_PROVER_LOCK`), client `--lock`. With the lease: label
  `gpu`, 0 fallbacks. `--zero-check`: `wipe.checked` true. Without the
  lease: label `cpu` with the reason "the device lock is not held by the
  caller", as the WSL2 profile requires.
- At the example relation's k = 6 every device call was declined with
  `below-min-k` (the default `MIDNIGHT_GPU_MIN_K` is 14). So the daemon
  proofs had no device call (`device_calls` empty, MSM count 0) and the
  wipe had 0 regions, although the label was `gpu`.
- `tests/gpu.rs` in the `gpu-test` image with CDI: 3 of 3 passed. These
  tests assert MSM count > 0, device calls, 0 fallbacks, a seeded device
  proof byte-equal to the seeded CPU proof (8 threads), and a zero-check
  that reads back more than 0 regions.
- `seeded_prove` (seed 7, 8 threads): the device-path proof in the GPU
  container, the CPU proof in the same process and the CPU proof in a
  CPU-only container have one SHA-256
  (`dc748f75e41d244cfffabc4e4926432a36b40fb7aba93461a08132d568f01eca`). At
  k = 6 the device path made no device call.
- Restart cap with the CUDA image and CDI: with a missing SRS the
  entrypoint exited 64 four times; then the container stayed exited with
  RestartCount 3 and health `unhealthy`. A client `prove` then gave label
  `cpu-fallback` and a proof.

## Image build

The `midnight-gpu` crate is not in the tree at this commit, so the `cuda`
feature of `midnight-gpu-prover` builds no device code. The image is a CPU
image. `MIDNIGHT_GPU_REQUIRE_CUDA=1` had no crate to check. The start record
shows `"device": null` and `"phases": []`.

- Build: `docker compose -f gpu-prover/container/compose.yaml build prover`
  (the host has no buildx plugin; Compose used the daemon's BuildKit).
  `docker build` without buildx fails, and the legacy builder cannot build the
  Dockerfile (`RUN --network=none`, `COPY --chmod`).
- Cold build time: 158 s (base image pulls 74 s, apt 23 s, toolchain 9 s,
  `cargo vendor` 11 s, offline release build 30 s).
- Image content size 205 MB (820 MB on disk, unpacked). Image ID
  `sha256:ad16318d7d6df6b945c2855d4fd16a7f20f09d5777745e1953938bd5e3c75c09`.
- Base images: the pinned digests in the Dockerfile resolved and pulled.
- The `gpu-test` target (`CARGO_FEATURES="cuda test-seed"`) built in 47 s on
  a warm cache. Its test binary ran with 0 tests, because `tests/gpu.rs`
  compiles only when the CUDA crate is linked. Image ID
  `sha256:9604b9b12d4848656bd0e64368e1539fd34fe0f872d6e3ba82afdff8a32e7d4e`.

## CPU end to end

Setup: daemon container with `--read-only --tmpfs /tmp --cap-drop ALL
--security-opt no-new-privileges --network none --restart on-failure:3`. The
public Midnight SRS file `midnight-srs-2p6` is mounted read-only (the example
relation has k = 6), and a named volume holds the socket. The client runs in a
second container with the same volume at the same path.

| Step | Result |
| --- | --- |
| Daemon user | uid 10001, gid 10001 |
| `healthcheck.sh` in the daemon container | exit 0, state `ready` |
| `health` from the client container | exit 0 |
| `prove` (96-byte input, mode 600, owner 10001) | `ok`, label `cpu`, proof 2932 bytes, mode 600, `verify_s` 0.002 (built-in stock verifier) |
| `stop` | daemon exit 0, RestartCount 0 (on-failure does not restart a clean stop) |
| `prove` after the stop | `ok`, label `cpu-fallback`, `daemon_error` "cannot connect to the daemon", proof written |
| Docker health status | `healthy` about 5 s after start; `docker stop` gives exit 0 |

The proofs were checked by the verifier step that the daemon and the client
run before they write a proof. No separate verifier was run.

## Restart cap with the real image

This run used the CPU image. The daemon container started with `MIDNIGHT_GPU_PROVER_SRS` set to a missing
file and `--restart on-failure:3`.

- The entrypoint exited with status 64 on each of 4 runs.
- Final state: `exited`, RestartCount 3, exit code 64. No further restart in
  the next 8 s.
- A client `prove` on the same socket volume then gave label `cpu-fallback`
  and a proof.

## check-cdi.sh on WSL2

The first run exited 1 with no message. The script ran `nvidia-ctk cdi
generate --output=/dev/stdout`, which fails because nvidia-ctk writes a
temporary file in the directory of the output. The script now reads the spec
from the standard output of `nvidia-ctk cdi generate`.

After the fix:

- The current spec: `OK (11 host paths present)`, exit 0.
- A copy of the spec with another driver directory name: reported stale,
  with the live driver directory, exit 1 (the exit code of the script, read
  without a pipe).

## CDI start gate

`check-cdi.test.sh` on WSL2 (RTX 5090 and RTX 5090 Laptop GPU), all cases pass (exit 0):

| Case | Result |
| --- | --- |
| Spec names the live driver directory | command runs |
| Spec names an old directory that is still on disk | refused, exit 1 |
| Spec names a missing directory | refused, exit 1 |
| The same without `nvidia-ctk` | refused, exit 1 |
| No spec file | refused, exit 1 |
| One current and one stale spec | refused, exit 1 |
| Host spec | command runs |
| Copy of the host spec with a renamed driver directory | refused, exit 1 |
| Without `nvidia-ctk`: old directory with libcuda still on disk, stale spec | refused, exit 1 |
| Without `nvidia-ctk`: two directories with libcuda, current spec | refused, exit 1 (live driver unknown) |
| Without `nvidia-ctk`: one directory with libcuda, current spec | command runs |
| Without `nvidia-ctk`: stale spec whose paths all exist | refused, exit 1 |
| Without `nvidia-ctk`: no directory with libcuda | refused, exit 1 |
| Host spec, without `nvidia-ctk` | command runs |
| Renamed host copy, without `nvidia-ctk` | refused, exit 1 |

With `CHECK_CDI` set to a check that always passes, 9 cases fail, so the test
detects a gate that does not check.

## Runtime libraries

The CUDA crate links `cudart` as a shared library. The runtime base image has
`libcudart.so.13` (13.4.92) and `libstdc++.so.6` in the loader cache, so no
toolkit file is needed in the runtime stage. The driver library (`libcuda`)
comes from the host through CDI or the NVIDIA Container Toolkit.

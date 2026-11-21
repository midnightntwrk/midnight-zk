# GPU prover container

This directory holds the files that build and run `midnight-gpu-proverd`, the
GPU prover daemon, in a container or as a systemd service.

| File | Purpose |
| --- | --- |
| `Dockerfile` | Multi-stage image build (CUDA devel builder, CUDA base runtime). |
| `Dockerfile.dockerignore` | Build-context filter for this Dockerfile. |
| `entrypoint.sh` | Checks the SRS and socket mounts, then runs the daemon as PID 1. |
| `healthcheck.sh` | Sends the daemon's `health` request with `midnight-gpu-prover-client`. |
| `compose.yaml` | Compose example, with NVIDIA Container Toolkit and CDI variants. |
| `midnight-gpu-proverd.service` | Example systemd unit for a host install. |
| `check-cdi.sh` | Refuses a stale CDI spec (WSL2 driver directory). |
| `run-gpu.sh` | Start gate for a CDI GPU container: runs `check-cdi.sh`, then the command; refuses a stale spec. |
| `check-cdi.test.sh` | Test of `check-cdi.sh` and `run-gpu.sh` with current and stale specs (no GPU needed). |
| `check-no-test-seed.sh` | Refuses an image that holds a `test-seed` build (marker string or a `*seeded*` file). |
| `check-no-test-seed.test.sh` | Test of `check-no-test-seed.sh` (no GPU needed). |
| `restart-cap.test.sh` | Test of the restart cap in systemd and Docker (no GPU needed). |
| `TESTED.md` | What was tested with these files, on which platform, and the result. |

## Build

Build from the repository root. The build context is the whole workspace.

```sh
docker buildx build -f gpu-prover/container/Dockerfile -t midnight-gpu-prover:local .
```

The Dockerfile needs BuildKit (`RUN --network=none`, `COPY --chmod`,
`TARGETARCH`). `docker buildx build`, and `docker build` with the buildx
plugin installed, use it. The legacy builder cannot build this file. On a
host with Docker Compose but without the buildx plugin, Compose builds with
the BuildKit of the Docker daemon:

```sh
SRS_DIR=/nonexistent SRS_FILE=unused PROVER_IMAGE=midnight-gpu-prover:local \
  docker compose -f gpu-prover/container/compose.yaml build prover
```

(`SRS_DIR` and `SRS_FILE` must be set because `compose.yaml` requires them;
the build does not read them. Pass build arguments with `--build-arg`.)

The host does not need a GPU or a CUDA install to build. The CUDA toolkit
comes from the builder image.

Build arguments:

| Argument | Default | Meaning |
| --- | --- | --- |
| `MIDNIGHT_GPU_ARCHS` | `sm_80,sm_86,sm_89,sm_90,sm_100,sm_120,sm_121` | GPU architectures to compile kernels for. A smaller list builds faster. |
| `CARGO_FEATURES` | `cuda` | Cargo features of `midnight-gpu-prover`. |
| `PROVER_UID`, `PROVER_GID` | `10001` | User and group that run the daemon. |
| `UBUNTU_SNAPSHOT` | `20261116T000000Z` | Ubuntu archive snapshot for apt. |
| `CUDA_DEVEL_IMAGE`, `CUDA_RUNTIME_IMAGE` | CUDA 13.4.3, Ubuntu 24.04, pinned by digest | Base images. |

The image contains the daemon `midnight-gpu-proverd` and the client
`midnight-gpu-prover-client`.

To build for one GPU only, for example an RTX 5090:

```sh
docker buildx build -f gpu-prover/container/Dockerfile \
  --build-arg MIDNIGHT_GPU_ARCHS=sm_120 -t midnight-gpu-prover:local .
```

### How the build is pinned

- Both base images are pinned by the digest of their multi-arch index
  (amd64 and arm64). The digest selects the same image on every build.
- apt reads only the dated snapshot on `snapshot.ubuntu.com`. The builder
  removes the NVIDIA apt repository of the base image, because that
  repository is not dated. Named packages have exact versions.
- `rustup-init` has a fixed version and SHA-256 for each architecture. The
  Rust toolchain is the one in `rust-toolchain.toml`. There is no `nvptx64`
  target: `nvcc` compiles the kernels.
- Crates are downloaded in one stage only. The `vendor` stage runs
  `cargo vendor --locked` against `Cargo.lock` and writes the vendored
  sources plus a cargo config that replaces every registry and git source
  with them. The `builder` stage runs with no network
  (`RUN --network=none`) and builds with `--locked --offline` and that
  config. A crate that is not in `Cargo.lock` fails the build.
- `MIDNIGHT_GPU_REQUIRE_CUDA=1` is set in the builder. If `nvcc` is missing,
  the build fails. Without it, `midnight-gpu` builds a CPU stub.

The runtime image contains the two binaries and the two scripts. It has no
compiler, no Rust toolchain, no vendored sources and no credentials.

## Run with the NVIDIA Container Toolkit

The host needs the NVIDIA driver and the
[NVIDIA Container Toolkit](https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/install-guide.html).

```sh
docker volume create midnight-gpu-prover-socket
docker run -d --name midnight-gpu-prover \
  --gpus all \
  --restart on-failure:3 \
  --read-only --tmpfs /tmp \
  --cap-drop ALL --security-opt no-new-privileges \
  -v /path/to/srs:/srv/midnight/srs:ro \
  -e MIDNIGHT_GPU_PROVER_SRS=/srv/midnight/srs/<srs file> \
  -v midnight-gpu-prover-socket:/run/midnight-gpu-prover \
  midnight-gpu-prover:local
```

The daemon reads its other settings from `MIDNIGHT_GPU_PROVER_*` environment
variables or a JSON file named by `MIDNIGHT_GPU_PROVER_CONFIG`; see the
`midnight-gpu-prover` crate. Arguments after the image name go to the daemon.

## Run with CDI

CDI (Container Device Interface) describes the GPU devices and driver files
in a spec file. Docker 25 and later (with CDI enabled) and Podman read it.

```sh
sudo nvidia-ctk cdi generate --output=/etc/cdi/nvidia.yaml
nvidia-ctk cdi list            # shows nvidia.com/gpu=0, ..., nvidia.com/gpu=all

gpu-prover/container/run-gpu.sh docker run -d --name midnight-gpu-prover \
  --device nvidia.com/gpu=all \
  --restart on-failure:3 \
  -v /path/to/srs:/srv/midnight/srs:ro \
  -e MIDNIGHT_GPU_PROVER_SRS=/srv/midnight/srs/<srs file> \
  -v midnight-gpu-prover-socket:/run/midnight-gpu-prover \
  midnight-gpu-prover:local
```

Start a CDI GPU container only through `run-gpu.sh`. It runs `check-cdi.sh`
on the spec files (`MIDNIGHT_GPU_CDI_SPECS`, default `/etc/cdi/nvidia.yaml`
and `/var/run/cdi/nvidia.yaml`). If a spec is missing or stale, it prints the
reason, does not run the command and exits 1. Otherwise it runs the command.

Regenerate the spec after every driver update.

### WSL2

On WSL2 the GPU driver is in a directory under `/usr/lib/wsl/drivers/` whose
name changes when the Windows NVIDIA driver is updated. The CDI spec names
that directory. After a driver update the spec is stale, and the container
starts without a working GPU.

`run-gpu.sh` runs `check-cdi.sh` before each start. In a systemd unit that
starts the container, put `check-cdi.sh` in `ExecStartPre=`. The script
exits 1 when a path in the spec does not exist. An old driver directory can stay on disk after an update, so when
`nvidia-ctk` is installed the script also generates a spec from the live
driver and exits 1 if that spec names another driver directory. Without
`nvidia-ctk`, the live driver is the one directory under
`/usr/lib/wsl/drivers/` that holds `libcuda.so.1.1`; if there is no such
directory or more than one, the script exits 1 (it does not accept a spec it
cannot confirm). Then regenerate the spec
with `sudo nvidia-ctk cdi generate --output=/etc/cdi/nvidia.yaml`. Do not
start the prover with a stale spec.

Limit: a restart under the restart policy (`on-failure:3`) does not go
through `run-gpu.sh`. After a driver update, stop the container, regenerate
the spec and start the container again through `run-gpu.sh`.

`check-cdi.test.sh` tests the gate. It makes specs that name the live driver
directory, an old directory that is still on disk, and a missing directory,
with a stub `nvidia-ctk`, and checks that `run-gpu.sh` runs the command only
for the current spec. On WSL2 it also copies the host spec, changes its
driver directory name, and checks that `run-gpu.sh` refuses the copy.

```sh
gpu-prover/container/check-cdi.test.sh
```

## SRS

Mount the directory that holds the SRS (structured reference string) file
read-only at `/srv/midnight/srs`, and set `MIDNIGHT_GPU_PROVER_SRS` to the
file in it. The file is in the `ParamsKZG::write_custom` raw format of the
Midnight and Filecoin SRS files. The entrypoint exits with status 64 if the
variable is unset or the file is missing or not readable, and prints a
warning if the file is writable. `--srs FILE` or `--insecure-test-srs` on the
command line replace the variable.

## Socket

The daemon listens on the Unix socket `/run/midnight-gpu-prover/proverd.sock`
(`MIDNIGHT_GPU_PROVER_SOCKET`). Mount a volume or a host directory at
`/run/midnight-gpu-prover` to reach the socket from other containers or from
the host. The daemon makes the socket with mode 0600, so a client must run
with the same uid as the daemon (`10001` by default) or as root. Build with
`PROVER_UID` set to the client's uid if they differ.

## Input and output files

The paths in a `prove` request are paths in the daemon's file system. The
daemon reads the input file and writes the proof there. The input file must
be owned by the daemon's uid and have mode 600. Give the daemon and its
clients one shared directory at the same path, for example the socket volume
or a second volume mounted at the same path in both containers. With
`--read-only`, the daemon can write the proof only to such a mounted
directory or to `/tmp`.

```sh
docker run --rm -v midnight-gpu-prover-socket:/run/midnight-gpu-prover \
  -v /path/to/srs:/srv/midnight/srs:ro \
  --entrypoint /usr/local/bin/midnight-gpu-prover-client midnight-gpu-prover:local \
  --socket /run/midnight-gpu-prover/proverd.sock \
  prove /run/midnight-gpu-prover/in.bin /run/midnight-gpu-prover/proof.bin \
  --srs /srv/midnight/srs/<srs file>
```

The client needs the SRS (`--srs`) only for its CPU fallback.

## Non-root user

The daemon runs as uid `10001` and gid `10001`. Change them with the
`PROVER_UID` and `PROVER_GID` build arguments, or with `--user` at run time.
If you use `--user`, the socket directory must be writable by that user. A
new named volume copies the ownership of `/run/midnight-gpu-prover` from the
image, which is the build-time user.

## Health

`HEALTHCHECK` runs `healthcheck.sh` every 30 s (timeout 10 s, start period
120 s, 3 retries). The script fails if the socket does not exist, and
otherwise runs `midnight-gpu-prover-client --socket <socket> health`. Set
`MIDNIGHT_GPU_PROVER_HEALTH_CMD` to replace the command.

```sh
docker inspect -f '{{.State.Health.Status}}' midnight-gpu-prover
```

## Restart policy

A daemon that keeps failing must stop, so that clients fall back to the CPU
prover instead of waiting on a restart loop.

- Docker and Compose: `restart: on-failure:3`. Docker restarts the container
  at most 3 times (4 runs), then leaves it exited. An unhealthy status does
  not restart a container; only an exit does.
- systemd: `Restart=on-failure` with `StartLimitBurst=3` and
  `StartLimitIntervalSec=600`. systemd starts the daemon at most 3 times in
  600 s. The next restart is refused, and the unit stays `failed` with
  `Result=start-limit-hit`. Clear it with
  `systemctl reset-failed midnight-gpu-proverd`.

`restart-cap.test.sh` checks both caps with a stub that exits 1. It reads the
settings from `midnight-gpu-proverd.service` and `compose.yaml`, uses a
transient `systemd-run --user` unit and a `busybox` container pinned by
digest, and removes only the unit and container it made.

```sh
gpu-prover/container/restart-cap.test.sh
```

## Compose

```sh
export SRS_DIR=/path/to/srs SRS_FILE=<srs file name>
docker compose -f gpu-prover/container/compose.yaml up -d prover
# CDI variant, through the start gate (refuses a stale CDI spec):
gpu-prover/container/run-gpu.sh \
  docker compose -f gpu-prover/container/compose.yaml --profile cdi up -d prover-cdi
```

`PROVER_IMAGE`, `PROVER_UID`, `PROVER_GID` and `PROVER_MEMORY_MAX` (default
`32g`) override the defaults.

## systemd (host install)

`midnight-gpu-proverd.service` runs the daemon from
`/usr/local/bin/midnight-gpu-proverd` as the system user `midnight-prover`
(create it first; clients must run as that user or root, because the socket
has mode 0600), with a read-only system, a private `/tmp`, `MemoryMax=32G`
and only `AF_UNIX` sockets. systemd creates the socket directory
(`RuntimeDirectory=midnight-gpu-prover`) and removes it when the unit stops.
Adjust `MemoryMax` to the host and put further settings in
`/etc/default/midnight-gpu-proverd`.

## Published image

Tags `gpu-prover-v<version>` build the image for amd64 and arm64 and push it
to `ghcr.io/<owner>/midnight-gpu-prover:<version>`
(`.github/workflows/gpu-prover-image.yml`). Pull requests that change the GPU
code only build it.

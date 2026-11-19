# syntax=docker/dockerfile:1.28.0@sha256:bb22d9815c728170f72750f4e5b0d672e06176142e1d602c7e66c050100b7e5b

# This file is part of midnight-zk.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Image for the GPU prover daemon (midnight-gpu-proverd).
#
# Build from the repository root:
#   docker buildx build -f gpu-prover/container/Dockerfile -t midnight-gpu-prover .
#
# Reproducibility:
#   * Base images are pinned by multi-arch index digest (amd64 + arm64).
#   * apt reads one dated Ubuntu snapshot, and named packages have exact versions.
#   * rustup-init is pinned by version and SHA-256; the Rust toolchain comes
#     from rust-toolchain.toml.
#   * Crates are fetched once, in the "vendor" stage, with `cargo vendor
#     --locked` from Cargo.lock. The "builder" stage has no network and builds
#     with `--locked --offline` from the vendored sources.
#   * The CUDA build is mandatory (MIDNIGHT_GPU_REQUIRE_CUDA=1): a missing nvcc
#     fails the build instead of producing the CPU stub.

ARG CUDA_DEVEL_IMAGE=docker.io/nvidia/cuda:13.4.3-devel-ubuntu24.04@sha256:5626a7d0ecafe3e7c115a452f6b05f20f214f8509346196a7835b205dc5b7fd9
ARG CUDA_RUNTIME_IMAGE=docker.io/nvidia/cuda:13.4.3-base-ubuntu24.04@sha256:07adb6792c59025f2c45bfb1a3f1d1148bf6d48bf2326d604a6b2e24c4f04d6f

# ---------------------------------------------------------------------------
# toolchain: CUDA devel image + pinned apt packages + pinned Rust toolchain.
# ---------------------------------------------------------------------------
FROM ${CUDA_DEVEL_IMAGE} AS toolchain

ARG UBUNTU_SNAPSHOT=20261116T000000Z
ARG RUSTUP_VERSION=1.29.3
ARG RUSTUP_SHA256_AMD64=b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55
ARG RUSTUP_SHA256_ARM64=9f608c142e0e38a78957d0661ba1dfaf0b6fb37184cfaa4b9a0aa57af6184282
ARG TARGETARCH

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Use only the dated Ubuntu snapshot. The NVIDIA apt repository in the base
# image is not dated, so it is removed; the image already has the CUDA toolkit.
# snapshot.ubuntu.com serves both amd64 and arm64 under /ubuntu.
RUN rm -f /etc/apt/sources.list.d/* /etc/apt/sources.list \
 && printf '%s\n' \
      'Types: deb' \
      "URIs: https://snapshot.ubuntu.com/ubuntu/${UBUNTU_SNAPSHOT}/" \
      'Suites: noble noble-updates noble-security' \
      'Components: main' \
      'Signed-By: /usr/share/keyrings/ubuntu-archive-keyring.gpg' \
      > /etc/apt/sources.list.d/ubuntu-snapshot.sources \
 && apt-get update \
 && apt-get install -y --no-install-recommends \
      build-essential=12.10ubuntu1 \
      ca-certificates=20260816ubuntu0.24.04.2 \
      curl=8.5.0-2ubuntu10.16 \
 && rm -rf /var/lib/apt/lists/*

ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    PATH=/opt/cargo/bin:${PATH}

RUN case "${TARGETARCH}" in \
      amd64) triple=x86_64-unknown-linux-gnu;  sum="${RUSTUP_SHA256_AMD64}" ;; \
      arm64) triple=aarch64-unknown-linux-gnu; sum="${RUSTUP_SHA256_ARM64}" ;; \
      *) echo "unsupported TARGETARCH: ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl --proto '=https' --tlsv1.2 -sSfL -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/${RUSTUP_VERSION}/${triple}/rustup-init" \
 && echo "${sum}  /tmp/rustup-init" | sha256sum -c - \
 && chmod +x /tmp/rustup-init \
 && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain none \
 && rm /tmp/rustup-init

# Install the toolchain named in rust-toolchain.toml (no nvptx64 target: the
# kernels are compiled by nvcc, not by rustc).
WORKDIR /src
COPY rust-toolchain.toml ./
RUN rustup toolchain install && rustc --version && nvcc --version

# ---------------------------------------------------------------------------
# vendor: the only stage that downloads crates. `cargo vendor --locked` reads
# Cargo.lock (registry and git sources) and writes the sources and a cargo
# config that replaces every source with the vendored directory.
# ---------------------------------------------------------------------------
FROM toolchain AS vendor
COPY . /src
RUN mkdir -p /opt/cargo-vendor \
 && cargo vendor --locked --versioned-dirs /opt/cargo-vendor/crates \
      > /opt/cargo-vendor/config.toml

# ---------------------------------------------------------------------------
# builder: offline, locked CUDA build of the daemon.
# ---------------------------------------------------------------------------
FROM toolchain AS builder

# Compute capabilities to compile kernels for, in the format that the
# midnight-gpu build script reads. The default covers Ampere (A100, RTX 30),
# Ada (RTX 40, L4, L40), Hopper (H100, H200), Blackwell data center (B200)
# and Blackwell client and GB10 (RTX 50, DGX Spark).
ARG MIDNIGHT_GPU_ARCHS="sm_80,sm_86,sm_89,sm_90,sm_100,sm_120,sm_121"
ARG CARGO_FEATURES=cuda

ENV MIDNIGHT_GPU_REQUIRE_CUDA=1 \
    MIDNIGHT_GPU_ARCHS=${MIDNIGHT_GPU_ARCHS} \
    CARGO_TARGET_DIR=/src/target

COPY . /src
COPY --from=vendor /opt/cargo-vendor /opt/cargo-vendor

RUN --network=none \
    cargo build --release --locked --offline \
      --config /opt/cargo-vendor/config.toml \
      -p midnight-gpu-prover \
      --bin midnight-gpu-proverd --bin midnight-gpu-prover-client \
      --features "${CARGO_FEATURES}" \
 && install -D -m 0755 -t /out \
      target/release/midnight-gpu-proverd target/release/midnight-gpu-prover-client

# ---------------------------------------------------------------------------
# gpu-test: test-only image with the device test binary of tests/gpu.rs and
# the `seeded_prove` example, built with the `test-seed` feature. Never
# published; check-no-test-seed.sh refuses it. Build it with
#   --target gpu-test --build-arg CARGO_FEATURES="cuda test-seed"
# and run it with a GPU. The test binary (the entrypoint) compares a seeded
# device proof with a seeded CPU proof byte for byte; `seeded_prove OUT_DIR`
# (--entrypoint /usr/local/bin/seeded_prove) writes both proofs and their
# SHA-256, so that they can be compared with a proof made elsewhere.
# ---------------------------------------------------------------------------
FROM builder AS gpu-test-build
ARG CARGO_FEATURES=cuda
RUN --network=none \
    cargo test --release --locked --offline \
      --config /opt/cargo-vendor/config.toml \
      -p midnight-gpu-prover --features "${CARGO_FEATURES}" \
      --test gpu --no-run --message-format=json-render-diagnostics \
      | grep '"kind":\["test"\]' \
      | sed -nE 's/.*"executable":"([^"]+)".*/\1/p' > /tmp/test-bins \
 && test -s /tmp/test-bins \
 && install -D -m 0755 "$(head -1 /tmp/test-bins)" /out/gpu-test \
 && cargo build --release --locked --offline \
      --config /opt/cargo-vendor/config.toml \
      -p midnight-gpu-prover --features "${CARGO_FEATURES}" --example seeded_prove \
 && install -D -m 0755 target/release/examples/seeded_prove /out/seeded_prove

FROM ${CUDA_RUNTIME_IMAGE} AS gpu-test
ARG PROVER_UID=10001
ARG PROVER_GID=10001
COPY --from=gpu-test-build /out/gpu-test /out/seeded_prove /usr/local/bin/
ENV NVIDIA_VISIBLE_DEVICES=all \
    NVIDIA_DRIVER_CAPABILITIES=compute,utility
USER ${PROVER_UID}:${PROVER_GID}
ENTRYPOINT ["/usr/local/bin/gpu-test", "--test-threads=1", "--nocapture"]

# ---------------------------------------------------------------------------
# runtime: CUDA base image (driver libraries come from the host through the
# NVIDIA Container Toolkit or CDI), non-root user, no build tools.
# ---------------------------------------------------------------------------
FROM ${CUDA_RUNTIME_IMAGE} AS runtime

ARG PROVER_UID=10001
ARG PROVER_GID=10001

RUN groupadd --gid "${PROVER_GID}" prover \
 && useradd --no-log-init --uid "${PROVER_UID}" --gid "${PROVER_GID}" \
      --no-create-home --home-dir /nonexistent --shell /usr/sbin/nologin prover \
 && install -d -m 0750 -o "${PROVER_UID}" -g "${PROVER_GID}" /run/midnight-gpu-prover \
 && install -d -m 0755 /srv/midnight/srs

COPY --from=builder /out/midnight-gpu-proverd /out/midnight-gpu-prover-client /usr/local/bin/
COPY --chmod=0755 gpu-prover/container/entrypoint.sh /usr/local/bin/entrypoint.sh
COPY --chmod=0755 gpu-prover/container/healthcheck.sh /usr/local/bin/healthcheck.sh

# SRS: mount the directory that holds the SRS file read-only at
# /srv/midnight/srs and set MIDNIGHT_GPU_PROVER_SRS to the file in it.
# Socket: /run/midnight-gpu-prover/proverd.sock, in a volume so that clients in
# other containers or on the host can reach it.
ENV MIDNIGHT_GPU_PROVER_SOCKET=/run/midnight-gpu-prover/proverd.sock \
    NVIDIA_VISIBLE_DEVICES=all \
    NVIDIA_DRIVER_CAPABILITIES=compute,utility

VOLUME ["/run/midnight-gpu-prover"]

USER ${PROVER_UID}:${PROVER_GID}

HEALTHCHECK --interval=30s --timeout=10s --start-period=120s --retries=3 \
  CMD ["/usr/local/bin/healthcheck.sh"]

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]

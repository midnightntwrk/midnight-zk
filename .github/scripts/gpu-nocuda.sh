#!/usr/bin/env bash
# Run from the workspace root after fetching or vendoring the locked dependencies.
set -euo pipefail

features=()
proof_features=()
case "$1" in
  default) ;;
  gpu)
    features=(--features midnight-proofs/gpu,midnight-gpu/cuda,midnight-gpu-prover/cuda)
    proof_features=(--features gpu)
    ;;
  all)
    features=(--all-features)
    proof_features=(--all-features)
    ;;
  *) echo "Unknown feature set: $1" >&2; exit 2 ;;
esac
gpu_packages=(-p midnight-gpu -p midnight-gpu-prover)
common=(--locked --offline)

case "$2" in
  preflight)
    if command -v nvcc || [[ -n ${CUDA_PATH:-} || -n ${CUDA_HOME:-} ||
        -e /opt/cuda/bin/nvcc || -e /usr/local/cuda/bin/nvcc ]]; then
      echo 'The no-CUDA job requires a runner without a CUDA toolkit.' >&2
      exit 1
    fi
    ;;
  build) cargo build "${common[@]}" --workspace "${features[@]}" ;;
  require-cuda)
    # A device gate that requires CUDA must fail specifically on missing nvcc.
    if output=$(MIDNIGHT_GPU_REQUIRE_CUDA=1 cargo check "${common[@]}" -p midnight-gpu --features cuda 2>&1); then
      echo 'Required CUDA build unexpectedly succeeded.' >&2
      exit 1
    fi
    printf '%s\n' "$output"
    [[ $output == *'nvcc not found'*'(MIDNIGHT_GPU_REQUIRE_CUDA=1)'* ]]
    ;;
  clippy)
    cargo clippy "${common[@]}" --workspace --all-targets "${features[@]}"
    cargo clippy "${common[@]}" "${gpu_packages[@]}" --all-targets "${features[@]}" -- -D warnings
    ;;
  doc)
    RUSTDOCFLAGS='-D warnings' cargo doc "${common[@]}" --no-deps "${gpu_packages[@]}" "${features[@]}"
    ;;
  test)
    # midnight-gpu's test dependency enables gpu-test. Run proofs separately
    # to also exercise proofs with the hooks disabled and with production hooks.
    cargo test "${common[@]}" -p midnight-proofs "${proof_features[@]}"
    # Include this test even if the build unexpectedly compiled the CUDA core.
    # It asserts cuda_built() is false before calling any device API.
    cargo test "${common[@]}" "${gpu_packages[@]}" "${features[@]}" --test stub -- --include-ignored
    cargo test "${common[@]}" "${gpu_packages[@]}" "${features[@]}"
    ;;
  *) echo "Unknown check: $2" >&2; exit 2 ;;
esac

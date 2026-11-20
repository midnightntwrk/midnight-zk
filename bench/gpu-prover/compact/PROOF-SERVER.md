# A GPU proof server for the 0.8 stack

The Midnight proof server 9.0.1 (crate `midnight-proof-server`, midnight-ledger revision
`a2b30128`, tag `proof-server-9.0.1`) proves the contract-call, zswap and dust proofs of a
transaction. Proofs made with midnight-proofs 0.9 do not verify on a ledger that pins 0.8.x,
so a GPU proof server for current networks runs the 0.8 stack with the hooked midnight-proofs
0.8.3, the same build that this benchmark measures.

`proof-server/` is that server: a crate with its own workspace and lock, outside the
repository's workspace. It does not fork the server source.

- It depends on `midnight-proof-server` at revision `a2b30128` and repeats the `[patch]`
  entries of the midnight-ledger workspace (a workspace's own `[patch]` does not apply to a git
  dependency).
- `Cargo.lock` starts from the lock of midnight-ledger at the same revision. It has no crate
  version that the ledger lock does not have; it only leaves out the crates that the server
  does not use.
- `main` installs the hooks of the backend crate (`compact-bench-gpu`, the API of
  `gpu-backend-stub/`) first, logs the device description, and then runs the stock `main`:
  the same flags and environment variables, the same key-material prefetch,
  `WorkerPool::new(...)` and `server(port, fetch_params, pool)`. The HTTP routes, request
  formats and responses do not change, so wallets and the transaction builder use it on the
  same port without a change.
- Built with the `gpu` feature, it refuses to start when the backend installs no hooks, so a
  CPU-only build cannot run under a GPU label.
- The log filter turns off the targets `zkir` and `midnight_zkir` and does not read
  `RUST_LOG`. zkir logs private inputs at error level on malformed-witness paths, and the
  stock server's filter (`zkir` only) does not match the library target `midnight_zkir`
  (see docs/gpu-prover/security.md, section 9).
- The default worker count is 1 (the stock default is 2): two proofs at the same time would
  share one device.
- A background thread logs the hook counters each time they change, for example
  `hooks: msm M ntt N coset C quotient Q fallbacks F (since last line); device peak P B`.
  With one worker this is one line per proof that used the hooks. A proof that does not reach
  the hooks writes no line. The line holds counts only, no request data.

## Build and run

```sh
# Stock (CPU): midnight-proofs from the lock.
scripts/build.sh --proof-server stock
# GPU: the hooked midnight-proofs 0.8.3 and a backend crate, as for compact-bench.
scripts/build.sh --proof-server hooked PROOFS BACKEND

# Same flags and environment variables as the stock server.
MIDNIGHT_PROOF_SERVER_PORT=6300 proof-server/target/hooked/release/gpu-proof-server
```

### Keep the port off the network

Proof requests carry witness data. Proof server 9.0.1 has no bind option: `server()` binds
`0.0.0.0` on the given port, and the wrapper calls it unchanged. The Preview runs therefore
start the server in a network namespace that has only a loopback interface, so the
all-interfaces bind opens no port on the machine. A `socat` in the same namespace bridges a
mode-600 unix socket to the server's port, and the wallet machine reaches the socket through
an SSH tunnel:

```sh
# GPU machine: user and network namespace with loopback only (no root needed).
unshare -rn sh -c 'ip link set lo up &&
  { socat UNIX-LISTEN:$SOCK,fork,mode=600 TCP:127.0.0.1:6300 & } &&
  MIDNIGHT_PROOF_SERVER_PORT=6300 exec proof-server/target/hooked/release/gpu-proof-server'
# Wallet machine: forward a local port to the socket.
ssh -N -L 127.0.0.1:6300:$SOCK gpu-machine
```

The session script refuses to continue if the port answers on any address of the machine
(every address from `ip -o addr` is probed after the socket appears). A systemd
`IPAddressDeny=` setting on the session unit is not enough when the server runs in a
separate transient scope, because the scope does not inherit the unit's IP filter. On the
Preview runs, a probe of the machine's network address on the server port was refused and a
request through the tunnel was answered. The CUDA device stays usable in the namespace: the
server printed its hooks-installed line with the GPU name and proved on the device.

## Which proofs go to the GPU

In proof-server 9.0.1 the ledger links two midnight-proofs versions. Contract calls (ZKIR v3,
`midnight-zkir` 3.2.0 and `midnight-transient-crypto` 3.0.1) prove with midnight-proofs 0.8,
which the hooks cover. The zswap and dust keys come from `midnight-transient-crypto` 2.2.0 on
midnight-proofs 0.7.3 (`ledger/src/dust.rs` and `zswap/src/verify.rs` take their verifier
keys from `transient_crypto_old`). The hooks do not cover 0.7.3, so the wallet's dust-spend
proof and every zswap proof stay on the CPU. A contract deploy carries only a dust-spend
proof, so it has no GPU proof. In a call transaction the contract-call proof runs on the GPU
and the dust spend on the CPU.

Labels for a transaction, from the counter lines of its proofs:

- **GPU-proven**: the contract-call proof has msm > 0, and fallbacks 0.
- **GPU (NTT/coset/quotient on device; MSM on CPU below k=14)**: the call's
  circuit is below k=14, so msm is 0, and the NTT, coset and quotient counts are
  above 0 with fallbacks 0. The MSM hook takes only MSMs of 2^14 terms or more.
- **CPU (0.7.3 dust path)**: a deploy, which has only the dust-spend proof and
  no counter line.

## Checks for each proof

- Every proof that the server makes is verified by the server itself (the `ProofPreimage::prove`
  self-check) before it answers.
- The counter line of each proof shows whether it used the device and whether a hook fell back
  to the CPU.
- On a network, the ledger verifies the proof with the stock verifier when it includes the
  transaction.

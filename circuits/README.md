# Midnight Circuits

[![CI checks](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/ci.yml/badge.svg)](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/ci.yml)
[![Examples](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/examples.yml/badge.svg)](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/examples.yml)
[![Crates.io Version](https://img.shields.io/crates/v/midnight-circuits?label=midnight-circuits)](https://crates.io/crates/midnight-circuits)

*Midnight Circuits* is a library designed for implementing circuits with [Halo2](https://github.com/zcash/halo2). It is built on the [PSE v0.4.0 release](https://github.com/privacy-scaling-explorations/halo2/releases/tag/v0.4.0) of Halo2, incorporating a few [minor additions](https://github.com/midnightntwrk/halo2/commits/dev/) required to support *Midnight Circuits*.

> **Disclaimer**: This library has not been audited. Use it at your own risk.

## Features

*Midnight Circuits* provides several tools to facilitate circuit development with Halo2. These include:

1. Native and non-native field operations.
2. Native and non-native elliptic-curve operations.
3. Native and non-native hash-to-curve functionality.
4. Bit/Byte decomposition tools and range-checks.
5. SHA-256.
6. SHA-512.
7. Set (non-)membership.
8. BigUInt.
9. Variable length vectors (see explanation below).
10. Finite-state automata parsing.
11. In-circuit verification of PLONK proofs (a.k.a. recursion).

We aim to expose these functionalities via traits, which can be found in `[src/instructions]`.

### Variable length vectors

We provide support for variable-length vectors in-circuit, even when the exact size of the vector is unknown 
at compilation time. Each variable-length vector is parameterized with a `MAX_LENGTH` attribute, which 
specifies the maximum allowed size.

The cost of using these structures in-circuit is proportional to the `MAX_LENGTH`, while the computed result
is guaranteed to correspond to the operation applied to the actual vector values. For example, operations
such as hashing or parsing are performed over the full vector of length `MAX_LENGTH`, and the final result
is conditionally selected to reflect the operation applied only to the actual elements of the vector.

## Usage

*Midnight Circuits* provides low-level building blocks for constructing zero-knowledge circuits.
For a higher-level abstraction that simplifies circuit development, see the [`midnight-zk-stdlib`](../zk_stdlib)
crate.

## Versioning

We use [Semantic Versioning](https://semver.org/spec/v2.0.0.html). To capture
the changes that do not affect the API, do not add any new functionality, but
are breaking changes, we increment the `MAJOR` version. This happens when the
circuit is modified for performance or bug fixes; the modification of the
verification keys break backwards compatibility.

* MAJOR: Incremented when you make incompatible API or VK changes
* MINOR: Incremented when you add functionality in a backward-compatible manner
* PATCH: Incremented when you make backward-compatible bug fixes

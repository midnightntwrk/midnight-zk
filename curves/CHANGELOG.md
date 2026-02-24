# Changelog

All notable changes to `curves` will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://book.async.rs/overview/stability-guarantees.html).

## [Unreleased]
### Added
* Add Curve25519 [#181](https://github.com/midnightntwrk/midnight-zk/pull/181)
* Add `k256` module [#189](https://github.com/midnightntwrk/midnight-zk/pull/189), [#191](https://github.com/midnightntwrk/midnight-zk/pull/191)

### Changed
* Change nr of bits to represent JubJub scalar field modulus from 255 -> 252 [#179](https://github.com/midnightntwrk/midnight-zk/pull/179)
* Updated Rust toolchain to 1.90.0 [#210](https://github.com/midnightntwrk/midnight-zk/pull/210)
* Feature-gate `derive::curve` macro and `hash_to_curve` module behind `dev-curves` [#216](https://github.com/midnightntwrk/midnight-zk/pull/216)
* Make `halo2derive` dependency optional, only needed with `dev-curves` [#216](https://github.com/midnightntwrk/midnight-zk/pull/216)

### Removed
* Remove native `secp256k1` module (replaced by `k256`) [#216](https://github.com/midnightntwrk/midnight-zk/pull/216)

## 0.2.0
### Added

### Changed

### Removed
* Removed halo2curves dependency [#139](https://github.com/midnightntwrk/midnight-zk/pull/139)

## 0.1.1
### Added
* Add original Blstrs licenses [#36](https://github.com/midnightntwrk/midnight-zk/pull/36)
* Halo2curves traits [#139](https://github.com/midnightntwrk/midnight-zk/pull/139)
* Halo2curves field and curve derivation macros [#139](https://github.com/midnightntwrk/midnight-zk/pull/139)
* Secp256k1 curve [#139](https://github.com/midnightntwrk/midnight-zk/pull/139)
* Bn256 curve under dev-curves feature [#139](https://github.com/midnightntwrk/midnight-zk/pull/139)
### Changed
* Use native batch normalize [#76](https://github.com/midnightntwrk/midnight-zk/pull/76)
* Address Clippy warnings [#91](https://github.com/midnightntwrk/midnight-zk/pull/91)
### Removed
* Some dbg prints [#59](https://github.com/midnightntwrk/midnight-zk/pull/59)

## 0.1.0
Initial release

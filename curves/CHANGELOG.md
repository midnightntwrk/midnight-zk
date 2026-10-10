# Changelog

All notable changes to `curves` will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://book.async.rs/overview/stability-guarantees.html).

## [Unreleased]
### Added
* `msm::FixedBases`: precomputed `2^(c·w)·P` tables for bases used many times, so all windows share one bucket set; ~100 MB for 2^16 BLS12-381 G1 bases at `c = 16`, grows with the bases and serves any prefix: 0.72-0.87x of `msm_best`'s time at 2^14-2^16 (x86 32 threads, Apple M3 16 threads), 0.66-0.76x single-threaded [#574](https://github.com/midnightntwrk/midnight-zk/pull/574)
* `FieldInto`: field arithmetic written into a destination (blst-style, all methods defaulted); now a bound on `CurveAffine::Base`, so a downstream `CurveAffine` implementation needs `impl FieldInto for <Base> {}` [#573](https://github.com/midnightntwrk/midnight-zk/pull/573)
* `CurveAffine::msm` (the Rust Pippenger; BLS12-381 G1 uses blst under the new `blst-msm` feature), `CurveAffine::from_xy_unchecked` (G1 skips the subgroup check) and `CurveAffine::glv` (BLS12-381 G1's endomorphism) [#573](https://github.com/midnightntwrk/midnight-zk/pull/573)
* Affine MSM path `G1Affine::multi_exp_affine` [#350](https://github.com/midnightntwrk/midnight-zk/pull/350)
* Cached-twiddle FFT (`best_fft_with_twiddles`, `compute_twiddles`) and pruned DIF FFT (`fft_coeff_to_extended`) [#352](https://github.com/midnightntwrk/midnight-zk/pull/352)
* Add Curve25519 [#181](https://github.com/midnightntwrk/midnight-zk/pull/181)
* Add `k256` module [#189](https://github.com/midnightntwrk/midnight-zk/pull/189), [#191](https://github.com/midnightntwrk/midnight-zk/pull/191)

### Changed
* **Breaking:** BLS12-381 G1 `CurveAffine::msm` is the Rust `msm_best`; the new `blst-msm` feature restores blst's `multi_exp_affine` [#573](https://github.com/midnightntwrk/midnight-zk/pull/573)
* `msm_best` is a Pippenger with batched affine buckets (gnark's; XYZZ below window 7) on blst's tiling, with measured per-arch window tables, through the GLV endomorphism for 32..128 terms: 0.6-0.75x of blst's time on BLS12-381 G1 from 2^10 terms on x86, 0.7-0.8x from 2^12 on Apple M3 [#573](https://github.com/midnightntwrk/midnight-zk/pull/573)
* Migrate to Rust edition 2024 (from 2018); declare MSRV 1.90. Both are now inherited from the workspace [#508](https://github.com/midnightntwrk/midnight-zk/pull/508)
*  Moved the generic extension-field tower (`ExtField`, `quadratic`/`cubic`) from `ff_ext` to the dev-curves `bn256` module [#412](https://github.com/midnightntwrk/midnight-zk/pull/412)

### Fixed
* Add prime-order subgroup check in `G1Affine::from_uncompressed` [#425](https://github.com/midnightntwrk/midnight-zk/pull/425)
* `G1Affine::coordinates` skips the subgroup check. [#573](https://github.com/midnightntwrk/midnight-zk/pull/573)

### Removed
* `h_commit` bench [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)
* Removed `serde::{Serialize, Deserialize}` impls and the `serde` feature [#412](https://github.com/midnightntwrk/midnight-zk/pull/412)
* Removed unused public API: `unique_messages`/`PairingG1G2`/`PairingG2G1`, `CurveExt::{endo, jacobian_coordinates, new_jacobian, hash_to_curve}`, `Coordinates::{u, v}`, `hash_to_curve` module (+ BLS inherent `hash_to_curve`), the `__private_bench` feature (`Fp12`/`Fp2`); the unused `halo2curves` dep [#412](https://github.com/midnightntwrk/midnight-zk/pull/412)
*
## 0.3.0
### Added
* Add Curve25519 [#181](https://github.com/midnightntwrk/midnight-zk/pull/181)
* Add `k256` module [#189](https://github.com/midnightntwrk/midnight-zk/pull/189), [#191](https://github.com/midnightntwrk/midnight-zk/pull/191)
* Update READMEs and add badges [#261](https://github.com/midnightntwrk/midnight-zk/pull/261)
* Add `p256` module [#269](https://github.com/midnightntwrk/midnight-zk/pull/269)

### Changed
* Change nr of bits to represent JubJub scalar field modulus from 255 -> 252 [#179](https://github.com/midnightntwrk/midnight-zk/pull/179)
* Updated Rust toolchain to 1.90.0 [#210](https://github.com/midnightntwrk/midnight-zk/pull/210)
* Feature-gate `derive::curve` macro and `hash_to_curve` module behind `dev-curves` [#216](https://github.com/midnightntwrk/midnight-zk/pull/216)
* Make `halo2derive` dependency optional, only needed with `dev-curves` [#216](https://github.com/midnightntwrk/midnight-zk/pull/216)
* Fix MSM identity handling [#225](https://github.com/midnightntwrk/midnight-zk/pull/225)

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

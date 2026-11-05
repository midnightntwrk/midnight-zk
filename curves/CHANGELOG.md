# Changelog

All notable changes to `curves` will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://book.async.rs/overview/stability-guarantees.html).

## [Unreleased]
### Added
* `FieldInto`: field arithmetic written into a destination (blst-style); every method has a default, and BLS12-381 `Fp` overrides them with direct blst calls [#594](https://github.com/midnightntwrk/midnight-zk/pull/594)
* `CurveAffine::glv`, a curve's GLV endomorphism (provided for BLS12-381 G1) [#TBD](https://github.com/midnightntwrk/midnight-zk/pull/TBD)
* `CurveAffine::from_xy_unchecked`, a point from coordinates the caller vouches for (BLS12-381 G1 skips the subgroup check), and the hidden `CurveAffine::xy_ref`, which lets an MSM read a base's coordinates in place [#594](https://github.com/midnightntwrk/midnight-zk/pull/594)
* Cached-twiddle FFT (`best_fft_with_twiddles`, `compute_twiddles`) and pruned DIF FFT (`fft_coeff_to_extended`) [#352](https://github.com/midnightntwrk/midnight-zk/pull/352)
* Add Curve25519 [#181](https://github.com/midnightntwrk/midnight-zk/pull/181)
* Add `k256` module [#189](https://github.com/midnightntwrk/midnight-zk/pull/189), [#191](https://github.com/midnightntwrk/midnight-zk/pull/191)

### Changed
* BREAKING: `CurveAffine::Base` requires `FieldInto`. A downstream `CurveAffine` implementation needs `impl FieldInto for <Base> {}` [#594](https://github.com/midnightntwrk/midnight-zk/pull/594)
* `msm::msm_best` is a Pippenger over blst-style tiles of windows × chunks of the terms, with batched affine buckets (gnark's) from window 7 and XYZZ buckets below, and per-arch window tables (x86-64, aarch64); through the GLV endomorphism for 32..128 terms, and one scalar multiplication per term below 32; a sparse input (more zero scalars than non-zero) is compacted first. It is now the MSM of every curve, BLS12-381 G1 included (the results are the same group elements) [#TBD](https://github.com/midnightntwrk/midnight-zk/pull/TBD)
* BLS12-381 `Fp` overrides `is_zero_vartime` (an OR of the limbs) and inlines `is_zero`, `square` and `double` [#594](https://github.com/midnightntwrk/midnight-zk/pull/594)
* Migrate to Rust edition 2024 (from 2018); declare MSRV 1.90. Both are now inherited from the workspace [#508](https://github.com/midnightntwrk/midnight-zk/pull/508)
*  Moved the generic extension-field tower (`ExtField`, `quadratic`/`cubic`) from `ff_ext` to the dev-curves `bn256` module [#412](https://github.com/midnightntwrk/midnight-zk/pull/412)

### Fixed
* `msm` bench: one generator per rayon job made 98% of its points and scalars repeats; each item is now seeded on its own [#594](https://github.com/midnightntwrk/midnight-zk/pull/594)
* Add prime-order subgroup check in `G1Affine::from_uncompressed` [#425](https://github.com/midnightntwrk/midnight-zk/pull/425)
* `G1Affine::coordinates` skips the subgroup check. [#544](https://github.com/midnightntwrk/midnight-zk/pull/544)

### Removed
* BREAKING: `msm::msm_serial` and `msm::msm_parallel`: every MSM goes through `msm::msm_best` (`G1Affine::multi_exp_affine`, unreleased, is gone too) [#TBD](https://github.com/midnightntwrk/midnight-zk/pull/TBD)
* BREAKING: `G1Projective::multi_exp` and `G2Projective::multi_exp`, the blst MSM wrappers; the tests and benches that need blst's MSM call it directly [#TBD](https://github.com/midnightntwrk/midnight-zk/pull/TBD)
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

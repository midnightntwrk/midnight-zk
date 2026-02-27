# Changelog

We use [Semantic Versioning](https://semver.org/spec/v2.0.0.html). To capture
the changes that do not affect the API, do not add any new functionality, but
are breaking changes, we increment the `MAJOR` version. This happens when the
circuit is modified for performance or bug fixes; the modification of the
verification keys break backwards compatibility.

* MAJOR: Incremented when you make incompatible API or VK changes
* MINOR: Incremented when you add functionality in a backward-compatible manner
* PATCH: Incremented when you make backward-compatible bug fixes

## [Unreleased]
### Added
* Added an example verifying an ethereum signature [#177](https://github.com/midnightntwrk/midnight-zk/pull/177)
* Adds identity related examples to evaluate the impact of substring checks + bug patch for the example it is compared against [#229](https://github.com/midnightntwrk/midnight-zk/pull/229)

### Changed
* Update IVC example to use improved verifier gadget [#212](https://github.com/midnightntwrk/midnight-zk/pull/212)
* Change nr of bits to represent JubJub scalar field modulus from 255 -> 252 [#179](https://github.com/midnightntwrk/midnight-zk/pull/179)
* Adapt external hash tests to hash instructions interface [#162](https://github.com/midnightntwrk/midnight-zk/pull/162)
* Updated Rust toolchain to 1.90.0 [#210](https://github.com/midnightntwrk/midnight-zk/pull/210)
* `CircuitField` refactor  [#201](https://github.com/midnightntwrk/midnight-zk/pull/201)
* Replace `secp256k1` with `k256`  [#192](https://github.com/midnightntwrk/midnight-zk/pull/192)

### Removed
* Move Blake2b and SHA3-256/Keccak256 implementations to zk-stdlib [#178](https://github.com/midnightntwrk/midnight-zk/pull/178)

## 1.0.0
### Added
- Initial release of zk_stdlib extracted from circuits crate

### Changed

### Removed

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

### Changed

### Removed

## [1.3.0]
### Fixed
* Bump `midnight-circuits` to 6.3.0 and `midnight-proofs` to 0.7.3, pulling in the `padding_flag` soundness fix. This changes the verification key of circuits that use vector or base64 gadgets. [#481](https://github.com/midnightntwrk/midnight-zk/pull/481)

## [1.2.1]
### Fixed
* Bug fix in midnight-curves [#433](https://github.com/midnightntwrk/midnight-zk/pull/433)

## [1.2.0]
### Added
* `Instantiable::from_public_input`: inverse of `as_public_input` for decoding values from their public input representation [#407](https://github.com/midnightntwrk/midnight-zk/pull/407)

## [1.1.0]
### Changed
* Update `prove` to accept `impl RngCore + CryptoRng` by value [#307](https://github.com/midnightntwrk/midnight-zk/pull/307)

## [1.0.0] 
### Added
- Initial release of zk_stdlib extracted from circuits crate

### Changed

### Removed

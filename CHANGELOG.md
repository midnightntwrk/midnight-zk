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
* SageMath script for generating hash to Jubjub params [#452](https://github.com/input-output-hk/midnight-circuits/pull/452)
* Suite for Hash to twisted Edwards curves [#419](https://github.com/input-output-hk/midnight-circuits/pull/419)
* Edwards ECC chip [#419](https://github.com/input-output-hk/midnight-circuits/pull/419)
* Public input interface [#404](https://github.com/input-output-hk/midnight-circuits/pull/404),
  [#408](https://github.com/input-output-hk/midnight-circuits/pull/408)
  [#410](https://github.com/input-output-hk/midnight-circuits/pull/410)
* Set membership/non-membership proof [#403](https://github.com/input-output-hk/midnight-circuits/pull/403)[#413](https://github.com/input-output-hk/midnight-circuits/pull/413)
* Hardcoded VKs for checking circuit breaking changes [#407](https://github.com/input-output-hk/midnight-circuits/pull/407)
* add `square` and `pow` (by constants) to `ArithmeticInstructions` with blanket implementations [#411](https://github.com/input-output-hk/midnight-circuits/pull/411).
* implement `PartialEq`, `Eq` and `Hash` for assigned types.
* Self-emulation params for Blstrs
* Introduce `msm_by_bounded_scalars` [#418](https://github.com/input-output-hk/midnight-circuits/pull/418).
* Emulation params for Pluto over BLS12-381 [#424](https://github.com/input-output-hk/midnight-circuits/pull/424).
* Emulation params for Secp over blstrs [#428](https://github.com/input-output-hk/midnight-circuits/pull/428)
* Moved poseidon from halo2 to midnight-circuits [#428](https://github.com/input-output-hk/midnight-circuits/pull/428)
* JSON verification example [#436](https://github.com/input-output-hk/midnight-circuits/pull/436).
* Added poseidon interface and implemented it for SHA [#438](https://github.com/input-output-hk/midnight-circuits/pull/438)
* Examples are now run with Filecoin's SRS [#444](https://github.com/input-output-hk/midnight-circuits/pull/444)
* Base64 encoded JSON verification example [#450](https://github.com/input-output-hk/midnight-circuits/pull/450).
* Check static VKs on PRs [#451](https://github.com/input-output-hk/midnight-circuits/pull/451)
* BigUintGadget (for RSA) [#453](https://github.com/input-output-hk/midnight-circuits/pull/453)
* Checkmarkx to CI [#457](https://github.com/input-output-hk/midnight-circuits/pull/457)
* Commit "assets" directory via .gitignore [#465](https://github.com/input-output-hk/midnight-circuits/pull/465)
* ecc/mul_by_constant [#469](https://github.com/input-output-hk/midnight-circuits/pull/469)
* Secp256k1 to compact_std_lib [#475](https://github.com/input-output-hk/midnight-circuits/pull/475)

### Changed
* Generalize typesystem of HTC over EccInstructions [#406](https://github.com/input-output-hk/midnight-circuits/pull/406)
* Foreign-field MSM now supports identity points as bases [#414](https://github.com/input-output-hk/midnight-circuits/pull/414)
* Optimize foreign-field MSMs (compare scalars to fixed-one) [#416](https://github.com/input-output-hk/midnight-circuits/pull/416)
* Minor change on debug_assert [#417](https://github.com/input-output-hk/midnight-circuits/pull/417)
* Fix issue on order of cached bases and scalars in foreign MSM [#422](https://github.com/input-output-hk/midnight-circuits/pull/422)
* Added a lint for unused assigned variables [#425](https://github.com/input-output-hk/midnight-circuits/pull/425)
* Midnight lib now can only be called with an inner Edwards curve [#428](https://github.com/input-output-hk/midnight-circuits/pull/428)
* Examples run with BLS12-381 curve [#428](https://github.com/input-output-hk/midnight-circuits/pull/428)
* Hash interface changes (takes and returns assigned bytes) [#431](https://github.com/input-output-hk/midnight-circuits/pull/431)
* New PoseidonGadget implementing the recently added SpongeInstructions and HashInstructions [#440](https://github.com/input-output-hk/midnight-circuits/pull/440)
* Visibility of circuit operation add_and_mul
* Refactor HTC, it is now generic w.r.t. the ecc chip and the hashing chip (this includes non-native EC and any hashing beyond Poseidon) [#435](https://github.com/input-output-hk/midnight-circuits/pull/435)
* Jubjub was hard-coded in midnight_lib [#442](https://github.com/input-output-hk/midnight-circuits/pull/442)
* Refactor CircuitLib (include Witness and Instance) [#443](https://github.com/input-output-hk/midnight-circuits/pull/443)
* Exports of the library, and naming of the std_lib [#446](https://github.com/input-output-hk/midnight-circuits/pull/446)
* Rename EccPoint -> AssignedNativePoint + pass on Edwards Chip.
* Remove CurveAffine from EC operations. [#456](https://github.com/input-output-hk/midnight-circuits/pull/456)
* Bound for `BoundedElement` changed to `F::NUM_BITS - 2` [#454](https://github.com/input-output-hk/midnight-circuits/pull/454)
* Ensure that assigned points are part of the JubJub subgroup [#458](https://github.com/input-output-hk/midnight-circuits/pull/458)
* Extend `BigUintGadget`, implement most traits [#463](https://github.com/input-output-hk/midnight-circuits/pull/463)
* Fixed multi-thread issues with goldenfiles [#473](https://github.com/input-output-hk/midnight-circuits/pull/473)

### Removed
* Existing ECC chip [#428](https://github.com/input-output-hk/midnight-circuits/pull/428)
* Existing Hash to curve [#428](https://github.com/input-output-hk/midnight-circuits/pull/428)
* Support for Pleris [#462](https://github.com/input-output-hk/midnight-circuits/pull/462)
* Batching of PI in FieldChip [#474](https://github.com/input-output-hk/midnight-circuits/pull/474)

## [1.0.0] - 13-08-2024

First release of the library

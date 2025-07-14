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
* Add Url-Safe Base64 support [#540](https://github.com/midnightntwrk/midnight-circuits/pull/540)
* verifier: TranscriptGadget [#545](https://github.com/midnightntwrk/midnight-circuits/pull/545)
* verifier: MSMs & Acc module [#550](https://github.com/midnightntwrk/midnight-circuits/pull/550)
* verifier: KZG multiopen module [#552](https://github.com/midnightntwrk/midnight-circuits/pull/552)
* Add Base64Instructions trait [#556](https://github.com/midnightntwrk/midnight-circuits/pull/556)
* verifier: permutation & lookup & vanishing modules [#554](https://github.com/midnightntwrk/midnight-circuits/pull/554)
* verifier: Verifier Gadget [#558](https://github.com/midnightntwrk/midnight-circuits/pull/558)
* Adds automaton-based parsing circuit [#547](https://github.com/midnightntwrk/midnight-circuits/pull/547)
* Add VectorInstructions, Base64VarInstructions and Vectorizable traits [#568](https://github.com/input-output-hk/midnight-circuits/pull/568)
* IVC example [#564](https://github.com/midnightntwrk/midnight-circuits/pull/564)
* Instance commitments [#572](https://github.com/midnightntwrk/midnight-circuits/pull/572)
* Adds support for multiple hard-coded automata in a single configurated circuit [#569](https://github.com/midnightntwrk/midnight-circuits/pull/569)
* EqualityInstructions & AssertionInstructions implementation for AssignedVectors [#574](https://github.com/midnightntwrk/midnight-circuits/pull/574)
* DivisionInstructions [#574](https://github.com/midnightntwrk/midnight-circuits/pull/574)
* Add Base64Vec intialization instruction + fix alignment bug [#20](https://github.com/midnightntwrk/midnight-zk/pull/20)
* Add a deserialisation function that does not need to know the relation [#18](https://github.com/midnightntwrk/midnight-zk/pull/18/commits/973467fecd6c31c6b57d06c89dfa0c7dd00bef2b)
* Add `trim_beginning` in `VectorInstructions` [#19](https://github.com/midnightntwrk/midnight-zk/pull/19)
* Expose `VectorInstructions in `ZkstdLib` [#19](https://github.com/midnightntwrk/midnight-zk/pull/19)
* Extra functions in `verifier` for the light aggregator [#25](https://github.com/midnightntwrk/midnight-zk/pull/25)
* Add `VectorGadget` [#28](https://github.com/midnightntwrk/midnight-zk/pull/28)

### Changed
* Add holder key check on credential example [#542](https://github.com/midnightntwrk/midnight-circuits/pull/542)
* Normalize after various foreign field ops if bound limit is close [#546](https://github.com/midnightntwrk/midnight-circuits/pull/546)
* Fix optimized `assign_many` from `NativeChip` [#551](https://github.com/midnightntwrk/midnight-circuits/pull/551)
* Fix issue on Base64Chip raised by zkSecurity [#549](https://github.com/midnightntwrk/midnight-circuits/pull/549)
* Representation of VK - we now add a version to the serialisation. This is a breaking change [#562](https://github.com/midnightntwrk/midnight-circuits/pull/562)
* verifier: verifier gadget handles h commitments as in the good old days (with the homomorphic property) [#565](https://github.com/midnightntwrk/midnight-circuits/pull/565)
* Optimize `assign_many` for `AssignedBit` and `AssignedByte` in `NativeGadget` [#561](https://github.com/midnightntwrk/midnight-circuits/pull/561)
* Improve readability and efficiency of Poseidon after audit's remarks [#557](https://github.com/midnightntwrk/midnight-circuits/pull/557)
* Change PoseidonChip dependency (from NativeGadget to NativeChip) [#12](https://github.com/midnightntwrk/midnight-zk/pull/12)
* ZkStdLib API is not generic on the hash function for Fiat-Shamir [#13](https://github.com/midnightntwrk/midnight-zk/pull/13)
* Fix minor issue with is_id flag in Fiat-Shamir with foreign points [#15](https://github.com/midnightntwrk/midnight-zk/pull/15)
* Generalized VerifierGadget with a new `SelfEmulation` trait [#24](https://github.com/midnightntwrk/midnight-zk/pull/24)
* Fixed completeness bug in NativeGadget's `sgn0` [#26](https://github.com/midnightntwrk/midnight-zk/pull/26)
* Optimize `sgn0` [#27](https://github.com/midnightntwrk/midnight-zk/pull/27)

### Removed
* Bit and Byte off-circuit types [#548](https://github.com/midnightntwrk/midnight-circuits/pull/548)

## [3.0.0] - 06-03-2025

### Added
* SageMath script for `field_to_weierstrass` and drawing the distribution of points as outputs of map_to_jubjub [#490](https://github.com/midnightntwrk/midnight-circuits/pull/490)
* Export halo2curves and halo2_proofs [#492](https://github.com/midnightntwrk/midnight-circuits/pull/492)
* Introduce `SRS_DIR` env variable [#487](https://github.com/midnightntwrk/midnight-circuits/pull/487)
* Midnight keys types (with read and write functions) [#499](https://github.com/midnightntwrk/midnight-circuits/pull/499)
* ParserGadget [#501](https://github.com/midnightntwrk/midnight-circuits/pull/501)
* Various emulation params for BN254 [#504](https://github.com/midnightntwrk/midnight-circuits/pull/504)
* Data type operations for ParserGadget [#503](https://github.com/midnightntwrk/midnight-circuits/pull/503)
* Zswap-output example [#505](https://github.com/midnightntwrk/midnight-circuits/pull/505)
* Add new function `downsize_srs_for_relation` [#514](https://github.com/midnightntwrk/midnight-circuits/pull/514)
* Support for more date formats in ParserGadget [#511](https://github.com/midnightntwrk/midnight-circuits/pull/511)
* Add Base64Chip and ParserGadget to ZkStdLib [#513](https://github.com/midnightntwrk/midnight-circuits/pull/513)
* Implement `WeierstrassCurve` for BN254 [#523](https://github.com/midnightntwrk/midnight-circuits/pull/523)
* New implementation of Poseidon (introduced in [#498](https://github.com/midnightntwrk/midnight-circuits/pull/498), now replacing the previous one) [#521](https://github.com/midnightntwrk/midnight-circuits/pull/521)
* `cargo bench` now runs Poseidon's cpu benchmarks
* Introduce `add_constants` [#527](https://github.com/midnightntwrk/midnight-circuits/pull/527)
* Expose `ControlFlowInstructions` in compact_std_lib [#537](https://github.com/midnightntwrk/midnight-circuits/pull/537)

### Changed
* Fix issues raised on `sha256/table16` by zkSecurity [#522](https://github.com/midnightntwrk/midnight-circuits/pull/522)
* Fix issues raised on `sha256/table11` by zkSecurity [#508](https://github.com/midnightntwrk/midnight-circuits/pull/508)
* Make `fe_to_le_bits` variable length (optimization) [#485](https://github.com/midnightntwrk/midnight-circuits/pull/485)
* Configurable ZkStdLib [#488](https://github.com/midnightntwrk/midnight-circuits/pull/488)
* Fix issues raised on FFA by zkSecurity [#489](https://github.com/midnightntwrk/midnight-circuits/pull/489)
* Optimize `sgn0` for native gadget [#491](https://github.com/midnightntwrk/midnight-circuits/pull/491)
* CompactStdLib api (change verify_proof output type)
* Add explicit randomness to `prove` in compact_std_lib [#496](https://github.com/midnightntwrk/midnight-circuits/pull/496)
* Add self to `k` and `used_gadgets` of `Relation` [#496](https://github.com/midnightntwrk/midnight-circuits/pull/496)
* Change `hash_to_curve` input type to slice [#496](https://github.com/midnightntwrk/midnight-circuits/pull/496)
* Change input type of `verify` and `batch_verify` to take `ParamsVerifierKZG` instead of `ParamsKZG` [#497](https://github.com/midnightntwrk/midnight-circuits/pull/497)
* Serialize `Relation` in prover keys [#500](https://github.com/midnightntwrk/midnight-circuits/pull/500)
* Fix issue with number of PIs (verification now fails if the number of PIs differs from the one declared during "synthesize") [#506](https://github.com/midnightntwrk/midnight-circuits/pull/506)
* Update `check_vk` to account for the whole `MidnightVK` and not just its halo2 component [#507](https://github.com/midnightntwrk/midnight-circuits/pull/507)
* Add warning on `assign_as_public_input` [#515](https://github.com/midnightntwrk/midnight-circuits/pull/515)
* Change to the new Halo2 version ([#502](https://github.com/midnightntwrk/midnight-circuits/pull/502), [516](https://github.com/midnightntwrk/midnight-circuits/pull/516), [517](https://github.com/midnightntwrk/midnight-circuits/pull/517))
* The check on consistent VKs is now run with `cargo test` [#509](https://github.com/midnightntwrk/midnight-circuits/pull/509)
* Made proof generation return Result instead of panic if generations fails [#525](https://github.com/midnightntwrk/midnight-circuits/pull/525)
* Poseidon upgraded to 60 rounds, and S-boxes a different input cell during partial rounds [#521](https://github.com/midnightntwrk/midnight-circuits/pull/521), [#526](https://github.com/midnightntwrk/midnight-circuits/pull/526)
* Add property checks in Atala credential example [#518](https://github.com/midnightntwrk/midnight-circuits/pull/518)
* Remove big_machine examples [#527](https://github.com/midnightntwrk/midnight-circuits/pull/527)
* Optimize jubjub addition and doubling [#529](https://github.com/midnightntwrk/midnight-circuits/pull/529)
* Remove `AssignedBoundedBigUint` [#536](https://github.com/midnightntwrk/midnight-circuits/pull/536)
* Update Checkmark yaml [#535](https://github.com/midnightntwrk/midnight-circuits/pull/535)
* Add AssignedVector type [#531](https://github.com/midnightntwrk/midnight-circuits/pull/531)
* Add variable-length hashing in PoseidonChip [#531](https://github.com/midnightntwrk/midnight-circuits/pull/531)


### Removed
* Remove Spoonge instructions for SHA [#528](https://github.com/midnightntwrk/midnight-circuits/pull/528)

## [2.0.0] - 18-11-2024

### Added
* SageMath script for generating hash to Jubjub params [#452](https://github.com/midnightntwrk/midnight-circuits/pull/452)
* Suite for Hash to twisted Edwards curves [#419](https://github.com/midnightntwrk/midnight-circuits/pull/419)
* Edwards ECC chip [#419](https://github.com/midnightntwrk/midnight-circuits/pull/419)
* Public input interface [#404](https://github.com/midnightntwrk/midnight-circuits/pull/404),
  [#408](https://github.com/midnightntwrk/midnight-circuits/pull/408)
  [#410](https://github.com/midnightntwrk/midnight-circuits/pull/410)
* Set membership/non-membership proof [#403](https://github.com/midnightntwrk/midnight-circuits/pull/403)[#413](https://github.com/midnightntwrk/midnight-circuits/pull/413)
* Hardcoded VKs for checking circuit breaking changes [#407](https://github.com/midnightntwrk/midnight-circuits/pull/407)
* add `square` and `pow` (by constants) to `ArithmeticInstructions` with blanket implementations [#411](https://github.com/midnightntwrk/midnight-circuits/pull/411).
* implement `PartialEq`, `Eq` and `Hash` for assigned types.
* Self-emulation params for Blstrs
* Introduce `msm_by_bounded_scalars` [#418](https://github.com/midnightntwrk/midnight-circuits/pull/418).
* Emulation params for Pluto over BLS12-381 [#424](https://github.com/midnightntwrk/midnight-circuits/pull/424).
* Emulation params for Secp over blstrs [#428](https://github.com/midnightntwrk/midnight-circuits/pull/428)
* Moved poseidon from halo2 to midnight-circuits [#428](https://github.com/midnightntwrk/midnight-circuits/pull/428)
* JSON verification example [#436](https://github.com/midnightntwrk/midnight-circuits/pull/436).
* Added poseidon interface and implemented it for SHA [#438](https://github.com/midnightntwrk/midnight-circuits/pull/438)
* Examples are now run with Filecoin's SRS [#444](https://github.com/midnightntwrk/midnight-circuits/pull/444)
* Base64 encoded JSON verification example [#450](https://github.com/midnightntwrk/midnight-circuits/pull/450).
* Check static VKs on PRs [#451](https://github.com/midnightntwrk/midnight-circuits/pull/451)
* BigUintGadget (for RSA) [#453](https://github.com/midnightntwrk/midnight-circuits/pull/453)
* Checkmarkx to CI [#457](https://github.com/midnightntwrk/midnight-circuits/pull/457)
* Add map gadget to ZkStdLib [#460](https://github.com/midnightntwrk/midnight-circuits/pull/460)
* Commit "assets" directory via .gitignore [#465](https://github.com/midnightntwrk/midnight-circuits/pull/465)
* ecc/mul_by_constant [#469](https://github.com/midnightntwrk/midnight-circuits/pull/469)
* Secp256k1 to compact_std_lib [#475](https://github.com/midnightntwrk/midnight-circuits/pull/475)
* Implement PublicInputInstructions for ScalarVar [#477](https://github.com/midnightntwrk/midnight-circuits/pull/477)
* Generic tests for PublicInputInstructions [#481](https://github.com/midnightntwrk/midnight-circuits/pull/481)

### Changed
* Generalize typesystem of HTC over EccInstructions [#406](https://github.com/midnightntwrk/midnight-circuits/pull/406)
* Foreign-field MSM now supports identity points as bases [#414](https://github.com/midnightntwrk/midnight-circuits/pull/414)
* Optimize foreign-field MSMs (compare scalars to fixed-one) [#416](https://github.com/midnightntwrk/midnight-circuits/pull/416)
* Minor change on debug_assert [#417](https://github.com/midnightntwrk/midnight-circuits/pull/417)
* Fix issue on order of cached bases and scalars in foreign MSM [#422](https://github.com/midnightntwrk/midnight-circuits/pull/422)
* Added a lint for unused assigned variables [#425](https://github.com/midnightntwrk/midnight-circuits/pull/425)
* Midnight lib now can only be called with an inner Edwards curve [#428](https://github.com/midnightntwrk/midnight-circuits/pull/428)
* Examples run with BLS12-381 curve [#428](https://github.com/midnightntwrk/midnight-circuits/pull/428)
* Hash interface changes (takes and returns assigned bytes) [#431](https://github.com/midnightntwrk/midnight-circuits/pull/431)
* New PoseidonGadget implementing the recently added SpongeInstructions and HashInstructions [#440](https://github.com/midnightntwrk/midnight-circuits/pull/440)
* Visibility of circuit operation add_and_mul
* Refactor HTC, it is now generic w.r.t. the ecc chip and the hashing chip (this includes non-native EC and any hashing beyond Poseidon) [#435](https://github.com/midnightntwrk/midnight-circuits/pull/435)
* Jubjub was hard-coded in midnight_lib [#442](https://github.com/midnightntwrk/midnight-circuits/pull/442)
* Refactor CircuitLib (include Witness and Instance) [#443](https://github.com/midnightntwrk/midnight-circuits/pull/443)
* Exports of the library, and naming of the std_lib [#446](https://github.com/midnightntwrk/midnight-circuits/pull/446)
* Rename EccPoint -> AssignedNativePoint + pass on Edwards Chip.
* Remove CurveAffine from EC operations. [#456](https://github.com/midnightntwrk/midnight-circuits/pull/456)
* Bound for `BoundedElement` changed to `F::NUM_BITS - 2` [#454](https://github.com/midnightntwrk/midnight-circuits/pull/454)
* Ensure that assigned points are part of the JubJub subgroup [#458](https://github.com/midnightntwrk/midnight-circuits/pull/458)
* Extend `BigUintGadget`, implement most traits [#463](https://github.com/midnightntwrk/midnight-circuits/pull/463)
* Fixed multi-thread issues with goldenfiles [#473](https://github.com/midnightntwrk/midnight-circuits/pull/473)
* Bumped blstrs and halo2 dependencies [#472](https://github.com/midnightntwrk/midnight-circuits/pull/472)
* Do not use FromScratch in doc tests [#478](https://github.com/midnightntwrk/midnight-circuits/pull/478)
* Simplify Pow2Range configure [#479](https://github.com/midnightntwrk/midnight-circuits/pull/479)
* Implement ControlFlowInstructions for AssignedByte [#493](https://github.com/midnightntwrk/midnight-circuits/pull/493)
* Add Base64 Chip [#493](https://github.com/midnightntwrk/midnight-circuits/pull/493)

### Removed
* Existing ECC chip [#428](https://github.com/midnightntwrk/midnight-circuits/pull/428)
* Existing Hash to curve [#428](https://github.com/midnightntwrk/midnight-circuits/pull/428)
* Support for Pleris [#462](https://github.com/midnightntwrk/midnight-circuits/pull/462)
* Batching of PI in FieldChip [#474](https://github.com/midnightntwrk/midnight-circuits/pull/474)

## [1.0.0] - 13-08-2024

First release of the library

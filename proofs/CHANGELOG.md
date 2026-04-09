# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
* changed `sha256` name in benches to account for the change of naming convention in `circuits` [#135](https://github.com/midnightntwrk/midnight-zk/pull/135)
* optional names on VerifierQuery commitments [#205](https://github.com/midnightntwrk/midnight-zk/pull/205)
* `padded_add` and `padded_sub` polynomial operations [#276](https://github.com/midnightntwrk/midnight-zk/pull/276)
* `single-h-commitment` feature to commit the quotient polynomial in one piece [#276](https://github.com/midnightntwrk/midnight-zk/pull/276)
* `fewer-point-sets` feature to reduce the number of distinct multi-open point sets [#281](https://github.com/midnightntwrk/midnight-zk/pull/281)

### Fixed
* Fix broken intra-doc links to private `Polynomial::padded_add` and `padded_sub` [#287](https://github.com/midnightntwrk/midnight-zk/pull/287)
* Fix cost model to account for committed instance column evaluations [#280](https://github.com/midnightntwrk/midnight-zk/pull/280)
* Increase number of blinding factors to account for logup helper polynomials [#312](https://github.com/midnightntwrk/midnight-zk/pull/312)
* Blind logup multiplicities polynomial on non-usable rows for ZK [#312](https://github.com/midnightntwrk/midnight-zk/pull/312)

### Changed
* Split linearization polynomial into homogeneous and affine parts, removing the generator point from the MSM and `constant_commitment` from the PCS trait [#313](https://github.com/midnightntwrk/midnight-zk/pull/313)
* Remove unnecessary polynomial padding in KZG multi-open [#276](https://github.com/midnightntwrk/midnight-zk/pull/276)
* Sort point sets deterministically in KZG multiopen for in-circuit verification [#256](https://github.com/midnightntwrk/midnight-zk/pull/256)
* Move advice queries before instance queries in prover and verifier [#256](https://github.com/midnightntwrk/midnight-zk/pull/256)
* `Circuit::Params` extended to carry `max_bit_len` [#251](https://github.com/midnightntwrk/midnight-zk/pull/251)
* Collapse MSMs during `multi_prepare` to match in-circuit verifier [#227](https://github.com/midnightntwrk/midnight-zk/pull/227)
* Improve MSM handling for fixed bases [#212](https://github.com/midnightntwrk/midnight-zk/pull/212)
* Filtered 0s from MSM [#185](https://github.com/midnightntwrk/midnight-zk/pull/185).
* Updated Rust toolchain to 1.90.0 [#210](https://github.com/midnightntwrk/midnight-zk/pull/210)
* Changed lookup argument to logup [#153](https://github.com/midnightntwrk/midnight-zk/pull/153)
* Implemented linearization prover [#190](https://github.com/midnightntwrk/midnight-zk/pull/190)
* Changed logup to use the selector variant [#220](https://github.com/midnightntwrk/midnight-zk/pull/220)
* Share the `z` and `m` polynomials across all logup instances [#279](https://github.com/midnightntwrk/midnight-zk/pull/279)

### Removed

## [0.7.0]
### Added
* changed `sha256` name in benches to account for the change of naming convention in `circuits` [#135](https://github.com/midnightntwrk/midnight-zk/pull/135)

### Changed
* Interface of `ParamsKZG::from_parts` 

### Removed

## 0.6.0
### Added
* Added a conversion to any AssignedCell to AssignedNative for external crates [#148](https://github.com/midnightntwrk/midnight-zk/pull/148)
* Blind limbs of quotient polynomial and ensure ZK [#161](https://github.com/midnightntwrk/midnight-zk/pull/161)

### Changed
* Address feedback from ZK Sec audit 3 [#125](https://github.com/midnightntwrk/midnight-zk/pull/125)
* Output type of `format_instances` is now wrapped in a `Result` [#120](https://github.com/midnightntwrk/midnight-zk/pull/120).
* Made bench_macros and criterion dev dependencies [#134](https://github.com/midnightntwrk/midnight-zk/pull/134)
* Cost model properly accounts for PIs and fix trash argument [#154](https://github.com/midnightntwrk/midnight-zk/pull/154)
* Halo2curves dependency removed and all tests moved to Bls12-381 [#139](https://github.com/midnightntwrk/midnight-zk/pull/139)

### Removed
* Remove module `model` [#142](https://github.com/midnightntwrk/midnight-zk/pull/142) and feature `cost-estimator`

## 0.5.1
### Added

### Changed
* Fix computation of min_k (due to an extra unusable row we were not accounting for) [#114](https://github.com/midnightntwrk/midnight-zk/pull/114)

### Removed

## 0.5.0
### Added
* Implement `From<u64>` for Expression [#39](https://github.com/midnightntwrk/midnight-zk/pull/39)
* Feature to run internal benchmarks [#93](https://github.com/midnightntwrk/midnight-zk/pull/93)

### Changed
* API for defining custom constraints was unified [#53](https://github.com/midnightntwrk/midnight-zk/pull/53)
* New cost-model with improved K computation [#104](https://github.com/midnightntwrk/midnight-zk/pull/104)
* Change type of k in cost model to u32 [#106](https://github.com/midnightntwrk/midnight-zk/pull/106)

### Removed

## 0.4.0
### Added
* Add deserialisation function that directly takes as input the ConstraintSystem [#18](https://github.com/midnightntwrk/midnight-zk/pull/18/commits/973467fecd6c31c6b57d06c89dfa0c7dd00bef2b)
* Add an `update_value` fn, to allow mutating the value inside an `AssignedCell` [#103](https://github.com/midnightntwrk/midnight-zk/pull/103)

### Changed
* VerifierQuery now accepts commitments in parts [#10](https://github.com/midnightntwrk/midnight-zk/pull/10)
* Update dependency names [#32](https://github.com/midnightntwrk/midnight-zk/pull/32)
* Fix versions of crates in monorepo [#33](https://github.com/midnightntwrk/midnight-zk/pull/33)
* Do not check transcript ends up empty [#34](https://github.com/midnightntwrk/midnight-zk/pull/34)
* Split `create_proof` into `trace` and `finalize` [#47](https://github.com/midnightntwrk/midnight-zk/pull/47)
* Optimize ops for `Expression<F>` and implement them for `&Expression<F>` [#52](https://github.com/midnightntwrk/midnight-zk/pull/52)
* Introduce trash arguments for additive selectors [#59](https://github.com/midnightntwrk/midnight-zk/pull/59)
* Implement TranscriptHash for u32 [#75](https://github.com/midnightntwrk/midnight-zk/pull/75)
* Improvement on verifier allocation and use of blstrs MSM [#76](https://github.com/midnightntwrk/midnight-zk/pull/76)
* Use HashMap instead of BTreeMap for computing shuffled tables [#61](https://github.com/midnightntwrk/midnight-zk/pull/61)
* Verifier skis `left` MSM if its size and its scalar are one [#102](https://github.com/midnightntwrk/midnight-zk/pull/102)
* Add a string to `Error::Synthesis` for a descriptive message [#105](https://github.com/midnightntwrk/midnight-zk/pull/105)

### Removed

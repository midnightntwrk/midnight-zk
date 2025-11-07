# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added

### Changed
* Address feedback from ZK Sec audit 3 [#125](https://github.com/midnightntwrk/midnight-zk/pull/125)
* Output type of `format_instances` is now wrapped in a `Result` [#120](https://github.com/midnightntwrk/midnight-zk/pull/120).
* Made bench_macros and criterion dev dependencies [#134](https://github.com/midnightntwrk/midnight-zk/pull/134)

### Removed

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

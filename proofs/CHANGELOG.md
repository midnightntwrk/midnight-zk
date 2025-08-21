# Changelog
 
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
### Changed
* API for defining custom constraints was unified [#53](https://github.com/midnightntwrk/midnight-zk/pull/53)
### Removed

## 0.4.0
### Added
* Add deserialisation function that directly takes as input the ConstraintSystem [#18](https://github.com/midnightntwrk/midnight-zk/pull/18/commits/973467fecd6c31c6b57d06c89dfa0c7dd00bef2b)
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

### Removed

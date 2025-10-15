# Changelog

All notable changes to `aggregator` will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://book.async.rs/overview/stability-guarantees.html).

## [Unreleased]
### Added
* Rebase to new `circuits/` [#120](https://github.com/midnightntwrk/midnight-zk/pull/120)
* Rebase to new `circuits/` with `sha512` [#96](https://github.com/midnightntwrk/midnight-zk/pull/96)
### Changed
### Removed

[0.1.2]
Update dependencies only.

[0.1.1]
### Added
* Missing load of native_chip and poseidon (although they were not necessary) [#90](https://github.com/midnightntwrk/midnight-zk/pull/90)

### Changed
* Modify `pow2range` chip: adjust architecture in light aggregator [#38](https://github.com/midnightntwrk/midnight-zk/pull/38)
* Update dependency names [#32](https://github.com/midnightntwrk/midnight-zk/pull/32)
* Fix versions of crates in monorepo [#33](https://github.com/midnightntwrk/midnight-zk/pull/33)
* Unify transcript style [#34](https://github.com/midnightntwrk/midnight-zk/pull/34)
* Fix minor issue (serialize u32 instead of u8 on acc lengths) [#75](https://github.com/midnightntwrk/midnight-zk/pull/75)
* Import CommittedInstanceInstructions [#381](https://github.com/midnightntwrk/midnight-zk/pull/381)
* Adapt ZkStdArch to new SHA256 chip [#39](https://github.com/midnightntwrk/midnight-zk/pull/39)
* Rebase to new cost-model with improved K computation [#104](https://github.com/midnightntwrk/midnight-zk/pull/104)

### Removed
* Add a turned-off automaton configuration due to the automaton chip being exposed in std_lib [#30](https://github.com/midnightntwrk/midnight-zk/pull/30)

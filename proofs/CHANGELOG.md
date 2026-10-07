# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
* `ConstraintSystem::fixed_polys_labels` and `ConstraintSystem::simple_selector_columns` [#547](https://github.com/midnightntwrk/midnight-zk/pull/547)
* `Rotation` derives `PartialOrd` and `Ord` [#543](https://github.com/midnightntwrk/midnight-zk/pull/543)
* `permutation::Argument::polynomial_labels`, `num_sets` and `accumulator_labels` are public [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* changed `sha256` name in benches to account for the change of naming convention in `circuits` [#135](https://github.com/midnightntwrk/midnight-zk/pull/135)
* optional names on VerifierQuery commitments [#205](https://github.com/midnightntwrk/midnight-zk/pull/205)
* `padded_add` and `padded_sub` polynomial operations [#276](https://github.com/midnightntwrk/midnight-zk/pull/276)
* `fewer-point-sets` feature to reduce the number of distinct multi-open point sets [#281](https://github.com/midnightntwrk/midnight-zk/pull/281)
* `LagrangeDelta` / `LagrangeDoubleDelta` commit bases [#379](https://github.com/midnightntwrk/midnight-zk/pull/379)
* `FloorPlanner` region-layout caching API (`synthesize_capturing_regions`, `synthesize_with_cached_regions`) and implementation in `SimpleFloorPlanner` to skip the shape pass during proving [#380](https://github.com/midnightntwrk/midnight-zk/pull/380)
* Add test for `FlatGraphEvaluator` [#394](https://github.com/midnightntwrk/midnight-zk/pull/394)
* `MSMKZG::new` constructor taking parallel slices of scalars, bases, and labels [#430](https://github.com/midnightntwrk/midnight-zk/pull/430)
* `KZGCommitment::collapse()` method and `From<KZGCommitment>` impl for `MSMKZG` [#430](https://github.com/midnightntwrk/midnight-zk/pull/430)
* Derive `Ord` on `PolynomialLabel`, making it usable as a `BTreeMap` key [#430](https://github.com/midnightntwrk/midnight-zk/pull/430)
* `commitment_byte_length` method on the `PolynomialCommitmentScheme` trait, defaulting to the per-commitment size times `n` and overridable for schemes that fold polynomials into a single proof element [#440](https://github.com/midnightntwrk/midnight-zk/pull/440)
* `circuit_model_with` taking an explicit commitment-size closure [#440](https://github.com/midnightntwrk/midnight-zk/pull/440)
* `Error::DuplicatedLabel`, returned when two polynomials of an argument group claim the same `PolynomialLabel` [#513](https://github.com/midnightntwrk/midnight-zk/pull/513)
* `ConstraintSystem::into_finalized`, converting the selectors of a constraint system to fixed columns without their polynomials, as in the constraint system of a verifying key [#546](https://github.com/midnightntwrk/midnight-zk/pull/546)
* `Fflonk<PCS, LOG2_T_MAX>`, a polynomial commitment scheme combining the polynomials of a group, in chunks of up to `2^LOG2_T_MAX`, into single polynomials committed to by the inner scheme `PCS` [#555](https://github.com/midnightntwrk/midnight-zk/pull/555)
* `PolynomialLabel::Collection`, a label made of other labels, and the `commitment_labels` method on the `PolynomialCommitmentScheme` trait, the labels a commitment tags its polynomials with [#555](https://github.com/midnightntwrk/midnight-zk/pull/555)
* `PolynomialCommitmentScheme::max_k`, the largest `k` such that some parameters can commit to polynomials of degree strictly less than `2^k` [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)
* `PolynomialCommitmentScheme::load_params`, reading the parameters of the scheme for committing to polynomials of degree strictly less than `2^k` [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)

### Fixed
* Cost model: a circuit with no permutation columns no longer underflows when counting the permutation queries, and is no longer charged for an accumulator commitment and its evaluations, which the prover does not produce [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* The KZG multi-open verifier reads the batch commitment `f` and the opening proof `π` through `read_commitment`, instead of reading them straight from the transcript and unwrapping them with `KZGMultiCommitment::into_single`. `into_single` panics on a group holding any other number of polynomials, and that number is declared by the prover, so a malformed proof could abort the verifier rather than fail verification [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* `KZGCommitmentScheme::read_commitment` rejects a commitment group holding a different number of polynomials than the number of labels expected. A group's length is declared in the proof and is not hashed into the transcript, so without this check the points read were silently zipped against the labels: a group truncated to one point made every query of that group resolve to that single commitment [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Resolve a query's commitment by matching its `PolynomialLabel` even when the group holds a single polynomial, instead of taking the sole inner commitment by position. The `Linear` linearization commitment, which aggregates many polynomials under no label of its own, is still taken as it is [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Bound the allocation in `Hashable::read` for `KZGMultiCommitment` by the bytes actually available, so a proof declaring a large group length no longer makes the verifier allocate up to 4 GiB before reading it [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Cost model: account for the length prefix framing each commitment group, and for the logup polynomials being committed in the two argument phase groups rather than one group per lookup argument. `commit(n)` is now the byte length of the single message that commits to `n` polynomials, so a site writing `n` commitments separately costs `n * commit(1)` [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Fix verifier evals bug [#356](https://github.com/midnightntwrk/midnight-zk/pull/356)
* Fix broken intra-doc links to private `Polynomial::padded_add` and `padded_sub` [#287](https://github.com/midnightntwrk/midnight-zk/pull/287)
* Fix cost model to account for committed instance column evaluations [#280](https://github.com/midnightntwrk/midnight-zk/pull/280)
* Increase number of blinding factors to account for logup helper polynomials [#312](https://github.com/midnightntwrk/midnight-zk/pull/312)
* Blind logup multiplicities polynomial on non-usable rows for ZK [#312](https://github.com/midnightntwrk/midnight-zk/pull/312)
* Fix cost-model [#435](https://github.com/midnightntwrk/midnight-zk/pull/435)

### Changed
* `ConstraintSystem::create_gate` panics on a gate whose polynomials are not all multiples of the same simple selector, or that queries a simple selector none of its polynomials is a multiple of. The verifier takes the evaluation of a simple selector as 1, which relies on that shape [#547](https://github.com/midnightntwrk/midnight-zk/pull/547)
* The verifying key commits to every fixed column but the simple selectors as one group, together with the fixed permutation polynomials, in the phase-0 group exposed as `VerifyingKey::phase0_commitment`, and to each simple selector on its own, as `VerifyingKey::simple_selector_commitments`. The serialized key changes to that layout, so every verifying key and its `transcript_repr` change [#547](https://github.com/midnightntwrk/midnight-zk/pull/547)
* The fixed columns are evaluated and opened through the phase-0 group: their evaluations are written to the proof with the group's, in label order, rather than once per fixed query. A simple selector is never opened, as before. Proof sizes do not change [#547](https://github.com/midnightntwrk/midnight-zk/pull/547)
* `msm_specific` always uses blst's `multi_exp_affine` for BLS12-381 G1,`msm_best`is a fallback for all other curves [#XXX](https://github.com/midnightntwrk/midnight-zk/pull/XXX)
* `commit_many`, `read_commitment` and `deserialize_commitment` take the labels of a group in the order it is committed to, rather than ordering them [#554](https://github.com/midnightntwrk/midnight-zk/pull/554)
* `ProverQuery` carries the labels and polynomials of the group the queried polynomial is committed with, so `multi_open` sees every polynomial committed together with the queried one [#554](https://github.com/midnightntwrk/midnight-zk/pull/554)
* KZG commits to a polynomial in Lagrange form as its evaluations over the domain whose size is its length, with `ParamsKZG` holding a Lagrange basis for every power-of-two size up to its own [#563](https://github.com/midnightntwrk/midnight-zk/pull/563)
* The KZG multi-open divides each point set's polynomial by the product of `X - point` at once, skipping its zero coefficients, instead of by each point in turn [#563](https://github.com/midnightntwrk/midnight-zk/pull/563)
* fflonk commits to polynomials in Lagrange form without converting them to coefficient form, keeping the rows where they vanish free in the commitment [#563](https://github.com/midnightntwrk/midnight-zk/pull/563)
* Keygen bounds the circuit size by `PolynomialCommitmentScheme::max_k` rather than by `Params::max_k` [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)
* The `PolynomialCommitmentScheme` implementation of `KZGCommitmentScheme<E>` requires `E::G1Affine: SerdeObject` and `E::G2: ProcessedSerdeObject` [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)
* `ProcessedSerdeObject` is implemented for curves that are not `Default` [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)
* `Guard` is generic over the verifier parameters of its PCS rather than over the PCS itself [#555](https://github.com/midnightntwrk/midnight-zk/pull/555)
* Commit the advice columns as part of the phase-1 argument group, together with the logup multiplicities, instead of one commitment per column, and open them through it at the rotations the circuit queries them at. This changes the transcript of every proof, which shrinks by 4 bytes per advice column (one fewer if the circuit has no lookup) [#543](https://github.com/midnightntwrk/midnight-zk/pull/543)
* Commit the logup multiplicities before squeezing `theta`, instead of after. The prover counts them by comparing the input and table tuples directly, and compresses the tuples with `theta` only when computing the helpers and aggregators. This changes the transcript of every proof over a circuit with a lookup [#543](https://github.com/midnightntwrk/midnight-zk/pull/543)
* Open the phase-1 and phase-2 groups first in the multi-open, followed by the phase-0 group and then the committed instances. This changes the opening proof but not its size [#543](https://github.com/midnightntwrk/midnight-zk/pull/543)
* Commit the permutation accumulators as part of the phase-2 argument group, and open the permutation polynomials as a phase-0 group, whose commitment lives in the verifying key rather than in the proof. `permutation::expressions` looks both sets of evaluations up by label, as the other arguments do, and the cost model counts the accumulators in the phase-2 group. This changes the transcript of every proof over a circuit with copy constraints: proofs produced by earlier versions no longer verify [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* The permutation polynomials are committed to as one group, in place of one commitment per polynomial. The verifying key holds that commitment directly, as `VerifyingKey::phase0_commitment() -> &CS::Commitment`; `permutation::VerifyingKey`, which held one commitment per polynomial, and the `VerifyingKey::permutation` accessor that returned it, are removed. A group is serialized as its polynomials' commitments back to back, so the verifying key's bytes and its `transcript_repr` are unchanged [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* `permutation::ProvingKey` is removed. The permutation polynomials belong to the proving key's phase-0 group, which holds them in coefficient form; the Lagrange form and the cosets that the prover reads once per proof are derived from it and cached beside it as `permutation::Sigmas`. `build_phase0_polys` derives the group and the `Sigmas` together, both at keygen and in `ProvingKey::read`, and is the only way to obtain either. The serialized key is unchanged: the Lagrange form is still the only one written [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* `compute_z_polys` and `Evaluator::evaluate_numerator` read the permutation polynomials from the proving key instead of taking the permutation proving key and its cosets as arguments [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* `commit_many` and `read_commitment` order a group's polynomials by their labels' `Ord` themselves, rather than requiring the caller to pass the labels in that order. Callers list the labels of a group in whatever order suits them and both sides agree on the on-wire order. A repeated label in a group now panics, in both, rather than being silently collapsed [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Commit the logup polynomials as generic argument groups: every multiplicities polynomial in the phase-1 group, and every aggregator, helper and trash polynomial in the phase-2 group, instead of one commitment per polynomial. `ChunkedArgument::expressions` takes the two evaluation maps and looks its own evaluations up by label. This changes the transcript of every proof over a circuit with a lookup: proofs produced by earlier versions no longer verify [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Frame each commitment group written to the proof with a little-endian `u32` byte-length prefix, so that `Hashable::read` for `KZGMultiCommitment` is self-delimiting. The prefix is not part of the hashed transcript; how many polynomials a group holds is pinned by the verifying key and checked on read. Proofs grow by 4 bytes per commitment group, and `KZGCommitmentScheme::commitment_byte_length` accounts for it [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* `commit_many` accepts a group with no polynomials. A commitment to no polynomials is neither written to nor absorbed into the transcript, and `read_commitment` with no labels reads nothing, in and out of circuit, so the phase groups of `VerifierTrace` are plain `Committed` values and `read_group` is removed. `commitment_byte_length(0)` is 0. The proof format is unchanged: an empty group was not written before either [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* Squeeze the trash challenge right after `gamma`, before the permutation and lookup commitments, so the trash polynomials are committed together with the other phase-2 polynomials. This changes the transcript of every proof, including for circuits with no trashcan: proofs produced by earlier versions no longer verify [#513](https://github.com/midnightntwrk/midnight-zk/pull/513)
* Commit the trash polynomials as a single generic argument group keyed by `PolynomialLabel`, rather than one commitment per trashcan. A new internal `plonk::argument` module owns the group's `Committed`/`Evaluated` types and the per-label opening points; `trash::Argument` is identified by an index instead of a name and looks its own evaluation up by label [#513](https://github.com/midnightntwrk/midnight-zk/pull/513)
* Migrate to Rust edition 2024; MSRV raised from 1.76 to 1.90. Both are now inherited from the workspace [#508](https://github.com/midnightntwrk/midnight-zk/pull/508)
* Extend `PolynomialCommitmentScheme` with `squeeze_evaluation_point` and add a `k` argument to `multi_prepare`, as PCS-agnostic extension points for fflonk [#487](https://github.com/midnightntwrk/midnight-zk/pull/487)
* `circuit_model` is now parameterized by a `PolynomialCommitmentScheme` (`circuit_model::<_, CS>`) instead of const `COMM`/`SCALAR` byte-size generics [#440](https://github.com/midnightntwrk/midnight-zk/pull/440)
* Rename `PolynomialPointer` to `PolynomialReference` in `ProverQuery`; rename `poly` field to `poly_ref`; change `poly_inner_product` to accept `&[&Polynomial<F, Coeff>]` to avoid cloning [#411](https://github.com/midnightntwrk/midnight-zk/pull/411)
* Rename `CommitmentLabel` to `PolynomialLabel`; add `NoLabel` variant for freshly deserialized commitments; introduce `Labelable` trait so every call site attaches the correct label after deserialization [#392](https://github.com/midnightntwrk/midnight-zk/pull/392)
* Introduce `KZGCommitment` enum with `Simple` and `Linear` variants; attach `CommitmentLabel` at `commit` time and propagate it homomorphically through arithmetic [#381](https://github.com/midnightntwrk/midnight-zk/pull/381)
* Simplify `CommitmentReference` to a pointer wrapper with identity-based equality; remove `commitment_label` from `VerifierQuery` [#381](https://github.com/midnightntwrk/midnight-zk/pull/381)
* Store SRS as affine and use an affine MSM path in KZG [#350](https://github.com/midnightntwrk/midnight-zk/pull/350)
* Cache twiddle factors in `EvaluationDomain` and use a pruned DIF FFT for `coeff_to_extended` [#352](https://github.com/midnightntwrk/midnight-zk/pull/352)
* Flatten and batch the graph evaluator for custom gates, lookups, and trash [#351](https://github.com/midnightntwrk/midnight-zk/pull/351)
* Parallelize logup, permutation, and SHPLONK [#353](https://github.com/midnightntwrk/midnight-zk/pull/353)
* Commit `perm_z` and `logup_multiplicities` in `LagrangeDelta`, `logup_aggregator` in `LagrangeDoubleDelta` [#379](https://github.com/midnightntwrk/midnight-zk/pull/379)
* Simplify `CommitmentReference` by removing unused `Chopped` variant [#314](https://github.com/midnightntwrk/midnight-zk/pull/314)
* Split linearization polynomial into non-constant and constant parts, removing the generator point from the MSM [#313](https://github.com/midnightntwrk/midnight-zk/pull/313)
* Remove unnecessary polynomial padding in KZG multi-open [#276](https://github.com/midnightntwrk/midnight-zk/pull/276)
* Sort point sets deterministically in KZG multiopen for in-circuit verification [#256](https://github.com/midnightntwrk/midnight-zk/pull/256)
* Move advice queries before instance queries in prover and verifier [#256](https://github.com/midnightntwrk/midnight-zk/pull/256)
* `Circuit::Params` extended to carry `max_bit_len` [#251](https://github.com/midnightntwrk/midnight-zk/pull/251)
* unifying `commit` and `commit_lagrange` [#368](https://github.com/midnightntwrk/midnight-zk/pull/368)
* Update feature `dev-curves` dependencies [#412](https://github.com/midnightntwrk/midnight-zk/pull/412)
* Simplify KZG multiopen verifier to use `KZGCommitment` directly [#430](https://github.com/midnightntwrk/midnight-zk/pull/430)

### Removed
* The `Params` trait. `max_k` and `downsize` remain inherent methods of `ParamsKZG`, and `downsize_from_circuit` is removed [#560](https://github.com/midnightntwrk/midnight-zk/pull/560)
* `fewer-point-sets` feature [#554](https://github.com/midnightntwrk/midnight-zk/pull/554)
* `VerifyingKey::fixed_commitments`, replaced by `phase0_commitment` and `simple_selector_commitments` [#547](https://github.com/midnightntwrk/midnight-zk/pull/547)
* `Clone` on `ProvingKey`, so that the polynomials it holds are never copied [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* Remove the internal `permutation::verifier` module and `permutation::Evaluated`; the permutation argument no longer carries any transcript plumbing of its own [#537](https://github.com/midnightntwrk/midnight-zk/pull/537)
* Remove `KZGCommitment::into_point`; use `as_point`, which borrows the point instead of consuming (and often cloning) the commitment [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Remove the internal `logup::verifier` module and `logup::Evaluated`; the lookup argument no longer carries any transcript plumbing of its own [#515](https://github.com/midnightntwrk/midnight-zk/pull/515)
* Remove the internal `trash::verifier` module and `trash::Evaluated`; the trash argument no longer carries any transcript plumbing of its own [#513](https://github.com/midnightntwrk/midnight-zk/pull/513)
* Remove the `Labelable` trait; commitments are now labeled while being read through `read_commitment` / `deserialize_commitment` instead of being re-labeled after deserialization [#491](https://github.com/midnightntwrk/midnight-zk/pull/491)
* Remove `Query<F>` trait; `construct_intermediate_sets` now accepts `&[(T, F, F)]` (commitment reference, point, eval) tuples with `T: PartialEq + Copy` [#411](https://github.com/midnightntwrk/midnight-zk/pull/411)
* Remove multi-phase PLONK support: `Phase`, `Challenge`, `FirstPhase`, and `Layouter::get_challenge()` are removed; `Any::Advice` is no longer phase-parameterized; the prover and dev tools synthesize in a single pass [#376](https://github.com/midnightntwrk/midnight-zk/pull/376)
* Remove multi-proof support; `create_proof` and `prepare` now operate on a single circuit and take `instances: &[&[F]]` instead of `&[&[&[F]]]` [#375](https://github.com/midnightntwrk/midnight-zk/pull/375)
* Remove `msm_inner_product` from `utils::arithmetic`; superseded by the generic `inner_product` [#430](https://github.com/midnightntwrk/midnight-zk/pull/430)
* Remove redundant `PolynomialLabel::Instance` variant; use `CommittedInstance` [#450](https://github.com/midnightntwrk/midnight-zk/pull/450)

## [0.8.0]
### Added
* Add `Blake2b256` transcript hash for on-chain verification [#322](https://github.com/midnightntwrk/midnight-zk/pull/322)
* Add functions to mark the region of a circuit to be measured for cost modelling [#296](https://github.com/midnightntwrk/midnight-zk/pull/296)
* changed `sha256` name in benches to account for the change of naming convention in `circuits` [#135](https://github.com/midnightntwrk/midnight-zk/pull/135)
* optional names on VerifierQuery commitments [#205](https://github.com/midnightntwrk/midnight-zk/pull/205)
* Update READMEs and add badges [#261](https://github.com/midnightntwrk/midnight-zk/pull/261)
* add MSMCompletenessFluke error [#277](https://github.com/midnightntwrk/midnight-zk/pull/277)

### Changed
* `MockProver::run` no longer takes a `k` parameter; the minimum required `k` is determined automatically [#293](https://github.com/midnightntwrk/midnight-zk/pull/293)
* Sort point sets deterministically in KZG multiopen for in-circuit verification [#256](https://github.com/midnightntwrk/midnight-zk/pull/256)
* Move advice queries before instance queries in prover and verifier [#256](https://github.com/midnightntwrk/midnight-zk/pull/256)
* `Circuit::Params` extended to carry `max_bit_len` [#251](https://github.com/midnightntwrk/midnight-zk/pull/251)
* (Benchmarks) Adapt `Relation` impl to new associated type `Error` [#252](https://github.com/midnightntwrk/midnight-zk/pull/252)
* Collapse MSMs during `multi_prepare` to match in-circuit verifier [#227](https://github.com/midnightntwrk/midnight-zk/pull/227)
* Improve MSM handling for fixed bases [#212](https://github.com/midnightntwrk/midnight-zk/pull/212)
* Filtered 0s from MSM [#185](https://github.com/midnightntwrk/midnight-zk/pull/185).
* Updated Rust toolchain to 1.90.0 [#210](https://github.com/midnightntwrk/midnight-zk/pull/210)
* Changed lookup argument to logup [#153](https://github.com/midnightntwrk/midnight-zk/pull/153)
* Implemented linearization prover [#190](https://github.com/midnightntwrk/midnight-zk/pull/190)
* Changed logup to use the selector variant [#220](https://github.com/midnightntwrk/midnight-zk/pull/220)
* Share the `z` and `m` polynomials across all logup instances [#279](https://github.com/midnightntwrk/midnight-zk/pull/279)

### Removed

## [0.7.1]
### Changed
* Thread the prover RNG explicitly [#307](https://github.com/midnightntwrk/midnight-zk/pull/307)
* Add `s_g2()` accessor on `ParamsVerifierKZG` [#307](https://github.com/midnightntwrk/midnight-zk/pull/307)

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

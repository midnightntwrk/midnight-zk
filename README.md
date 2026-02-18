# Midnight ZK

[![Crates.io Version](https://img.shields.io/crates/v/midnight-proofs?label=midnight-proofs)](https://crates.io/crates/midnight-proofs)
[![Crates.io Version](https://img.shields.io/crates/v/midnight-curves?label=midnight-curves)](https://crates.io/crates/midnight-curves)
[![Crates.io Version](https://img.shields.io/crates/v/midnight-circuits?label=midnight-circuits)](https://crates.io/crates/midnight-circuits)
[![Crates.io Version](https://img.shields.io/crates/v/midnight-zk-stdlib?label=midnight-zk-stdlib)](https://crates.io/crates/midnight-zk-stdlib)

This repository implements the proof system used in **Midnight**, along with tooling for building zero-knowledge circuits.

## Repository Structure

- `curves`: Implementation of elliptic curves used in Midnight, concretely BLS12-381 and JubJub.
- `proofs`: Plonk proof system using KZG commitments.
- `circuits`: Tooling for constructing ZK circuits.
- `aggregator`: Toolkit for proof aggregation of midnight-proofs.
- `zk_stdlib`: A high-level abstraction for building zero-knowledge circuits using `proofs` and `circuits`.

## Acknowledgments

This project was originally built upon the foundations of several outstanding open-source libraries:

- [`blstrs`](https://github.com/filecoin-project/blstrs) – by the Filecoin Project
- [`jubjub`](https://github.com/zcash/jubjub) – by the Zcash Project
- [`halo2curves`](https://github.com/privacy-scaling-explorations/halo2curves) v0.8.0 – by the Privacy Scaling Explorations (PSE) team
- [`halo2`](https://github.com/privacy-scaling-explorations/halo2) v0.3.0 – by the Privacy Scaling Explorations (PSE) team, itself originally derived from the [Zcash Sapling proving system](https://github.com/zcash/halo2)

We initially maintained the following components as forks:

- `bls12_381` and its embedded `jubjub` implementation originated as forks of `blstrs` and `jubjub`, respectively.
- `proofs` began as a fork of `halo2` v0.3.0.

Over time, our codebases have diverged from the upstream projects. These components are no longer maintained as forks and have evolved into standalone implementations tailored to Midnight's needs.

We gratefully acknowledge the authors and maintainers of the original projects.

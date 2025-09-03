# Midnight ZK

This repository implements the proof system used in **Midnight**, along with tooling for building zero-knowledge circuits.

## Repository Structure

- `curves`: Implementation of elliptic curves used in midnight, concretely BLS12-381 and JubJub
- `proof-system`: Plonk proof system using KZG commitments
- `circuits`: Tooling for constructing ZK circuits

## Acknowledgments

This project was originally built upon the foundations of several outstanding open-source libraries:

- [`blstrs`](https://github.com/filecoin-project/blstrs) – by the Filecoin Project
- [`jubjub`](https://github.com/zcash/jubjub) – by the Zcash Project
- [`halo2`](https://github.com/privacy-scaling-explorations/halo2) v0.3.0 – by the Privacy Scaling Explorations (PSE) team, itself originally derived from the [Zcash Sapling proving system](https://github.com/zcash/halo2)

We initially maintained the following components as forks:

- `bls12-381` and its embedded `jubjub` implementation originated as forks of `blstrs` and `jubjub`, respectively.
- `proof-system` began as a fork of `halo2` v0.3.0.

Over time, our codebases have diverged from the upstream projects. These components are no longer maintained as forks and have evolved into standalone implementations tailored to Midnight's needs.

We gratefully acknowledge the authors and maintainers of the original projects.

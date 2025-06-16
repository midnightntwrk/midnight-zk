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

# TODO - New Repo Owner

### Software Package Data Exchange (SPDX)
Include the following Software Package Data Exchange (SPDX) short-form identifier in a comment at the top headers of each source code file.


 <I>// This file is part of <B>REPLACE WITH REPO-NAME</B>.<BR>
 // Copyright (C) 2025 Midnight Foundation<BR>
 // SPDX-License-Identifier: Apache-2.0<BR>
 // Licensed under the Apache License, Version 2.0 (the "License");<BR>
 // You may not use this file except in compliance with the License.<BR>
 // You may obtain a copy of the License at<BR>
 //<BR>
 //	http://www.apache.org/licenses/LICENSE-2.0<BR>
 //<BR>
 // Unless required by applicable law or agreed to in writing, software<BR>
 // distributed under the License is distributed on an "AS IS" BASIS,<BR>
 // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.<BR>
 // See the License for the specific language governing permissions and<BR>
 // limitations under the License.</I>

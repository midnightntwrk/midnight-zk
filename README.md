# Midnight Circuits

[![CI checks](https://github.com/input-output-hk/midnight-circuits/actions/workflows/ci.yml/badge.svg)](https://github.com/input-output-hk/midnight-circuits/actions/workflows/ci.yml)
[![Examples](https://github.com/input-output-hk/midnight-circuits/actions/workflows/examples.yml/badge.svg)](https://github.com/input-output-hk/midnight-circuits/actions/workflows/examples.yml)

Midnight Circuits is a library for implementing circuits using [Halo2](https://github.com/zcash/halo2). It is based on the [Galois fork](https://github.com/input-output-hk/galois_recursion/tree/galois_base) of Halo2, which implements recursion over a cycle of curves.

> **Disclaimer**: This library has not been audited. Use it at your own risk.

## Features

Midnight Circuits provides several tools to facilitate circuit development with Halo2. These include:

1. Native and non-native field operations.
2. Native and non-native elliptic-curve operations.
3. Native and non-native hash-to-curve functionality.
4. Bit/Byte decomposition tools and range-checks.
5. SHA-256.
6. Set (non-)membersihp.

We aim to expose these functionalities via traits, which can be found in `[src/instructions]`.

## ZkStdLib

Midnight Circuits includes the `ZkStdLib`, which encapsulates the functionality required by Midnight. This library has a fixed configuration, meaning you cannot choose the number of columns, lookups, or gates. If you require this flexibility, you should build a circuit without using `ZkStdLib`.

The motivations for a fixed configuration are:

1. Simplified reasoning for recursion.
2. The verifier can perform pre-parsing of circuits since they all have the same structure.

`ZkStdLib` also serves as an abstraction layer, allowing developers to focus on circuit logic rather than the configuration and chip creation. Developers only need to implement the `Relation` trait, avoiding the boilerplate of Halo2's `Circuit`. For example, to prove knowledge of a SHA preimage:

```rust
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    testing_utils::real_test_api::filecoin_srs,
    types::{AssignedByte, Byte, Instantiable},
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = blstrs::Scalar;

// In this example we show how to build a circuit for proving the knowledge of a
// SHA256 preimage. Concretely, given public input x, we will argue that we know
// w ∈ {0,1}^192 such that x = SHA-256(w).

#[derive(Clone, Default)]
struct ShaPreImageCircuit {
    input_bytes: [Value<Byte>; 24], // 192 = 24 * 8
}

impl Relation for ShaPreImageCircuit {
    // When defining a circuit, one must clearly state the instance and the witness
    // of the underlying NP-relation.
    type Instance = [u8; 32];
    type Witness = [u8; 24];

    // The log2 of the number of rows in the circuit table.
    const K: u32 = 13;

    // We must specify how the instance is converted into raw field elements to
    // be process by the prover/verifier. The order here must be consistent with
    // the order in which public inputs are constrained/assigned in [circuit].
    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        instance
            .iter()
            .flat_map(|b| AssignedByte::<F>::as_public_input(&Byte(*b)))
            .collect()
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        ShaPreImageCircuit {
            input_bytes: witness.map(Byte).map(Value::known),
        }
    }

    // Define the logic of the NP-relation being proved.
    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let assigned_input = std_lib.assign_many(layouter, &self.input_bytes)?;
        let output = std_lib.sha256(layouter, &assigned_input)?;
        output
            .iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }
}

fn main() {
    let srs = filecoin_srs(ShaPreImageCircuit::K);

    let vk = compact_std_lib::setup_vk::<ShaPreImageCircuit>(&srs);
    let pk = compact_std_lib::setup_pk::<ShaPreImageCircuit>(&srs, &vk);

    // Sample a random preimage as the witness.
    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
    let instance = sha2::Sha256::digest(witness).into();

    let proof = compact_std_lib::prove::<ShaPreImageCircuit>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<ShaPreImageCircuit>(&srs, &vk, &instance, proof)
}
```

You can find more examples in the examples directory.

## Versioning

We use [Semantic Versioning](https://semver.org/spec/v2.0.0.html). To capture 
the changes that do not affect the API, do not add any new functionality, but
are breaking changes, we increment the `MAJOR` version. This happens when the 
circuit is modified for performance or bug fixes; the modification of the 
verification keys break backwards compatibility. 

* MAJOR: Incremented when you make incompatible API or VK changes
* MINOR: Incremented when you add functionality in a backward-compatible manner
* PATCH: Incremented when you make backward-compatible bug fixes


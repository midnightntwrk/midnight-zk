# Midnight ZK Standard Library

The Midnight ZK Standard Library (`midnight-zk-stdlib`) provides a 
high-level abstraction for building zero-knowledge circuits using the 
[Midnight Circuits](../circuits) library and the [Midnight Proofs](../proofs)
proving system.

> **WARNING**: This library has not been audited. Use it at your own risk.

## Overview

`ZkStdLib` encapsulates the functionality required by Midnight and serves as an abstraction layer, allowing developers to focus on circuit logic rather than the configuration and chip creation. Developers only need to implement the `Relation` trait, avoiding the boilerplate of Halo2's `Circuit` trait.

The architecture of `ZkStdLib` is configurable via the following structure:

```rust
pub struct ZkStdLibArch {
    pub jubjub: bool,
    pub poseidon: bool,
    pub sha2_256: bool,
    pub sha2_512: bool,
    pub sha3_256: bool,
    pub keccak_256: bool,
    pub blake2b: bool,
    pub secp256k1: bool,
    pub bls12_381: bool,
    pub base64: bool,
    pub automaton: bool,
    pub nr_pow2range_cols: u8,
}
```

The configuration can be defined via the `Relation` trait with the `used_chips` function. The default architecture activates only `JubJub`, `Poseidon` and `sha256`, and uses a single column for the `pow2range` chip. The maximum number of columns accepted for the `pow2range` chip is currently 4.

## Example: Proving Knowledge of a SHA-256 Preimage

Here is a complete example showing how to build a circuit for proving knowledge of a SHA-256 preimage.
Given a public input `x`, we will prove that we know `w ∈ {0,1}^192` such that `x = SHA-256(w)`.

```rust
use midnight_circuits::{
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Instantiable},
};
use midnight_zk_stdlib::{utils::plonk_api::filecoin_srs, Relation, ZkStdLib, ZkStdLibArch};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = midnight_curves::Fq;

#[derive(Clone, Default)]
struct ShaPreImageCircuit;

impl Relation for ShaPreImageCircuit {
    // When defining a circuit, one must clearly state the instance and the witness
    // of the underlying NP-relation.
    type Instance = [u8; 32]; // x ∈ {0, 1}^256
    type Witness = [u8; 24];  // w ∈ {0, 1}^192  (192 = 24 * 8)

    // We must specify how the instance, which can be any Rust type, is converted
    // into raw field elements to be processed by the prover/verifier. The order 
    // here must be consistent with the order in which public inputs are 
    // constrained/assigned in [circuit].
    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error>  {
        Ok(instance
            .iter()
            .flat_map(AssignedByte::<F>::as_public_input)
            .collect())
    }

    // Define the logic of the NP-relation being proved.
    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_input = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.sha2_256(layouter, &assigned_input)?;
        output
            .iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaPreImageCircuit)
    }
}

// An upper bound on the log2 of the number of rows in the circuit.
// The closer to the real value, the better, but you do not have to worry too much.
const K: u32 = 14;
let mut srs = filecoin_srs(K);

let relation = ShaPreImageCircuit;

// The actual k needed by this circuit is 13. We can downsize it automatically.
midnight_zk_stdlib::downsize_srs_for_relation(&mut srs, &relation);

let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

// Sample a random preimage as the witness.
let mut rng = ChaCha8Rng::from_entropy();
let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
let instance = sha2::Sha256::digest(witness).into();

let proof = midnight_zk_stdlib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
    &srs, &pk, &relation, &instance, witness, OsRng,
)
.expect("Proof generation should not fail");

assert!(
    midnight_zk_stdlib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof
    )
    .is_ok()
)
```

You can find more examples in the [examples directory](examples/).

## Versioning

We use [Semantic Versioning](https://semver.org/spec/v2.0.0.html). To capture the changes that do not affect the API, do not add any new functionality, but are breaking changes, we increment the `MAJOR` version. This happens when the circuit is modified for performance or bug fixes; the modification of the verification keys break backwards compatibility.

* MAJOR: Incremented when you make incompatible API or VK changes
* MINOR: Incremented when you add functionality in a backward-compatible manner
* PATCH: Incremented when you make backward-compatible bug fixes

# Midnight Circuits

[![CI checks](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/ci.yml/badge.svg)](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/ci.yml)
[![Examples](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/examples.yml/badge.svg)](https://github.com/midnightntwrk/midnight-circuits/actions/workflows/examples.yml)

Midnight Circuits is a library designed for implementing circuits with [Halo2](https://github.com/zcash/halo2). It is built on the [PSE v0.4.0 release](https://github.com/privacy-scaling-explorations/halo2/releases/tag/v0.4.0) of Halo2, incorporating a few [minor additions](https://github.com/midnightntwrk/halo2/commits/dev/) required to support Midnight Circuits.

> **Disclaimer**: This library has not been audited. Use it at your own risk.

## Features

Midnight Circuits provides several tools to facilitate circuit development with Halo2. These include:

1. Native and non-native field operations.
2. Native and non-native elliptic-curve operations.
3. Native and non-native hash-to-curve functionality.
4. Bit/Byte decomposition tools and range-checks.
5. SHA-256.
6. SHA-512.
7. Set (non-)membership.
8. BigUInt.
9. Variable length vectors (see explanation below).
10. Finite-state automata parsing.
11. In-circuit verification of Plonk proofs (a.k.a. recursion)

We aim to expose these functionalities via traits, which can be found in `[src/instructions]`.

### Variable length vectors
We provide support for variable-length vectors in-circuit, even when the exact size of the vector is unknown 
at compilation time. Each variable-length vector is parameterized with a `MAX_LENGTH` attribute, which 
specifies the maximum allowed size.

The cost of using these structures in-circuit is proportional to the `MAX_LENGTH`, while the computed result 
is guaranteed to correspond to the operation applied to the actual vector values. For example, operations 
such as hashing or parsing are performed over the full vector of length `MAX_LENGTH`, and the final result 
is conditionally selected to reflect the operation applied only to the actual elements of the vector.


## ZkStdLib

Midnight Circuits includes the `ZkStdLib`, which encapsulates the functionality required by Midnight. 
The architecture of `ZkStdLib` is configurable via the following structure:

```text
pub struct ZkStdLibArch {
    pub jubjub: bool,
    pub poseidon: bool,
    pub sha256: bool,
    pub sha512: bool,
    pub secp256k1: bool,
    pub bls12_381: bool,
    pub base64: bool,
    pub nr_pow2range_cols: u8,
    pub automaton: bool,
}
```

which can be defined via the `Relation` trait with the `used_chips` function. The default 
architecture activates only `JubJub`, `Poseidon` and `sha256`, and uses a single column for
`pow2range` chip. The maximum number of columns accepted for the `pow2range` chip is currently
at 4.

`ZkStdLib` also serves as an abstraction layer, allowing developers to focus on circuit logic 
rather than the configuration and chip creation. Developers only need to implement the `Relation` 
trait, avoiding the boilerplate of Halo2's `Circuit`. For example, to prove knowledge of a SHA preimage:

```rust
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedByte, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = midnight_curves::Fq;

// In this example we show how to build a circuit for proving the knowledge of a
// SHA256 preimage. Concretely, given public input x, we will argue that we know
// w ∈ {0,1}^192 such that x = SHA-256(w).

#[derive(Clone, Default)]
struct ShaPreImageCircuit;

impl Relation for ShaPreImageCircuit {
    // When defining a circuit, one must clearly state the instance and the witness
    // of the underlying NP-relation.
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192 = 24 * 8

    // We must specify how the instance is converted into raw field elements to
    // be process by the prover/verifier. The order here must be consistent with
    // the order in which public inputs are constrained/assigned in [circuit].
    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        instance
            .iter()
            .flat_map(AssignedByte::<F>::as_public_input)
            .collect()
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
        let output = std_lib.sha256(layouter, &assigned_input)?;
        output
            .iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }
    
    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 1,
            automaton: false,
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
compact_std_lib::downsize_srs_for_relation(&mut srs, &relation);

let vk = compact_std_lib::setup_vk(&srs, &relation);
let pk = compact_std_lib::setup_pk(&relation, &vk);

// Sample a random preimage as the witness.
let mut rng = ChaCha8Rng::from_entropy();
let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
let instance = sha2::Sha256::digest(witness).into();

let proof = compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
    &srs, &pk, &relation, &instance, witness, OsRng,
)
.expect("Proof generation should not fail");

assert!(
    compact_std_lib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof
    )
    .is_ok()
)
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

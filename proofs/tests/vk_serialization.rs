//! Serialization of the proving and verifying keys: the bytes a key writes are
//! the bytes it reads back, `bytes_length` is the length of those bytes, and
//! the `transcript_repr` derived from them is the same on both paths (keygen
//! and deserialization).

use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, ProvingKey, Selector,
        VerifyingKey, keygen_pk, keygen_vk_with_k,
    },
    poly::{
        Rotation,
        kzg::{KZGCommitmentScheme, params::ParamsKZG},
    },
    utils::{SerdeFormat, arithmetic::Field},
};
use rand::{SeedableRng, rngs::StdRng};

const K: u32 = 5;

#[derive(Clone)]
struct Config {
    a: Column<Advice>,
    b: Column<Advice>,
    s: Selector,
}

#[derive(Default)]
struct MyCircuit;

impl Circuit<Fq> for MyCircuit {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        MyCircuit
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let q = meta.fixed_column();
        let s = meta.selector();

        // Three columns in the permutation argument: two advice and the fixed
        // column carrying constants.
        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_constant(q);

        meta.create_gate("a = b", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            Constraints::with_selector(s, vec![a - b])
        });

        Config { a, b, s }
    }

    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                config.s.enable(&mut region, 0)?;
                let a = region.assign_advice(|| "", config.a, 0, || Value::known(Fq::ONE))?;
                a.copy_advice(|| "", &mut region, config.b, 0)?;
                Ok(())
            },
        )
    }
}

fn keygen() -> VerifyingKey<Fq, KZGCommitmentScheme<Bls12>> {
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, StdRng::seed_from_u64(0));
    keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &MyCircuit, K)
        .expect("vk should not fail")
}

#[test]
fn vk_round_trip() {
    for format in [
        SerdeFormat::Processed,
        SerdeFormat::RawBytes,
        SerdeFormat::RawBytesUnchecked,
    ] {
        let vk = keygen();
        let bytes = vk.to_bytes(format);
        assert_eq!(bytes.len(), vk.bytes_length(format));

        let read = VerifyingKey::<Fq, KZGCommitmentScheme<Bls12>>::from_bytes::<MyCircuit>(
            &bytes,
            format,
            #[cfg(feature = "circuit-params")]
            (),
        )
        .expect("vk should deserialize");

        assert_eq!(read.to_bytes(format), bytes);
        assert_eq!(read.transcript_repr(), vk.transcript_repr());
    }
}

#[test]
fn pk_round_trip() {
    for format in [
        SerdeFormat::Processed,
        SerdeFormat::RawBytes,
        SerdeFormat::RawBytesUnchecked,
    ] {
        let pk = keygen_pk(keygen(), &MyCircuit).expect("pk should not fail");
        let bytes = pk.to_bytes(format);
        assert_eq!(bytes.len(), pk.bytes_length(format));

        let read = ProvingKey::<Fq, KZGCommitmentScheme<Bls12>>::from_bytes::<MyCircuit>(
            &bytes,
            format,
            #[cfg(feature = "circuit-params")]
            (),
        )
        .expect("pk should deserialize");

        assert_eq!(read.to_bytes(format), bytes);
    }
}

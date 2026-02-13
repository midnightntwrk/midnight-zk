use std::{
    fs::File,
    io::{BufReader, BufWriter, Write},
};

use blake2b_simd::State;
use ff::Field;
use midnight_curves::{Bls12, Fq as Scalar};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk_with_k, prepare, Advice, Circuit, Column,
        ConstraintSystem, Constraints, Error, Fixed, Instance, ProvingKey,
    },
    poly::{
        commitment::Guard,
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use rand_core::OsRng;

#[derive(Clone, Copy)]
struct StandardPlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_a: Column<Fixed>,
    q_b: Column<Fixed>,
    q_c: Column<Fixed>,
    q_ab: Column<Fixed>,
    constant: Column<Fixed>,
    #[allow(dead_code)]
    instance: Column<Instance>,
}

impl StandardPlonkConfig {
    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self {
        let [a, b, c] = [(); 3].map(|_| meta.advice_column());
        let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
        let instance = meta.instance_column();

        [a, b, c].iter().for_each(|column| meta.enable_equality(*column));

        meta.create_gate(
            "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
            |meta| {
                let [a, b, c] = [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                    .map(|column| meta.query_fixed(column, Rotation::cur()));
                let instance = meta.query_instance(instance, Rotation::cur());
                Constraints::without_selector(vec![(
                    "Arithmetic gate",
                    q_a * &a + q_b * &b + q_c * c + q_ab * a * b + constant + instance,
                )])
            },
        );

        StandardPlonkConfig {
            a,
            b,
            c,
            q_a,
            q_b,
            q_c,
            q_ab,
            constant,
            instance,
        }
    }
}

#[derive(Clone, Default)]
struct StandardPlonk(Scalar);

impl Circuit<Scalar> for StandardPlonk {
    type Config = StandardPlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self::Config {
        StandardPlonkConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Scalar::ONE))?;

                region.assign_advice(|| "", config.a, 1, || Value::known(-Scalar::from(5u64)))?;
                for (idx, column) in (1..).zip([
                    config.q_a,
                    config.q_b,
                    config.q_c,
                    config.q_ab,
                    config.constant,
                ]) {
                    region.assign_fixed(
                        || "",
                        column,
                        1,
                        || Value::known(Scalar::from(idx as u64)),
                    )?;
                }

                let a = region.assign_advice(|| "", config.a, 2, || Value::known(Scalar::ONE))?;
                a.copy_advice(|| "", &mut region, config.b, 3)?;
                a.copy_advice(|| "", &mut region, config.c, 4)?;
                Ok(())
            },
        )
    }
}

fn main() {
    let k = 4;
    let circuit = StandardPlonk(Scalar::random(OsRng));
    let params = ParamsKZG::<Bls12>::unsafe_setup(k, OsRng);
    let vk = keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, k)
        .expect("vk should not fail");
    let pk = keygen_pk(vk, &circuit).expect("pk should not fail");

    let f = File::create("serialization-test.pk").unwrap();
    let mut writer = BufWriter::new(f);
    pk.write(&mut writer, SerdeFormat::RawBytes).unwrap();
    writer.flush().unwrap();

    let f = File::open("serialization-test.pk").unwrap();
    let mut reader = BufReader::new(f);
    #[allow(clippy::unit_arg)]
    let pk = ProvingKey::<Scalar, KZGCommitmentScheme<Bls12>>::read::<_, StandardPlonk>(
        &mut reader,
        SerdeFormat::RawBytes,
        #[cfg(feature = "circuit-params")]
        circuit.params(),
    )
    .unwrap();

    std::fs::remove_file("serialization-test.pk").unwrap();

    let instances: &[&[Scalar]] = &[&[circuit.0]];
    let mut transcript = CircuitTranscript::<State>::init();

    create_proof::<Scalar, KZGCommitmentScheme<Bls12>, _, _>(
        &params,
        &pk,
        &[circuit],
        #[cfg(feature = "committed-instances")]
        0,
        &[instances],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");

    let proof = transcript.finalize();

    let mut transcript = CircuitTranscript::<State>::init_from_bytes(&proof[..]);

    assert!(prepare::<Scalar, KZGCommitmentScheme<Bls12>, _>(
        pk.get_vk(),
        #[cfg(feature = "committed-instances")]
        &[&[]],
        &[instances],
        &mut transcript,
    )
    .unwrap()
    .verify(&params.verifier_params())
    .is_ok());
}

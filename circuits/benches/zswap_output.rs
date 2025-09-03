//! Bechmarks for the prover and verifier performance on the Zswap-output
//! circuit from the zswap protocol.
//!
//! For more details, visit:
//! https://github.com/midnightntwrk/midnight-ledger-prototype/blob/main/zswap/zswap.compact

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use ff::Field;
use group::Group;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib},
    ecc::{hash_to_curve::HashToCurveGadget, native::EccChip},
    hash::poseidon::PoseidonChip,
    instructions::{
        AssignmentInstructions, ConversionInstructions, DecompositionInstructions, EccInstructions,
        HashToCurveCPU, PublicInputInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, AssignedNativePoint, Instantiable},
};
use midnight_curves::{Fr as JubjubScalar, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::params::ParamsKZG,
};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = midnight_curves::Fq;

type CoinCom = [u8; 32];
type ValueCom = JubjubSubgroup;

#[derive(Clone, Copy, Debug)]
pub enum PK {
    ZSwapCoinPublicKey([u8; 32]),
    ContractAddress([u8; 32]),
}

#[derive(Clone, Copy, Debug)]
pub struct CoinInfo {
    color: F,
    nonce: F,
    value: u64,
}

#[derive(Clone, Debug)]
struct AssignedPK {
    bytes: [AssignedByte<F>; 32],
    is_contract: AssignedBit<F>,
}

#[derive(Clone, Debug)]
struct AssignedCoinInfo {
    color_bytes: [AssignedByte<F>; 32],
    nonce_bytes: [AssignedByte<F>; 32],
    value_bytes: [AssignedByte<F>; 8],

    color: AssignedNative<F>,
    value: AssignedNative<F>,
}

#[derive(Clone, Default)]
pub struct ZSwapOutputCircuit;

impl Relation for ZSwapOutputCircuit {
    type Instance = (CoinCom, ValueCom);

    type Witness = (PK, CoinInfo, JubjubScalar);

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        let mut pi: Vec<F> = (instance.0.iter())
            .flat_map(AssignedByte::<F>::as_public_input)
            .collect();
        pi.extend(AssignedNativePoint::<Jubjub>::as_public_input(&instance.1));
        pi
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let pk = assign_pk(std_lib, layouter, witness.as_ref().map(|w| w.0))?;
        let coin = assign_coin(std_lib, layouter, witness.as_ref().map(|w| w.1))?;
        let domain_sep = assign_fixed_domain_sep(std_lib, layouter, "mdn:cc")?;

        let coin_com = {
            std_lib.sha256(
                layouter,
                &[
                    coin.color_bytes.to_vec(),
                    coin.nonce_bytes.to_vec(),
                    coin.value_bytes.to_vec(),
                    vec![pk.is_contract.into()],
                    pk.bytes.to_vec(),
                    domain_sep,
                ]
                .concat(),
            )?
        };

        let value_com = {
            let color_base = std_lib.hash_to_curve(layouter, &[coin.color])?;
            let gen = std_lib
                .jubjub()
                .assign_fixed(layouter, JubjubSubgroup::generator())?;
            let rc = std_lib
                .jubjub()
                .assign(layouter, witness.as_ref().map(|w| w.2))?;
            let coin_value_as_scalar = std_lib.jubjub().convert(layouter, &coin.value)?;
            std_lib
                .jubjub()
                .msm(layouter, &[coin_value_as_scalar, rc], &[color_base, gen])?
        };

        coin_com
            .iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))?;

        std_lib
            .jubjub()
            .constrain_as_public_input(layouter, &value_com)
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ZSwapOutputCircuit)
    }
}

fn assign_pk(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    pk: Value<PK>,
) -> Result<AssignedPK, Error> {
    let (bytes_val, is_contract_val) = pk
        .map(|pk| match pk {
            PK::ZSwapCoinPublicKey(bytes) => (bytes, false),
            PK::ContractAddress(bytes) => (bytes, true),
        })
        .unzip();

    let bytes = std_lib.assign_many(layouter, &bytes_val.transpose_array())?;

    Ok(AssignedPK {
        bytes: bytes.try_into().unwrap(),
        is_contract: std_lib.assign(layouter, is_contract_val)?,
    })
}

fn assign_coin(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    coin: Value<CoinInfo>,
) -> Result<AssignedCoinInfo, Error> {
    let color = std_lib.assign(layouter, coin.map(|coin| coin.color))?;
    let nonce = std_lib.assign(layouter, coin.map(|coin| coin.nonce))?;
    let value = std_lib.assign(layouter, coin.map(|coin| F::from(coin.value)))?;

    let color_bytes = std_lib.assigned_to_le_bytes(layouter, &color, Some(32))?;
    let nonce_bytes = std_lib.assigned_to_le_bytes(layouter, &nonce, Some(32))?;
    let value_bytes = std_lib.assigned_to_le_bytes(layouter, &value, Some(8))?;

    Ok(AssignedCoinInfo {
        color_bytes: color_bytes.try_into().unwrap(),
        nonce_bytes: nonce_bytes.try_into().unwrap(),
        value_bytes: value_bytes.try_into().unwrap(),
        color,
        value,
    })
}

fn assign_fixed_domain_sep(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    domain_sep: &str,
) -> Result<Vec<AssignedByte<F>>, Error> {
    std_lib.assign_many_fixed(layouter, domain_sep.as_bytes())
}

fn sample_zswap_inputs() -> (
    <ZSwapOutputCircuit as Relation>::Instance,
    <ZSwapOutputCircuit as Relation>::Witness,
) {
    let mut rng = ChaCha8Rng::from_entropy();

    let zswap_pk_bytes = core::array::from_fn(|_| rng.gen());
    let zswap_pk_is_contract: bool = rng.gen();
    let zswap_pk = match zswap_pk_is_contract {
        false => PK::ZSwapCoinPublicKey(zswap_pk_bytes),
        true => PK::ContractAddress(zswap_pk_bytes),
    };

    let coin = CoinInfo {
        color: F::from(42),
        nonce: F::random(&mut rng),
        value: 1000,
    };

    let coin_com: [u8; 32] = {
        let mut preimage = coin.color.to_bytes_le().to_vec();
        preimage.extend(coin.nonce.to_bytes_le().to_vec());
        preimage.extend(coin.value.to_le_bytes().to_vec());
        preimage.push(zswap_pk_is_contract as u8);
        preimage.extend(zswap_pk_bytes.map(|b| b).to_vec());
        preimage.extend("mdn:cc".as_bytes());
        sha2::Sha256::digest(preimage).into()
    };

    let rc = JubjubScalar::random(rng);
    let value_com = {
        let coin_base = <HashToCurveGadget<
            F,
            Jubjub,
            AssignedNative<F>,
            PoseidonChip<F>,
            EccChip<Jubjub>,
        > as HashToCurveCPU<Jubjub, F>>::hash_to_curve(&[coin.color]);
        JubjubSubgroup::generator() * rc + coin_base * JubjubScalar::from(coin.value)
    };

    let witness = (zswap_pk, coin, rc);
    let instance = (coin_com, value_com);

    (instance, witness)
}

fn bench_zswap_output(c: &mut Criterion) {
    const K: u32 = 14;
    let srs = ParamsKZG::unsafe_setup(K, OsRng);

    let relation = ZSwapOutputCircuit;
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let mut group = c.benchmark_group("zswap-output");

    group.sample_size(10);
    group.bench_function("prove", |b| {
        b.iter_batched(
            sample_zswap_inputs,
            |(instance, witness)| {
                let _proof = compact_std_lib::prove::<ZSwapOutputCircuit, blake2b_simd::State>(
                    black_box(&srs),
                    black_box(&pk),
                    black_box(&relation),
                    black_box(&instance),
                    black_box(witness),
                    OsRng,
                )
                .expect("proof generation failed");
            },
            criterion::BatchSize::SmallInput,
        );
    });

    let (instance, witness) = sample_zswap_inputs();
    let proof = compact_std_lib::prove::<ZSwapOutputCircuit, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("proof generation failed");

    group.sample_size(100);
    group.bench_function("verify", |b| {
        b.iter(|| {
            assert!(
                compact_std_lib::verify::<ZSwapOutputCircuit, blake2b_simd::State>(
                    black_box(&srs.verifier_params()),
                    black_box(&vk),
                    black_box(&instance),
                    black_box(None),
                    black_box(&proof)
                )
                .is_ok()
            )
        });
    });

    group.finish();
}

criterion_group!(benches, bench_zswap_output);
criterion_main!(benches);

use std::{
    fs::File,
    io::{BufReader, Write},
    path::Path,
    time::Instant,
};

use blstrs::Bls12;
use halo2_proofs::{
    plonk::{keygen_pk, keygen_vk},
    poly::{commitment::Params, kzg::commitment::ParamsKZG},
    SerdeFormat,
};
use midnight_circuits::compact_std_lib::{MidnightCircuit, Relation};

use crate::circuit::BigMachineExample;

mod circuit;

type Circuit = MidnightCircuit<BigMachineExample>;

fn main() {
    let params_fs = File::open("./bls_srs").expect("couldn't load proof parameters");
    let mut params: ParamsKZG<Bls12> =
        ParamsKZG::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params");
    params.downsize(BigMachineExample::K);

    let timer = Instant::now();
    let vk = keygen_vk(&params, &Circuit::default()).expect("keygen_vk should not fail");
    println!("VK generation time: {:?}ms", timer.elapsed().as_millis());

    // Initialize the polynomial commitment parameters.
    let params_path = Path::new(&"./vk");
    let mut buf = Vec::new();

    vk.write(&mut buf, SerdeFormat::RawBytesUnchecked)
        .expect("Failed to write VK");
    let mut file = File::create(params_path).expect("Failed to create file");

    file.write_all(&buf[..])
        .expect("Failed to write VK to file");

    let timer = Instant::now();
    println!("Start proving key");
    let pk = keygen_pk(&params, vk, &Circuit::default()).expect("keygen_pk should not fail");
    println!("PK generation time: {:?}ms", timer.elapsed().as_millis());

    // Initialize the polynomial commitment parameters.
    let params_path = Path::new(&"./pk");
    let mut buf = Vec::new();

    pk.write(&mut buf, SerdeFormat::RawBytesUnchecked)
        .expect("Failed to write PK");
    let mut file = File::create(params_path).expect("Failed to create file");

    file.write_all(&buf[..])
        .expect("Failed to write PK to file");
}

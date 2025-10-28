use std::{fs::File, io::Write, path::Path, time::Instant};

use blstrs::Bls12;
use halo2_proofs::poly::{
    commitment::{Params, ParamsProver},
    kzg::commitment::ParamsKZG,
};

mod circuit;

fn main() {
    // Initialize the polynomial commitment parameters
    let params_path = Path::new(&"./bls_srs");
    // Parameter generation
    let timer = Instant::now();
    let params = ParamsKZG::<Bls12>::new(21);
    println!(
        "KZG SRS generation time: {:?}ms",
        timer.elapsed().as_millis()
    );
    let mut buf = Vec::new();

    params.write(&mut buf).expect("Failed to write params");
    let mut file = File::create(params_path).expect("Failed to create file");

    file.write_all(&buf[..])
        .expect("Failed to write params to file");
}

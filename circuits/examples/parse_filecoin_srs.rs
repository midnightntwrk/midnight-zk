//! Binary to read the file format of the powers of tau.

use std::{
    fs::{File, OpenOptions},
    io::{Read, Write},
};

use bellman::{
    domain::{EvaluationDomain, Group},
    multicore::Worker,
};
use blstrs::{Bls12, G1Affine, G2Affine};
use halo2curves::{serde::SerdeObject, CurveAffine};
use midnight_proofs::{poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use rand::rngs::OsRng;

const G1_SIZE: usize = 96;
const G2_SIZE: usize = 192;

const K: usize = 19;
const TAU_POWERS_LENGTH: usize = 1 << K;

#[derive(Clone, Copy, Debug)]
struct WrapperPoint<C: CurveAffine>(C);

impl<C: CurveAffine> Group<C::Scalar> for WrapperPoint<C> {
    fn group_zero() -> Self {
        WrapperPoint(C::identity())
    }

    fn group_mul_assign(&mut self, by: &C::Scalar) {
        self.0 = self.0.mul(*by).into()
    }

    fn group_add_assign(&mut self, other: &Self) {
        self.0 = self.0.add(other.0).into()
    }

    fn group_sub_assign(&mut self, other: &Self) {
        self.0 = self.0.sub(other.0).into()
    }
}

#[allow(clippy::type_complexity)]
fn read_points() -> std::io::Result<(Vec<WrapperPoint<G1Affine>>, Vec<WrapperPoint<G2Affine>>)> {
    let srs_dir = std::env::var("SRS_DIR").unwrap_or("./examples/assets".into());

    let mut fd = OpenOptions::new()
        .read(true)
        .open(format!("{srs_dir}/phase1radix2m19"))?;

    let mut header = [0u8; G1_SIZE + G1_SIZE + G2_SIZE];
    fd.read_exact(&mut header[..])?;

    let mut g1_points = vec![];
    for _ in 0..TAU_POWERS_LENGTH {
        let mut bytes = [0u8; G1_SIZE];
        fd.read_exact(&mut bytes)?;

        g1_points.push(WrapperPoint(
            G1Affine::from_raw_bytes(&bytes).expect("Failed to deserialise G1 point"),
        ));
    }

    let mut g2_points = vec![];
    for _ in 0..TAU_POWERS_LENGTH {
        let mut bytes = [0u8; G2_SIZE];
        fd.read_exact(&mut bytes)?;

        g2_points.push(WrapperPoint(
            G2Affine::from_raw_bytes(&bytes).expect("Failed to deserialise g2 point"),
        ));
    }

    Ok((g1_points, g2_points))
}

fn main() -> std::io::Result<()> {
    let srs_dir = std::env::var("SRS_DIR").unwrap_or("./examples/assets".into());

    if OpenOptions::new()
        .read(true)
        .open(format!("{srs_dir}/bls_filecoin_2p19"))
        .is_ok()
    {
        return Ok(());
    }

    let (g1s, g2s) = read_points()?;

    let worker = &Worker::new();
    let mut eval_domain_1 =
        EvaluationDomain::from_coeffs(g1s.clone()).expect("Failed to generate Evaluation domain");
    eval_domain_1.fft(worker);
    let mut eval_domain_2 =
        EvaluationDomain::from_coeffs(g2s.clone()).expect("Failed to generate Evaluation domain");
    eval_domain_2.fft(worker);

    let g1 = eval_domain_1
        .into_coeffs()
        .into_iter()
        .map(|p| p.0.into())
        .collect::<Vec<_>>();
    let g2 = eval_domain_2
        .into_coeffs()
        .into_iter()
        .map(|p| p.0.into())
        .collect::<Vec<_>>();

    let g1s = g1s.into_iter().map(|p| p.0.into()).collect::<Vec<_>>();

    let params = ParamsKZG::<Bls12>::unsafe_setup(K as u32, OsRng);
    let params = params.from_parts(K as u32, g1, Some(g1s), g2[0], g2[1]);
    let mut buf = Vec::new();

    params
        .write_custom(&mut buf, SerdeFormat::RawBytesUnchecked)
        .expect("Failed to write");
    let mut file =
        File::create(format!("{srs_dir}/bls_filecoin_2p19")).expect("Failed to create file");

    file.write_all(&buf[..])
        .expect("Failed to write Params to file");

    Ok(())
}

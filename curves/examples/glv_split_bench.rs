//! Timing of the GLV scalar split (tuning aid, not shipped).
use ff::{Field, PrimeField};
use midnight_curves::{CurveAffine, Fq, G1Affine, msm::glv_split};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

fn main() {
    let mut rng = XorShiftRng::seed_from_u64(1);
    let (_, lambda) = G1Affine::glv().unwrap();
    let ks: Vec<_> = (0..1 << 16).map(|_| Fq::random(&mut rng).to_repr()).collect();
    let t = std::time::Instant::now();
    let mut acc = 0u8;
    for k in &ks {
        let (a, b) = glv_split(k.as_ref(), lambda);
        acc ^= a[0] ^ b[0];
    }
    let el = t.elapsed();
    let t2 = std::time::Instant::now();
    for k in &ks {
        acc ^= Fq::from_repr(*k).unwrap().to_repr()[0];
    }
    println!(
        "split {:.0} ns/scalar; to_repr round trip {:.0} ns ({acc})",
        el.as_nanos() as f64 / ks.len() as f64,
        t2.elapsed().as_nanos() as f64 / ks.len() as f64
    );
}

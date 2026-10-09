//! Profiling loop for the XYZZ Pippenger (tuning aid, not shipped).
use group::{Curve, Group};
use midnight_curves::{
    G1Affine, G1Projective,
    msm::{msm_xyzz_glv_with_window, msm_xyzz_with_window},
};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

fn main() {
    let k: usize = std::env::args().nth(1).map_or(12, |a| a.parse().unwrap());
    let c: usize = std::env::args().nth(2).map_or(9, |a| a.parse().unwrap());
    let mut rng = XorShiftRng::seed_from_u64(1);
    let bases: Vec<G1Affine> =
        (0..1 << k).map(|_| G1Projective::random(&mut rng).to_affine()).collect();
    let coeffs: Vec<_> = (0..1 << k).map(|_| ff::Field::random(&mut rng)).collect();
    let mode = std::env::args().nth(3).unwrap_or_default();
    let glv = mode == "glv";
    let blst = mode == "blst";
    let t = std::time::Instant::now();
    let mut n = 0;
    while t.elapsed().as_secs() < 10 {
        if blst {
            std::hint::black_box(G1Affine::multi_exp_affine(&bases, &coeffs));
        } else if glv {
            std::hint::black_box(msm_xyzz_glv_with_window(&coeffs, &bases, c));
        } else {
            std::hint::black_box(msm_xyzz_with_window(&coeffs, &bases, c));
        }
        n += 1;
    }
    println!(
        "{n} runs, {:.0} us each",
        t.elapsed().as_secs_f64() * 1e6 / n as f64
    );
}

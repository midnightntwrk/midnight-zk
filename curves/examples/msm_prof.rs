//! Profiling loop for the Pippenger (tuning aid, not shipped).
use group::{Curve, Group};
use midnight_curves::serde::SerdeObject;
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
    let best = mode == "best";
    // blst1: blst's own single-threaded Pippenger, for a like-for-like `RAYON_NUM_THREADS=1` A/B
    let blst1 = mode == "blst1";
    let (affines, scalar_bytes) = blst1_inputs(&bases, &coeffs);
    let mut scratch =
        vec![0u64; unsafe { blst::blst_p1s_mult_pippenger_scratch_sizeof(bases.len()) } / 8];
    // x1: ours inside a one-thread pool, so all the work (and nothing else) is on one thread
    let pool =
        (mode == "x1").then(|| rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap());
    let t = std::time::Instant::now();
    let mut n = 0;
    // ITERS=n: exactly n runs (for instruction counts); otherwise as many as fit in 10 s
    let iters: Option<usize> = std::env::var("ITERS").ok().map(|v| v.parse().unwrap());
    while iters.map_or(t.elapsed().as_secs() < 10, |i| n < i) {
        if blst1 {
            let points = [affines.as_ptr(), std::ptr::null()];
            let scalars = [scalar_bytes.as_ptr(), std::ptr::null()];
            let mut out = blst::blst_p1::default();
            // SAFETY: both inputs hold `bases.len()` elements and `scratch` is sized by blst
            unsafe {
                blst::blst_p1s_mult_pippenger(
                    &mut out,
                    points.as_ptr(),
                    bases.len(),
                    scalars.as_ptr(),
                    255,
                    scratch.as_mut_ptr(),
                )
            };
            std::hint::black_box(out);
        } else if let Some(pool) = &pool {
            std::hint::black_box(pool.install(|| msm_xyzz_with_window(&coeffs, &bases, c)));
        } else if best {
            std::hint::black_box(midnight_curves::msm::msm_best(&coeffs, &bases));
        } else if blst {
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

fn blst1_inputs(
    bases: &[G1Affine],
    coeffs: &[midnight_curves::Fq],
) -> (Vec<blst::blst_p1_affine>, Vec<u8>) {
    let affines = bases
        .iter()
        .map(|b| {
            let mut a = blst::blst_p1_affine::default();
            // SAFETY: `to_uncompressed` is a valid 96-byte serialisation
            let r = unsafe { blst::blst_p1_deserialize(&mut a, b.to_raw_bytes().as_ptr()) };
            assert_eq!(r, blst::BLST_ERROR::BLST_SUCCESS);
            a
        })
        .collect();
    (
        affines,
        coeffs.iter().flat_map(|s| s.to_bytes_le()).collect(),
    )
}

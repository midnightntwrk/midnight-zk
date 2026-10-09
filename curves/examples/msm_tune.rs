//! Window-size sweep for the MSM backends (tuning aid, not shipped).
use std::time::Instant;

use group::{Curve, Group};
use midnight_curves::{
    G1Affine, G1Projective,
    msm::{
        msm_batch_affine_with_window, msm_pointwise, msm_xyzz_glv_with_window, msm_xyzz_with_window,
    },
};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

fn median_us(mut f: impl FnMut()) -> f64 {
    let mut ts: Vec<f64> = (0..21)
        .map(|_| {
            let t = Instant::now();
            f();
            t.elapsed().as_secs_f64() * 1e6
        })
        .collect();
    ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
    ts[3]
}

fn main() {
    let mut rng = XorShiftRng::seed_from_u64(1);
    let max_k = 18;
    let bases: Vec<G1Affine> =
        (0..1 << max_k).map(|_| G1Projective::random(&mut rng).to_affine()).collect();
    let coeffs: Vec<_> = (0..1 << max_k).map(|_| ff::Field::random(&mut rng)).collect();
    for k in [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] {
        let n = 1 << k;
        let (s, b) = (&coeffs[..n], &bases[..n]);
        let blst = median_us(|| {
            G1Affine::multi_exp_affine(b, s);
        });
        let best = median_us(|| {
            midnight_curves::msm::msm_best(s, b);
        });
        let pw = median_us(|| {
            msm_pointwise(s, b);
        });
        print!("k={k:2} blst={blst:9.0} best={best:9.0} pointwise={pw:8.0} | xyzz c:");
        for c in 3..=15usize {
            if c + 3 < k / 2 || c > k + 2 {
                continue;
            }
            let t = median_us(|| {
                msm_xyzz_with_window(s, b, c);
            });
            print!(" {c}:{t:.0}");
        }
        if std::env::var("GLV").is_err() {
            println!();
            continue;
        }
        print!(" | glv c:");
        for c in [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] {
            if k < 12 && c > 12 {
                continue;
            }
            let t = median_us(|| {
                msm_xyzz_glv_with_window(s, b, c);
            });
            print!(" {c}:{t:.0}");
        }
        if std::env::var("GRID").is_err() {
            println!();
            continue;
        }
        print!(" | batch c:");
        for c in 3..=14 {
            let t = median_us(|| {
                msm_batch_affine_with_window(s, b, c);
            });
            print!(" {c}:{t:.0}");
        }
        println!();
    }
}

//! Timing of the GLV scalar split (tuning aid, not shipped).
use ff::{Field, PrimeField};
use midnight_curves::{
    CurveAffine, Fq, G1Affine,
    msm::{glv_split, glv_split_fast},
};
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
    let m = {
        // ⌊2^256/λ⌋, as glv_reciprocal computes it
        let lam = lambda;
        let (mut rem, mut q) = (1u128, [0u64; 3]);
        for _ in 0..256 {
            let carry = rem >> 127;
            rem <<= 1;
            let bit = carry == 1 || rem >= lam;
            if bit {
                rem = rem.wrapping_sub(lam);
            }
            q = [
                q[0] << 1 | u64::from(bit),
                q[1] << 1 | q[0] >> 63,
                q[2] << 1 | q[1] >> 63,
            ];
        }
        q
    };
    let t3 = std::time::Instant::now();
    for k in &ks {
        let (a, b) = glv_split_fast(k.as_ref(), lambda, &m);
        acc ^= a[0] ^ b[0];
    }
    let fast = t3.elapsed();
    let t2 = std::time::Instant::now();
    for k in &ks {
        acc ^= Fq::from_repr(*k).unwrap().to_repr()[0];
    }
    println!(
        "Barrett split {:.1} ns/scalar",
        fast.as_nanos() as f64 / ks.len() as f64
    );
    println!(
        "long-division split {:.0} ns/scalar; to_repr round trip {:.0} ns ({acc})",
        el.as_nanos() as f64 / ks.len() as f64,
        t2.elapsed().as_nanos() as f64 / ks.len() as f64
    );
}

// SPDX-License-Identifier: Apache-2.0

use std::{env, mem::size_of};

use ff::{Field, PrimeField};
use midnight_curves::{Fq, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rayon::prelude::*;

use super::{
    hooks::{self, Expected::Device},
    transforms,
};

fn sparse_terms(n: usize) -> [(usize, Fq); 7] {
    let positions = [0, 1, n / 4, n / 2 - 1, n / 2, n - 2, n - 1];
    std::array::from_fn(|i| (positions[i], Fq::from((13 * i + 1) as u64)))
}

fn input(n: usize) -> Vec<Fq> {
    let mut a = vec![Fq::ZERO; n];
    for (pos, value) in sparse_terms(n) {
        a[pos] = value;
    }
    a
}

// Check the same seven sparse inputs as the full stock FFT, in linear time.
// At x = root^i the quarter- and half-domain powers repeat every four rows.
// The remaining powers are x, 1/x and 1/x². Stream them inside each chunk.
fn check_sparse_transform(actual: &[Fq], root: Fq, scale: Fq) {
    let n = actual.len();
    if n < 8 {
        // Some positions coincide. Use the exact input (including overwrites).
        let mut expected = input(n);
        best_fft(&mut expected, root, n.ilog2());
        expected.iter_mut().for_each(|v| *v *= scale);
        super::same_values(actual, &expected, "max-k transform");
        return;
    }
    let [
        constant,
        linear,
        quarter,
        half_minus_one,
        half,
        penultimate,
        last,
    ] = sparse_terms(n).map(|(_, value)| value * scale);
    let mut periodic = [constant, quarter, half, Fq::ZERO];
    best_fft(&mut periodic, root.pow_vartime([(n / 4) as u64]), 2);
    let mut inverse_linear = [last, half_minus_one];
    best_fft(&mut inverse_linear, -Fq::ONE, 1);

    let step_inv = root.invert().unwrap();
    let step_inv_sq = step_inv.square();
    const CHUNK: usize = 16384;
    actual.par_chunks(CHUNK).enumerate().for_each(|(chunk, values)| {
        let start = chunk * CHUNK;
        let mut x_term = linear * root.pow_vartime([start as u64]);
        let mut x_inv = step_inv.pow_vartime([start as u64]);
        let mut x_inv_sq_term = penultimate * x_inv.square();
        for (i, value) in values.iter().enumerate() {
            let expected = periodic[i % 4] + x_term + inverse_linear[i % 2] * x_inv + x_inv_sq_term;
            assert_eq!(*value, expected, "coefficient {}", start + i);
            x_term *= root;
            x_inv *= step_inv;
            x_inv_sq_term *= step_inv_sq;
        }
    });
}

#[test]
fn maximum_k() {
    hooks::run(0, false, || {
        let parameter = env::var("FUZZ_MAX_K").unwrap_or_else(|_| "10".into());
        let k = if parameter == "auto" {
            // Initialize both sppark root tables, then free the temporary data buffer.
            transforms(4, 1, 1, false);
            assert!(gpu::end_request());
            let (free, _) = gpu::mem_info().expect("auto sizing needs device memory information");
            // gpu/src/ntt.rs uses one device scratch element per transform element.
            let k = (free / size_of::<gpu::Scalar>()).ilog2().min(gpu::MAX_EXT_K);
            eprintln!("CUDA free after warmup: {free} bytes");
            k
        } else {
            parameter.parse::<u32>().expect("FUZZ_MAX_K must be auto or an integer")
        };
        assert!((1..=gpu::MAX_EXT_K).contains(&k));
        let n = 1usize << k;
        eprintln!(
            "maximum_k: k={k}, {n} field elements, {} bytes of device scratch",
            n * size_of::<Fq>()
        );
        let mut omega = Fq::ROOT_OF_UNITY;
        for _ in k..Fq::S {
            omega = omega.square();
        }
        for inverse in [false, true] {
            let mut actual = input(n);
            let scale = inverse.then(|| Fq::from(n as u64).invert().unwrap());
            let root = if inverse {
                omega.invert().unwrap()
            } else {
                omega
            };
            let w = adapter::scalar(root);
            let accepted = if let Some(d) = scale {
                hooks::IFFT.check(Device, || {
                    hooks::ifft(adapter::scalars_mut(&mut actual), w, k, adapter::scalar(d))
                })
            } else {
                hooks::FFT.check(Device, || {
                    hooks::fft(adapter::scalars_mut(&mut actual), w, k)
                })
            };
            assert_eq!(accepted, gpu::cuda_built());
            if !accepted {
                best_fft(&mut actual, root, k);
                if let Some(scale) = scale {
                    actual.iter_mut().for_each(|x| *x *= scale);
                }
            }
            assert!(gpu::end_request());
            check_sparse_transform(&actual, root, scale.unwrap_or(Fq::ONE));
        }
    });
}

// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Chunked parallel Montgomery batch inversion.
//!
//! The permutation and LogUp provers invert plain slices of denominators.
//! For the BLS12-381 scalar field, each chunk needs one inversion of the
//! product of its nonzero elements. Inversion in this field does no
//! operand-dependent work. Zero stays zero, and every nonzero inverse is
//! unique, so changing the chunk size or thread count preserves every result.
//!
//! Prefix products use heap scratch. Slices below the parallel threshold
//! are handled serially without consulting the thread pool. Other fields
//! use the stock batch inversion at every size.

use std::any::TypeId;

use ff::{BatchInvert, BatchInverter, Field};
use rayon::{iter::ParallelIterator, slice::ParallelSliceMut};

pub(crate) fn is_bls_scalar<F: Field>() -> bool {
    TypeId::of::<F>() == TypeId::of::<midnight_curves::Fq>()
}

const MAX_CHUNK: usize = 1024;
/// Shorter slices are inverted without consulting the thread pool.
const MIN_PAR_LEN: usize = 256;

/// Serial chunked Montgomery batch inversion: the same values as
/// `parallel_batch_invert`, with no rayon call. Zero elements stay
/// zero, as with `ff::BatchInvert::batch_invert`.
///
/// The prefix-product scratch is one heap `Vec` sized to the smaller
/// of the input length and the chunk size. It is dropped unzeroed,
/// as the scratch `Vec` of `ff::BatchInvert` is.
pub(crate) fn serial_batch_invert<F: Field>(values: &mut [F]) {
    let mut scratch = vec![F::ZERO; values.len().min(MAX_CHUNK)];
    for chunk in values.chunks_mut(MAX_CHUNK) {
        BatchInverter::invert_with_external_scratch(chunk, &mut scratch[..chunk.len()]);
    }
}

/// Inverts each non-zero element of `values` in place using chunked
/// Montgomery batch inversion across the current rayon threads. Zero
/// elements stay zero, as with `ff::BatchInvert::batch_invert`.
pub(crate) fn parallel_batch_invert<F: Field>(values: &mut [F]) {
    if !is_bls_scalar::<F>() {
        // The stock batch inversion: one field inversion of the
        // product of all nonzero elements, and no rayon call.
        values.iter_mut().batch_invert();
        #[cfg(all(test, feature = "dev-curves"))]
        tests::USED_STOCK_INVERSION.set(true);
        return;
    }
    if values.len() < MIN_PAR_LEN {
        return serial_batch_invert(values);
    }

    let num_threads = rayon::current_num_threads().max(1);
    if num_threads == 1 {
        return serial_batch_invert(values);
    }

    let chunk_size = values.len().div_ceil(num_threads).clamp(64, MAX_CHUNK);
    values.par_chunks_mut(chunk_size).for_each_init(
        || vec![F::ZERO; chunk_size],
        |scratch, chunk| {
            BatchInverter::invert_with_external_scratch(chunk, &mut scratch[..chunk.len()]);
        },
    );
}

#[cfg(test)]
mod tests {
    use ff::{BatchInvert, Field, PrimeField};
    use midnight_curves::Fq as Scalar;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::{parallel_batch_invert, serial_batch_invert};

    #[cfg(feature = "dev-curves")]
    thread_local! {
        pub(super) static USED_STOCK_INVERSION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }

    fn in_pool<R: Send>(threads: usize, f: impl FnOnce() -> R + Send) -> R {
        rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap().install(f)
    }

    fn assert_same<F: PrimeField>(par: &[F], ser: &[F]) {
        assert_eq!(par.len(), ser.len());
        for (a, b) in par.iter().zip(ser.iter()) {
            assert!(
                a.to_repr().as_ref() == b.to_repr().as_ref(),
                "field element mismatch"
            );
        }
    }

    fn check_invert<F: PrimeField>(input: &[F], threads: usize) {
        let mut par = input.to_vec();
        in_pool(threads, || parallel_batch_invert(&mut par));
        let mut ser = input.to_vec();
        ser.iter_mut().batch_invert();
        assert_same(&par, &ser);
    }

    #[test]
    fn parallel_batch_invert_matches_serial() {
        let mut rng = ChaCha20Rng::from_seed([0x42; 32]);
        let sizes = [
            0usize, 1, 2, 3, 7, 63, 64, 65, 255, 256, 257, 1000, 1023, 1024, 1025, 4097, 20000,
        ];
        for &n in &sizes {
            let cases: Vec<Vec<Scalar>> = vec![
                vec![Scalar::ZERO; n],
                (0..n).map(|_| Scalar::random(&mut rng)).collect(),
                (0..n)
                    .map(|i| match i % 5 {
                        0 => Scalar::ZERO,
                        1 => Scalar::ONE,
                        2 => -Scalar::ONE,
                        _ => Scalar::random(&mut rng),
                    })
                    .collect(),
                (0..n).map(|i| Scalar::from((i % 3) as u64)).collect(),
            ];
            for case in &cases {
                for threads in [1usize, 2, 4] {
                    check_invert(case, threads);
                }
            }
        }
    }

    #[test]
    fn serial_batch_invert_matches_serial() {
        // The small path of `parallel_batch_invert` is this separate
        // function, which contains no rayon call; here it is checked
        // directly for every size below and around the threshold.
        let mut rng = ChaCha20Rng::from_seed([0x17; 32]);
        for n in 0..=300usize {
            let input: Vec<Scalar> = (0..n)
                .map(|i| match i % 5 {
                    0 => Scalar::ZERO,
                    1 => Scalar::ONE,
                    2 => -Scalar::ONE,
                    _ => Scalar::random(&mut rng),
                })
                .collect();
            let mut par = input.clone();
            serial_batch_invert(&mut par);
            let mut ser = input;
            ser.iter_mut().batch_invert();
            assert_same(&par, &ser);
        }
    }

    #[test]
    fn serial_batch_invert_on_small_stack() {
        // The scratch is on the heap, sized to the input, so a
        // single-value inversion fits on a small stack.
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::Builder::new()
            .stack_size(40 * 1024)
            .spawn(move || {
                let mut values = vec![Scalar::from(7u64)];
                serial_batch_invert(&mut values);
                sender.send(values[0] * Scalar::from(7u64) == Scalar::ONE).unwrap();
            })
            .unwrap();
        assert!(receiver.recv_timeout(std::time::Duration::from_secs(10)).unwrap());
    }

    #[test]
    fn parallel_batch_invert_all_zero_chunks() {
        // A chunk with no non-zero element must not attempt to invert zero.
        for threads in [1usize, 2, 4] {
            check_invert(&vec![Scalar::ZERO; 5000], threads);
        }
    }

    #[cfg(feature = "dev-curves")]
    #[test]
    fn parallel_batch_invert_takes_stock_path_for_bn256() {
        use midnight_curves::bn256::Fr as BnScalar;

        in_pool(4, || {
            for n in [100, 5000] {
                let mut values: Vec<_> = (0..n).map(|i| BnScalar::from(i % 5)).collect();
                let mut expected = values.clone();
                expected.iter_mut().batch_invert();

                USED_STOCK_INVERSION.set(false);
                parallel_batch_invert(&mut values);
                assert!(USED_STOCK_INVERSION.get(), "BN256 must use stock inversion");
                assert_same(&values, &expected);
            }
        });
    }

    #[test]
    #[ignore]
    fn timing_batch_invert() {
        use std::time::Instant;

        fn median_of_5(mut runs: Vec<std::time::Duration>) -> std::time::Duration {
            runs.sort();
            runs[2]
        }

        let mut rng = ChaCha20Rng::from_seed([0x5; 32]);
        for log_n in [18u32, 20, 21] {
            let n = 1usize << log_n;
            let input: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let mut stock = Vec::new();
            let mut par = Vec::new();
            for _ in 0..5 {
                let mut v = input.clone();
                let t = Instant::now();
                v.iter_mut().batch_invert();
                stock.push(t.elapsed());
                let mut v = input.clone();
                let t = Instant::now();
                parallel_batch_invert(&mut v);
                par.push(t.elapsed());
            }
            println!(
                "batch_invert n=2^{} stock_median={:?} par_median={:?} threads={}",
                log_n,
                median_of_5(stock),
                median_of_5(par),
                rayon::current_num_threads()
            );
        }
    }
}

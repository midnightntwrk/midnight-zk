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

//! The running product of the permutation argument, in parallel blocks: the
//! block products, a short scan for each block's first value, then the stock
//! recurrence within each block. Field multiplication is exact, so the values
//! are the stock ones.

use ff::Field;
use rayon::{
    iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

/// Rows per block.
const BLOCK: usize = 1 << 13;

/// The `n` values `z_0 = 1`, `z_r = z_{r-1} · m_{r-1}` (`m` holds at least
/// `n - 1` factors; `n >= 1`).
pub(crate) fn prefix_product_from_one<F: Field>(m: &[F], n: usize) -> Vec<F> {
    assert!(n >= 1 && m.len() >= n - 1);
    let blocks = n.div_ceil(BLOCK);
    let block_products: Vec<F> = (0..blocks.saturating_sub(1))
        .into_par_iter()
        .map(|b| m[b * BLOCK..(b + 1) * BLOCK].iter().fold(F::ONE, |acc, f| acc * f))
        .collect();
    let mut starts = Vec::with_capacity(blocks);
    starts.push(F::ONE);
    for p in &block_products {
        let next = *starts.last().unwrap() * p;
        starts.push(next);
    }

    let mut z: Vec<F> = (0..n).into_par_iter().map(|_| F::ZERO).collect();
    z.par_chunks_mut(BLOCK).zip(starts.into_par_iter()).enumerate().for_each(
        |(b, (block, start))| {
            let first = b * BLOCK;
            block[0] = start;
            for j in 1..block.len() {
                block[j] = block[j - 1] * m[first + j - 1];
            }
        },
    );
    z
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_curves::Fq;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::*;
    use crate::par::testing::{assert_on_pools, random_values, stock_prefix_product};

    /// Factors with zeros and ones, and nonzero factors only.
    #[test]
    fn prefix_product_matches_stock() {
        let mut rng = ChaCha20Rng::seed_from_u64(0x2a);
        for n in [1, 2, BLOCK, 3 * BLOCK + 7] {
            let mut m = random_values(&mut rng, n);
            for i in (0..n).step_by(997) {
                m[i] = if i % 2 == 0 { Fq::ZERO } else { Fq::ONE };
            }
            for m in [m.clone(), m.iter().map(|x| *x + Fq::ONE).collect()] {
                assert_on_pools(&stock_prefix_product(&m, n), || {
                    prefix_product_from_one(&m, n)
                });
            }
        }
    }
}

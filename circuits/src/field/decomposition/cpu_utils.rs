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

//! CPU implementations for witness generation

use std::collections::HashMap;

use crate::CircuitField;

/// Decomposes an element of the input field into limbs of variable sizes and
/// each limb is in the output field: given x\in InF and a slice limb_sizes that
/// represents bit lengths, it returns [a_1, ..., a_m] such that:
///      (1) x = sum c_i a_i
///      (2) a_i < 2^{limbs_size{i}}
///      (3) c_i = 2^{sum_{j=1}^{i-1} limb_sizes\[i\]}
///      (4) a_i in OutF
///
/// Every limb size must be at most 64, so that limbs fit in a `u64`.
///
/// # Panics
///
/// If the field element cannot be represented with limb_sizes (in debug
/// builds), or if some limb size exceeds 64.
pub(crate) fn decompose_in_variable_limbsizes<InF: CircuitField, OutF: CircuitField>(
    x: &InF,
    limb_sizes: &[usize],
) -> Vec<OutF> {
    let bytes = x.to_bytes_le();
    let bytes = bytes.as_ref();

    // Reads the `size <= 64` bits of `x` starting at bit `shift`. Bits beyond the
    // end of the representation are zero.
    let read_bits = |shift: usize, size: usize| -> u64 {
        assert!(
            size <= 64,
            "Decomposition Chip: limb sizes above 64 bits are not supported"
        );
        let first = shift / 8;
        let mut window = [0u8; 16];
        let avail = bytes.len().saturating_sub(first).min(16);
        window[..avail].copy_from_slice(&bytes[first.min(bytes.len())..][..avail]);
        let mask = if size == 0 {
            0
        } else {
            u128::MAX >> (128 - size)
        };
        ((u128::from_le_bytes(window) >> (shift % 8)) & mask) as u64
    };

    let mut shift = 0;
    let limbs = limb_sizes
        .iter()
        .map(|&limb_size| {
            // NOTE: when the limb_size is 0 the limb is always 0
            let limb = OutF::from(read_bits(shift, limb_size));
            shift += limb_size;
            limb
        })
        .collect::<Vec<_>>();

    // sanity check. Panics if the limbs are not enough to represent the number
    #[cfg(not(test))]
    debug_assert!(
        bytes.iter().enumerate().all(|(i, &b)| {
            let low_bits_kept = shift.saturating_sub(8 * i).min(8);
            (b as u32) >> low_bits_kept == 0
        }),
        "Decomposition Chip: the integer cannot be represented with the given limb_sizes"
    );

    limbs
}

/// Returns `2^exponent` as a field element.
fn pow2<F: CircuitField>(exponent: usize) -> F {
    if exponent < 128 {
        F::from_u128(1u128 << exponent)
    } else {
        F::from(2u64).pow_vartime([exponent as u64])
    }
}

/// Compute the fixed coefficients when decomposing with variable limbs
/// (see [decompose_in_variable_limbsizes])
///
/// Given a slice limbs_sizes this corresponds to
/// - c_i = 2^{sum_{j=1}^{i-1} limb_sizes\[i\]} if limb_sizes\[i\] > 0
/// - 0 if limb_sizes=0
pub(super) fn variable_limbsize_coefficients<F: CircuitField>(limb_sizes: &[usize]) -> Vec<F> {
    // 2^shift, where shift is the sum of the previous limb sizes
    let mut power_of_two = F::ONE;
    limb_sizes
        .iter()
        .map(|&limb_size| {
            // by convenion we return the zero coefficient when we have a trivial limb size
            let coefficient = if limb_size == 0 {
                F::ZERO
            } else {
                power_of_two
            };
            power_of_two *= pow2::<F>(limb_size);
            coefficient
        })
        .collect()
}

/// Helper function to fill the limb sizes with trivial ones, i.e. zeros
pub(super) fn process_limb_sizes(max_parallel_lookups: usize, limbs: &mut Vec<usize>) {
    while !limbs.len().is_multiple_of(max_parallel_lookups) {
        limbs.push(0)
    }
}

/// Dynamic Programming algorithm to compute the optimal (in number of rows)
/// limb decomposition of a number of the form `2^i` using a single parallel
/// lookup that asserts in a single `max_parallel_lookups` numbers are smaller
/// than `2^{bit_length}` for `0 < bit_length <= max_bit_len`.
///
/// The idea is the following: given a number x any decomposition will be of the
/// form
/// - [x_1, x_2, x_3, ..., x_k, 0, 0, 0] where x_i's are limbs of the same
///   bitlength b in the current row
/// - decompose(x - k * b) in the next rows.
///
/// The total number of rows needed will be rows(decompose(b)) = 1 +
/// rows(decompose(x-k*b))
///
/// Since we don't know the optimal values k, b we bruteforce through all
/// possibilities and keep the one that minimizes the total number of rows.
///
/// We implement this using Dynamic Programing with Memoization: we recursively
/// solve the smaller sized problems and keeping the optimal solutions to the
/// `solution` HashMap
///
/// The recursive formula for the above is the following:
///
/// if bound = 0: OPT(bound) = 0 with SOL = [] (base case)
/// otherwise it is 1 + OPT where
///      OPT(bound) =
///         min_{
///             cols:       1..=max_parallel_lookups,
///             bit_length: 1..=max_bit_length
///             }
///         1 + OPT(bound - i*j)
///      with SOL = [i; j] concatenated with SOL(bound - i*j)
pub(crate) fn compute_optimal_limb_sizes(
    solutions: &mut HashMap<i32, Vec<Vec<usize>>>,
    max_parallel_lookups: usize,
    max_bit_length: usize,
    // we use an i32 type because of the operation `bound - (bit_length * parallel_lookups)`
    // which could result in a negative number (although such cases are filtered)
    bound: i32,
) -> Vec<Vec<usize>> {
    // solution already computed
    #[allow(clippy::map_entry)]
    if solutions.contains_key(&bound) {
        solutions.get(&bound).unwrap().to_vec()
    }
    // trivial bound
    else if bound == 0 {
        solutions.insert(bound, vec![]);
        vec![]
    } else {
        let (mut opt_solution, mut opt_value) = (Vec::new(), usize::MAX);
        // iterate over all possibile pairs
        for parallel_lookups in 1..=max_parallel_lookups {
            for bit_length in (1..=max_bit_length).rev() {
                let next_bound = bound - (bit_length * parallel_lookups) as i32;
                if next_bound >= 0 {
                    // compute the optimal solution of the next problem
                    let mut sol = compute_optimal_limb_sizes(
                        solutions,
                        max_parallel_lookups,
                        max_bit_length,
                        next_bound,
                    );
                    // add one vector for what is left
                    sol.push(vec![bit_length; parallel_lookups]);
                    // if the solution is shorter than the current best, update the optimial
                    // solution and its value
                    if sol.len() < opt_value {
                        opt_value = sol.len();
                        opt_solution = sol;
                    }
                }
            }
        }
        solutions.insert(bound, opt_solution.clone());
        opt_solution
    }
}

#[cfg(test)]
mod tests {

    use std::collections::HashMap;

    use itertools::Itertools;
    use num_bigint::BigInt;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::{compute_optimal_limb_sizes, decompose_in_variable_limbsizes};
    use crate::{
        CircuitField, field::decomposition::cpu_utils::variable_limbsize_coefficients,
        utils::util::bigint_to_fe,
    };

    /// Original (BigInt based) implementation of
    /// [decompose_in_variable_limbsizes].
    fn decompose_reference<InF: CircuitField, OutF: CircuitField>(
        x: &InF,
        limb_sizes: &[usize],
    ) -> Vec<OutF> {
        let x: BigInt = x.to_biguint().into();
        let mut shift = 0;
        limb_sizes
            .iter()
            .map(|&size| {
                let mask = (BigInt::from(1) << size) - 1;
                let limb = bigint_to_fe(&((&x >> shift) & mask));
                shift += size;
                limb
            })
            .collect()
    }

    /// Original (BigInt based) implementation of
    /// [variable_limbsize_coefficients].
    fn coefficients_reference<F: CircuitField>(limb_sizes: &[usize]) -> Vec<F> {
        let mut shift = 0;
        limb_sizes
            .iter()
            .map(|&size| {
                let coeff = if size == 0 {
                    BigInt::from(0)
                } else {
                    BigInt::from(1) << shift
                };
                shift += size;
                bigint_to_fe(&coeff)
            })
            .collect()
    }

    /// Limb-size lists, including ones that straddle byte boundaries, covering
    /// at least `nb_bits` bits.
    fn limb_size_lists(nb_bits: usize) -> Vec<Vec<usize>> {
        let mut lists: Vec<Vec<usize>> = vec![vec![], vec![0], vec![1], vec![0, 0, 3, 0]];
        for size in [1usize, 7, 8, 9, 63, 64] {
            lists.push(vec![size; nb_bits.div_ceil(size)]);
        }
        lists.push([7, 9, 1, 0, 8, 63, 64, 5].repeat(nb_bits.div_ceil(157)));
        lists.push([3, 13, 64, 2, 0, 31].repeat(nb_bits.div_ceil(113)));
        lists
    }

    fn check_decomposition<F: CircuitField, OutF: CircuitField>() {
        let mut rng = ChaCha8Rng::seed_from_u64(0xdec0);
        let nb_bits = F::NUM_BITS as usize;
        let mut values = vec![F::ZERO, F::ONE, -F::ONE, -F::from(2), F::from(u64::MAX)];
        values.extend((0..30).map(|_| F::random(&mut rng)));
        // Values near the modulus.
        values.extend((1..=10u64).map(|i| -F::from(i)));
        // Values with a single high bit set.
        values.extend((0..nb_bits).step_by(13).map(|b| F::from(2).pow_vartime([b as u64])));

        for limb_sizes in limb_size_lists(nb_bits) {
            assert_eq!(
                variable_limbsize_coefficients::<OutF>(&limb_sizes),
                coefficients_reference::<OutF>(&limb_sizes),
                "{limb_sizes:?}"
            );
            for x in &values {
                assert_eq!(
                    decompose_in_variable_limbsizes::<F, OutF>(x, &limb_sizes),
                    decompose_reference::<F, OutF>(x, &limb_sizes),
                    "{limb_sizes:?}"
                );
            }
        }
    }

    #[test]
    fn decomposition_matches_reference() {
        use midnight_curves::{Fp, Fq, k256, p256};
        check_decomposition::<Fq, Fq>();
        check_decomposition::<Fp, Fq>();
        check_decomposition::<k256::Fp, Fq>();
        check_decomposition::<p256::Fq, Fq>();
        check_decomposition::<Fq, Fp>();
    }

    /// The coefficients stay correct for limb sizes beyond 64 and 128 bits.
    #[test]
    fn coefficients_with_large_limb_sizes() {
        use midnight_curves::Fq;
        let sizes = [1, 64, 65, 127, 128, 129, 200, 3];
        assert_eq!(
            variable_limbsize_coefficients::<Fq>(&sizes),
            coefficients_reference::<Fq>(&sizes)
        );
    }

    /// function that returns true iff bit_size can be writen in the form
    /// [x1, x1, ..., x1, 0, 0, ..., 0]
    /// [x2, x2, ..., x2, 0, 0, ..., 0]
    ///             :
    ///             :
    /// [xk, xk, ..., xk, 0, 0, ..., 0]
    ///
    /// where
    /// - k < optimal_value
    /// - xi \in [1, max_bit_length]
    /// - the sum of the given elements equals `bit_size`
    fn limb_sizes_is_optimal(
        bound: usize,
        max_parallel_lookups: usize,
        max_bit_length: usize,
        optimal_value: usize,
    ) -> bool {
        // create all vectors of the form [a,a,..,a,0,..0]
        // - 1..=max_bit_length selects the xi
        // - 1..=max_parallel_lookups selects how many xi's exists in the row
        let mut possible_rows = (1..=max_bit_length)
            .cartesian_product(1..=max_parallel_lookups)
            .map(|(x, how_many)| vec![x; how_many])
            .collect::<Vec<_>>();
        // we add the zero row as well to consider the case where we can decompose in
        // less than optimal_value - 1 rows
        possible_rows.push(vec![0]);

        // take all possible combinations and try to find one that yields
        // a correct decomposition
        possible_rows
            .into_iter()
            .combinations(optimal_value - 1)
            .map(|solution| solution.iter().flatten().sum::<usize>())
            .all(|x| x != bound)
    }

    #[test]
    fn test_limb_size_decomposition_optimality() {
        let mut opt_limbs = HashMap::new();
        let max_parallel_lookups = 4usize;
        let max_bit_length = 8usize;

        for bound in 1..=128 {
            let opt = compute_optimal_limb_sizes(
                &mut opt_limbs,
                max_parallel_lookups,
                max_bit_length,
                bound as i32,
            )
            .len();
            assert!(limb_sizes_is_optimal(
                bound,
                max_parallel_lookups,
                max_bit_length,
                opt
            ));
        }
    }
}

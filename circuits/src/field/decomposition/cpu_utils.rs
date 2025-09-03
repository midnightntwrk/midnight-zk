// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

use ff::PrimeField;
use num_bigint::BigInt;

use crate::utils::util::{bigint_to_fe, fe_to_bigint};

/// Decomposes an element of the input field into limbs of variable sizes and
/// each limb is in the output field: given x\in InF and a slice limb_sizes that
/// represents bit lengths, it returns [a_1, ..., a_m] such that:      
///      (1) x = sum c_i a_i
///      (2) a_i < 2^{limbs_size{i}}
///      (3) c_i = 2^{sum_{j=1}^{i-1} limb_sizes\[i\]}
///      (4) a_i in OutF
///
/// # Panics
///
/// Panics if the field element cannot be represented with limb_sizes
pub(crate) fn decompose_in_variable_limbsizes<InF: PrimeField, OutF: PrimeField>(
    x: &InF,
    limb_sizes: &[usize],
) -> Vec<OutF> {
    // convert the given number to bigint for efficient bitwise operations
    let x: BigInt = fe_to_bigint(x);

    // vector to keep the result
    let mut limbs: Vec<OutF> = Vec::with_capacity(limb_sizes.len());

    // each time we shift the mask to "extract" the correct bits. This variable
    // holds the next shift
    let mut shift = 0;

    for limb_size in limb_sizes {
        // compute the mask vector i.e. 111..1 (limb_size ones)
        // NOTE: when the limb_size is 0 he mask will always be 0
        let mask_bits: u64 = (1 << limb_size) - 1;
        let mask = BigInt::from(mask_bits);

        // right shift the number and perform an and operation to take the limb
        let limb_int = (x.clone() >> shift) & mask;
        let limb = bigint_to_fe(&limb_int);
        limbs.push(limb);

        // update shift to get the next limb
        shift += limb_size;
    }

    // sanity check. Panics if the limbs are not enough to represent the number
    #[cfg(not(test))]
    debug_assert_eq!(
        x.clone() >> shift,
        0.into(),
        "Decomposition Chip: the integer cannot be represented with the given limb_sizes"
    );

    limbs
}

/// Compute the fixed coefficients when decomposing with variable limbs
/// (see [decompose_in_variable_limbsizes])
///
/// Given a slice limbs_sizes this corresponds to
/// - c_i = 2^{sum_{j=1}^{i-1} limb_sizes\[i\]} if limb_sizes\[i\] > 0
/// - 0 if limb_sizes=0
pub(super) fn variable_limbsize_coefficients<F: PrimeField>(limb_sizes: &[usize]) -> Vec<F> {
    // vector to keep the result
    let mut coefficients = Vec::with_capacity(limb_sizes.len());

    // each time we shift the mask to "extract" the correct bits. This variable
    // holds the next shift
    let mut shift = 0;
    for limb_size in limb_sizes {
        // by convenion we return the zero coefficient when we have a trivial limb size
        if *limb_size == 0 {
            coefficients.push(BigInt::from(0));
        } else {
            // the coefficient in this case corresponds to 2^shift
            coefficients.push(BigInt::from(1) << shift);
        }
        shift += limb_size;
    }
    // convert to field elements and return the result
    coefficients.iter().map(|x| bigint_to_fe(x)).collect()
}

/// Helper function to fill the limb sizes with trivial ones, i.e. zeros
pub(super) fn process_limb_sizes(max_parallel_lookups: usize, limbs: &mut Vec<usize>) {
    while limbs.len() % max_parallel_lookups != 0 {
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
pub(super) fn compute_optimal_limb_sizes(
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
        return vec![];
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

    use super::compute_optimal_limb_sizes;

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

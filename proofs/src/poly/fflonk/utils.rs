//! Helpers of the fflonk scheme: the split of a group into chunks, the
//! combination `g` of a chunk and the roots it is opened at.

use std::{
    collections::{HashMap, hash_map::Entry},
    hash::Hash,
    iter,
    marker::PhantomData,
};

use ff::PrimeField;

use crate::poly::{Coeff, Polynomial};

/// The chunks of a group of `items`: the fewest chunks of at most `t_max`
/// items, `⌈items.len() / t_max⌉`, of sizes that differ by at most one, the
/// larger ones first, each a run of consecutive items.
pub fn balanced_chunks<T>(items: &[T], t_max: usize) -> impl Iterator<Item = &[T]> {
    let nb_chunks = items.len().div_ceil(t_max);
    let (size, nb_larger) = match nb_chunks {
        0 => (0, 0),
        _ => (items.len() / nb_chunks, items.len() % nb_chunks),
    };
    (0..nb_chunks).scan(items, move |rest, i| {
        let (chunk, tail) = rest.split_at(size + usize::from(i < nb_larger));
        *rest = tail;
        Some(chunk)
    })
}

/// `g(X) = Σ_i X^i f_i(X^t)`, for `polys` the polynomials `f_0, ..., f_{k-1}`
/// in coefficient form and `t` the next power of two of `k`: the coefficients
/// of `g` interleave those of the `f_i`, with the slots of the `t - k` dummy
/// polynomials padding the `k` given ones to `t` left zero.
pub(super) fn compute_g<F: PrimeField>(polys: &[&Polynomial<F, Coeff>]) -> Polynomial<F, Coeff> {
    let t = polys.len().next_power_of_two();
    let n = polys.iter().map(|poly| poly.len()).max().unwrap_or(0);
    let mut values = vec![F::ZERO; t * n];
    for (i, poly) in polys.iter().enumerate() {
        for (j, coeff) in poly.values.iter().enumerate() {
            values[t * j + i] = *coeff;
        }
    }
    Polynomial {
        values,
        _marker: PhantomData,
    }
}

/// The `t`-th roots of `x`, for a power of two `t`.
///
/// Returns `None` if `x` is not a `t`-th power. Since the field has roots of
/// unity of order `t`, if `x` has a `t`-th root then it has all `t` of them.
///
/// # Panics
///
/// Panics if `t` is not a power of two, or if `F` has no roots of unity of
/// order `t`.
pub fn roots<F: PrimeField>(x: F, t: usize) -> Option<Vec<F>> {
    assert!(
        t.is_power_of_two(),
        "fflonk roots of order {t}, not a power of two"
    );
    let log_t = t.trailing_zeros();
    assert!(
        log_t <= F::S,
        "the field has no roots of unity of order {t}"
    );
    let mut root = x;
    for _ in 0..log_t {
        root = Option::from(root.sqrt())?;
    }
    let omega = F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - log_t)]);
    Some(iter::successors(Some(root), |r| Some(*r * omega)).take(t).collect())
}

/// [`roots`] of `x`, computed once per `x` and `t` and kept in `cache`.
pub(super) fn cached_roots<F: PrimeField + Hash>(
    cache: &mut HashMap<(F, usize), Vec<F>>,
    x: F,
    t: usize,
) -> Option<&[F]> {
    Some(match cache.entry((x, t)) {
        Entry::Occupied(entry) => entry.into_mut(),
        Entry::Vacant(entry) => entry.insert(roots(x, t)?),
    })
}

#[cfg(test)]
mod tests {
    use super::balanced_chunks;

    #[test]
    fn test_balanced_chunks() {
        let sizes = |len: usize, t_max: usize| {
            let items: Vec<usize> = (0..len).collect();
            let chunks: Vec<_> = balanced_chunks(&items, t_max).collect();
            assert_eq!(chunks.concat(), items);
            chunks.iter().map(|chunk| chunk.len()).collect::<Vec<_>>()
        };
        assert_eq!(sizes(17, 8), [6, 6, 5]);
        assert_eq!(sizes(49, 8), [7; 7]);
        assert_eq!(sizes(12, 8), [6, 6]);
        assert_eq!(sizes(5, 8), [5]);
        assert_eq!(sizes(8, 4), [4, 4]);
        assert_eq!(sizes(0, 8), Vec::<usize>::new());
        for len in 0..100 {
            for t_max in [1, 2, 4, 8, 16] {
                let sizes = sizes(len, t_max);
                assert_eq!(sizes.len(), len.div_ceil(t_max));
                assert!(sizes.iter().all(|&size| 0 < size && size <= t_max));
                assert!(sizes.windows(2).all(|w| w[0] >= w[1] && w[0] - w[1] <= 1));
            }
        }
    }
}

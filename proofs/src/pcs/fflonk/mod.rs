//! fflonk-style polynomial commitment scheme ([reference](https://eprint.iacr.org/2021/1167.pdf)).
//!
//! Packs groups of `t` polynomials of degree `< n` into a single polynomial `g`
//! of degree `< t·n` via `g(X) = Σ_i X^i · f_i(X^t)`, commits once to `g`, and
//! opens at the `t` t-th roots of each logical query point.
//!
//! # Layout
//! - `math`: the curve-free fflonk paper math (`combine`, roots, ...).
//! - `partition`: the deterministic bundling policy.
//! - `commitment`: the `FflonkCommitment` type and its wire format.
//! - `bundle_expansion`: multi-open bundle pre-expansion.
//!
//! # Implementation
//! `commit_many` bundles via `partition::partition`. For each bundle of size
//! `t > 1` it builds `g(X) = Σ_i X^i · f_i(X^t)` from the `f_i` converted to
//! coefficient form; singleton bundles are committed in whichever basis they
//! were given.
//!
//! `multi_open` / `multi_prepare` pre-expand bundled queries into synthetic
//! queries on `g` at the `t`-th roots of each distinct logical opening point,
//! which is the characterisation of Lemma 5.1 of the paper (see
//! `eval_claims_as_poly`). The expansion is the only fflonk-specific phase;
//! everything downstream is the standard Halo2 multi-open argument, shared with
//! KZG through `multi_open_core`.
//!
//! # Protocol invariant
//! All polynomials of one bundlable family must be committed in a single
//! `commit_many` call: `multi_open` re-derives the bundles by partitioning the
//! labels it is queried on, and that partition has to reproduce the one used at
//! commit time. A prover violating this opens polynomials the commitments do
//! not contain, which the final pairing check rejects.
//!
//! TODO: for now, computing `g` is only possible if each `f_i` is in
//! coefficient form; `commit_many` converts otherwise. Native support for the
//! other bases will be implemented in the future.

pub mod commitment;

mod partition;

pub use commitment::FflonkCommitment;

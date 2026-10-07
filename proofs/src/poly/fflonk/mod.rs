//! fflonk over a generic inner polynomial commitment scheme.
//!
//! Let `t` be a power of two. fflonk commits to a group of polynomials
//! `f_0, ..., f_{t-1}` of degree < `n` by committing to a meta polynomial:
//!
//! ```text
//! g(X) = Σ_i X^i f_i(X^t)
//! ```
//!
//! with the inner PCS commitment scheme. Note that `g` has degree < `t · n`.
//!
//! In order to "open" the committed polynomials `f_i` at evaluation point `x`,
//! we open `g` at the `t`-th roots of `x` instead. From the evaluations of `g`
//! at such roots, one can recompute (univocally) the evaluations of `f_i` at
//! `x`. Note that for every root `r`:
//!
//! ```text
//! g(r) = Σ_i r^i f_i(x)
//! ```
//!
//! which gives a Vandermonde system of `t` equations. Conversely, the verifier,
//! given the evaluations of the `f_i` at `x`, computes those of `g` at the
//! roots and checks them with the inner PCS.
//!
//! # Notes
//!
//! - The verifier needs every `f_i(x)`, so the evaluations at `x` of the `f_i`
//!   not queried at `x` are written to the proof.
//!
//! - A group of `k` polynomials, for `k` not a power of two, is padded with
//!   dummy polynomials up to the next power of two `t`.
//!
//! - The degree of `g` grows with `t`, so `t` is bounded by `T_MAX`: the
//!   polynomials of a `commit_many` call are split into chunks of at most
//!   `T_MAX` polynomials.

mod utils;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, hash_map::Entry},
    hash::Hash,
    io::{self, Read},
    marker::PhantomData,
    slice,
};

use ff::WithSmallOrderMulGroup;
use utils::{compute_g, roots};

use crate::{
    poly::{
        Error, Polynomial, PolynomialLabel,
        PolynomialLabel::Collection,
        PolynomialRepresentation, ProverQuery, VerifierQuery,
        commitment::{Params, PolynomialCommitmentScheme},
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{arithmetic::eval_polynomial, helpers::SerdeFormat},
};

/// fflonk over the polynomial commitment scheme `PCS`.
///
/// The polynomials of a `commit_many` call are combined in chunks of at most
/// `T_MAX = 2^LOG2_T_MAX`.
#[derive(Clone, Debug)]
pub struct Fflonk<PCS, const LOG2_T_MAX: u32>(PhantomData<PCS>);

impl<PCS, const LOG2_T_MAX: u32> Fflonk<PCS, LOG2_T_MAX> {
    /// The maximum number of polynomials combined into one.
    const T_MAX: usize = 1 << LOG2_T_MAX;
}

impl<F, PCS, const LOG2_T_MAX: u32> PolynomialCommitmentScheme<F> for Fflonk<PCS, LOG2_T_MAX>
where
    F: WithSmallOrderMulGroup<3>,
    PCS: PolynomialCommitmentScheme<F>,
{
    type Parameters = PCS::Parameters;
    type VerifierParameters = PCS::VerifierParameters;
    type Commitment = PCS::Commitment;
    type VerificationGuard = PCS::VerificationGuard;

    fn gen_params(k: u32) -> Self::Parameters {
        let mut params = PCS::gen_params(k + LOG2_T_MAX);
        params.downsize_lagrange(k);
        params
    }

    fn load_params<R: io::Read>(
        reader: &mut R,
        format: SerdeFormat,
        k: u32,
    ) -> io::Result<Self::Parameters> {
        let mut params = PCS::load_params(reader, format, k + LOG2_T_MAX)?;
        params.downsize_lagrange(k);
        Ok(params)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        PCS::get_verifier_params(params)
    }

    fn commit_many<B: PolynomialRepresentation>(
        params: &Self::Parameters,
        polynomials: &[&Polynomial<F, B>],
        labels: &[PolynomialLabel],
    ) -> Self::Commitment {
        PolynomialLabel::assert_distinct(labels);
        let g_labels: Vec<_> = labels.chunks(Self::T_MAX).map(|l| Collection(l.to_vec())).collect();
        let gs: Vec<_> = polynomials.chunks(Self::T_MAX).map(compute_g).collect();
        PCS::commit_many(params, &gs.iter().collect::<Vec<_>>(), &g_labels)
    }

    fn read_commitment<T: Transcript>(
        transcript: &mut T,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        PolynomialLabel::assert_distinct(labels);
        let g_labels: Vec<_> = labels.chunks(Self::T_MAX).map(|l| Collection(l.to_vec())).collect();
        PCS::read_commitment(transcript, &g_labels)
    }

    fn write_commitment<T: Transcript>(
        transcript: &mut T,
        commitment: &Self::Commitment,
    ) -> io::Result<()>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        PCS::write_commitment(transcript, commitment)
    }

    fn deserialize_commitment<R: Read>(
        reader: &mut R,
        format: SerdeFormat,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment> {
        PolynomialLabel::assert_distinct(labels);
        let g_labels: Vec<_> = labels.chunks(Self::T_MAX).map(|l| Collection(l.to_vec())).collect();
        PCS::deserialize_commitment(reader, format, &g_labels)
    }

    fn squeeze_evaluation_point<T: Transcript>(transcript: &mut T) -> F
    where
        F: Sampleable<T::Hash>,
    {
        PCS::squeeze_evaluation_point(transcript).pow_vartime([Self::T_MAX as u64])
    }

    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        queries: &[ProverQuery<F>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>,
    {
        // Maps the labels of every queried chunk to its polynomials and the
        // points they are queried at: `labels -> (polys, points)`.
        let chunks_info = queries.iter().fold(BTreeMap::new(), |mut chunks_info, q| {
            let (labels, polys) =
                (q.group_labels.chunks(Self::T_MAX).zip(q.group_polys.chunks(Self::T_MAX)))
                    .find(|(labels, _)| labels.contains(&q.label))
                    .expect("the queried group has no polynomial under the query label");
            let (_, points) = (chunks_info.entry(labels))
                .or_insert_with(|| (polys.iter().collect::<Vec<_>>(), BTreeSet::new()));
            points.insert(q.point);
            chunks_info
        });

        // fflonk requires that every polynomial of a chunk be queried at every point of
        // the chunk. We compute the missing evaluations (those that were not queried)
        // and write them to the transcript. Note that the evaluations of explicit
        // queries are expected to be in the transcript before the call to `multi_open`.
        let queried: HashSet<_> = queries.iter().map(|q| (q.label.clone(), q.point)).collect();
        for (labels, (polys, points)) in &chunks_info {
            for point in points {
                for (label, poly) in labels.iter().zip(polys.iter()) {
                    if !queried.contains(&(label.clone(), *point)) {
                        let eval = eval_polynomial(poly, *point);
                        transcript.write(&eval).map_err(|_| Error::OpeningError)?;
                    }
                }
            }
        }

        // Compute g for every chunk as in `commit_many`. This step needs to be
        // performed again, since the PCS is stateless, but it is cheap here.
        let g_labels: Vec<_> = chunks_info.keys().map(|l| [Collection(l.to_vec())]).collect();
        let gs: Vec<_> = chunks_info.values().map(|(polys, _)| compute_g(polys)).collect();

        // Opening a chunk at `x` amounts to opening its `g` at the `t`-th roots of `x`.
        let mut inner_queries = Vec::new();
        for (((polys, points), g_label), g) in chunks_info.values().zip(&g_labels).zip(&gs) {
            for x in points {
                for root in roots(*x, polys.len().next_power_of_two()).ok_or(Error::OpeningError)? {
                    let g_poly = slice::from_ref(g);
                    inner_queries.push(ProverQuery::new(g_label, g_poly, root, g_label[0].clone()));
                }
            }
        }

        PCS::multi_open(params, &inner_queries, transcript)
    }

    fn commitment_labels(commitment: &Self::Commitment) -> Vec<PolynomialLabel> {
        PCS::commitment_labels(commitment)
            .into_iter()
            .flat_map(|label| match label {
                Collection(labels) => labels,
                label => panic!("fflonk commitment tagged with {label}, not a collection"),
            })
            .collect()
    }

    fn commitment_byte_length(n: usize) -> usize {
        PCS::commitment_byte_length(n.div_ceil(Self::T_MAX))
    }

    fn multi_prepare<'com, T: Transcript>(
        queries: &[VerifierQuery<'com, F, Self>],
        k: u32,
        transcript: &mut T,
    ) -> Result<Self::VerificationGuard, Error>
    where
        F: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash> + 'com,
    {
        // Maps the labels of every queried chunk to its commitment and the
        // points its polynomials are queried at: `labels -> (commitment, points)`.
        let chunks_info = queries.iter().fold(BTreeMap::new(), |mut chunks_info, q| {
            let labels = (Self::commitment_labels(q.commitment).chunks(Self::T_MAX))
                .find(|labels| labels.contains(&q.label))
                .map_or_else(|| vec![q.label.clone()], <[_]>::to_vec);
            let (_, points) = chunks_info.entry(labels).or_insert((q.commitment, BTreeSet::new()));
            points.insert(q.point);
            chunks_info
        });

        // The evaluations of the chunks at all the points, both the explicit (taken
        // from the queries) and the implicit (read from the transcript here) ones.
        let mut evals: HashMap<(PolynomialLabel, F), F> =
            queries.iter().map(|q| ((q.label.clone(), q.point), q.eval)).collect();
        for (labels, (_, points)) in &chunks_info {
            for point in points {
                for label in labels {
                    if let Entry::Vacant(entry) = evals.entry((label.clone(), *point)) {
                        entry.insert(transcript.read().map_err(|_| Error::SamplingError)?);
                    }
                }
            }
        }

        // Opening a chunk at `x` amounts to opening its `g` polynomial at
        // the `t`-th roots of `x`, where computing `g(r) = Σ_i r^i f_i(x)` for
        // such a root `r` is equivalent to evaluating at `r` the polynomial with
        // coefficients `f_i(x)`.
        let mut inner_queries = Vec::new();
        for (labels, (commitment, points)) in &chunks_info {
            for x in points {
                let f_evals: Vec<F> = labels.iter().map(|l| evals[&(l.clone(), *x)]).collect();
                for root in
                    roots(*x, labels.len().next_power_of_two()).ok_or(Error::OpeningError)?
                {
                    let eval = eval_polynomial(&f_evals, root);
                    let label = Collection(labels.clone());
                    inner_queries.push(VerifierQuery::new(root, *commitment, label, eval));
                }
            }
        }

        PCS::multi_prepare(&inner_queries, k, transcript)
    }
}

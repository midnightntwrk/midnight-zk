//! The multi-point opening argument, shared by every scheme built on a
//! KZG-style SRS.
//!
//! Refer to the [Halo 2 Book](https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html)
//! for the argument itself.
//!
//! A scheme's `multi_open` / `multi_prepare` is its own query expansion
//! followed by a call into this module: KZG opens the queries it is given,
//! while fflonk first replaces bundled queries with synthetic ones on the
//! bundle's combined polynomial. Everything from the first squeezed challenge
//! onwards is identical, and lives here.

use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData};

use ff::{Field, PrimeField};
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

#[cfg(feature = "truncated-challenges")]
use crate::utils::arithmetic::{truncate, truncated_powers};
use crate::{
    pcs::{
        PolynomialCommitmentScheme,
        kzg::commitment::KZGCommitment,
        msm::{DualMSM, MSMKZG},
        utils::construct_intermediate_sets,
    },
    poly::{Coeff, Error, Polynomial, ProverQuery, query::PolynomialLabel},
    transcript::{Hashable, Sampleable, Transcript},
    utils::arithmetic::{
        CurveAffine, CurveExt, MSM, eval_polynomial, evals_inner_product, inner_product,
        kate_division, lagrange_interpolate, parallelize, powers,
    },
};

/// Label carried by the batch commitment `f`. Never serialized, so its value
/// is cosmetic.
const BATCH_LABEL: &str = "multi_open_batch";

/// Label carried by the opening proof `π`. Never serialized, so its value is
/// cosmetic.
const PROOF_LABEL: &str = "multi_open_proof";

/// Like [`inner_product`] but for coefficient-form polynomials that may
/// have different lengths (zero-extending the shorter operands).
///
/// Fused parallel implementation: a single pass accumulates all
/// scaled contributions directly into the output buffer, avoiding
/// M intermediate allocations and the sequential reduce chain.
fn poly_inner_product<F: PrimeField>(
    polys: &[&Polynomial<F, Coeff>],
    scalars: impl IntoIterator<Item = F>,
) -> Polynomial<F, Coeff> {
    let scalars: Vec<F> = scalars.into_iter().take(polys.len()).collect();
    let max_len = polys.iter().map(|p| p.len()).max().unwrap_or(0);
    let mut values = vec![F::ZERO; max_len];
    parallelize(&mut values, |chunk, start| {
        for (poly, scalar) in polys.iter().zip(scalars.iter()) {
            let pv: &[F] = poly;
            let end = (start + chunk.len()).min(pv.len());
            if start < pv.len() {
                for (out, coeff) in chunk[..end - start].iter_mut().zip(&pv[start..end]) {
                    *out += *coeff * scalar;
                }
            }
        }
    });
    Polynomial {
        values,
        _marker: PhantomData,
    }
}

/// Sort point sets by ascending cardinality, so the first set is the one
/// holding commitments evaluated at a single point (the fixed ones). Not
/// needed by the proving system itself, but the in-circuit verifier relies on
/// it for a collapse optimization.
///
/// The `(len, i)` key gives a deterministic total order when two sets share a
/// cardinality.
fn point_set_order<F>(point_sets: &[Vec<F>]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..point_sets.len()).collect();
    order.sort_by_key(|&i| (point_sets[i].len(), i));
    order
}

/// Prove that the polynomials behind `queries` take the claimed values at the
/// claimed points, writing the argument to `transcript`.
///
/// Callers are responsible for any scheme-specific expansion of `queries`
/// (fflonk's bundle expansion, the `fewer-point-sets` dummy queries) before
/// handing them over.
pub(crate) fn multi_open_core<F, CS, T>(
    params: &CS::Parameters,
    queries: &[ProverQuery<F>],
    transcript: &mut T,
) -> Result<(), Error>
where
    F: PrimeField + Hash + Ord + Sampleable<T::Hash> + Hashable<T::Hash>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    let x1: F = transcript.squeeze_challenge();
    let x2: F = transcript.squeeze_challenge();

    // Map each label to the polynomial it identifies, so the per-set
    // grouping (keyed by label) can recover the actual polynomials.
    let label_to_poly: HashMap<PolynomialLabel, &Polynomial<F, Coeff>> =
        queries.iter().map(|q| (q.label.clone(), q.poly)).collect();

    let triples = queries
        .iter()
        .map(|query| {
            (
                query.label.clone(),
                query.point,
                eval_polynomial(&query.poly[..], query.point),
            )
        })
        .collect::<Vec<_>>();
    let (poly_map, point_sets) = construct_intermediate_sets(&triples)?;

    let mut q_polys = vec![vec![]; point_sets.len()];

    for com_data in poly_map.iter() {
        q_polys[com_data.set_index].push(label_to_poly[&com_data.label]);
    }

    let q_polys: Vec<_> = q_polys
        .par_iter()
        .map(|polys| {
            #[cfg(feature = "truncated-challenges")]
            let x1 = truncated_powers(x1);

            #[cfg(not(feature = "truncated-challenges"))]
            let x1 = powers(x1);

            poly_inner_product(polys, x1)
        })
        .collect();

    let (q_polys, point_sets) = {
        let order = point_set_order(&point_sets);
        let q_polys: Vec<_> = order.iter().map(|&i| &q_polys[i]).collect();
        let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
        (q_polys, point_sets)
    };

    let f_poly = {
        let f_polys: Vec<_> = point_sets
            .into_par_iter()
            .zip(q_polys.clone().into_par_iter())
            .map(|(points, q_poly)| {
                let poly = points.iter().fold(q_poly.values.clone(), |poly, point| {
                    kate_division(&poly, *point)
                });
                Polynomial {
                    values: poly,
                    _marker: PhantomData,
                }
            })
            .collect();
        poly_inner_product(&f_polys.iter().collect::<Vec<_>>(), powers(x2))
    };

    let f_com = CS::commit(params, &f_poly, PolynomialLabel::Custom(BATCH_LABEL.into()));
    transcript.write(&f_com).map_err(|_| Error::OpeningError)?;

    let x3: F = transcript.squeeze_challenge();
    #[cfg(feature = "truncated-challenges")]
    let x3 = truncate(x3);

    // Evaluate all q_polys at x3 in parallel, then write sequentially.
    let q_evals: Vec<F> =
        q_polys.par_iter().map(|q_poly| eval_polynomial(&q_poly.values, x3)).collect();
    for eval in &q_evals {
        transcript.write(eval).map_err(|_| Error::OpeningError)?;
    }

    let x4: F = transcript.squeeze_challenge();

    let final_poly = {
        let mut polys = q_polys;
        polys.push(&f_poly);
        #[cfg(feature = "truncated-challenges")]
        let powers = truncated_powers(x4);

        #[cfg(not(feature = "truncated-challenges"))]
        let powers = powers(x4);

        poly_inner_product(&polys, powers)
    };
    let v = eval_polynomial(&final_poly, x3);

    let pi = {
        let pi_poly = Polynomial::<_, Coeff> {
            values: kate_division(&(&final_poly - v).values, x3),
            _marker: PhantomData,
        };
        CS::commit(
            params,
            &pi_poly,
            PolynomialLabel::Custom(PROOF_LABEL.into()),
        )
    };

    transcript.write(&pi).map_err(|_| Error::OpeningError)
}

/// How a scheme accumulates commitments while batching the opening argument.
///
/// The argument only ever scales commitments and adds them together, then
/// hands the result to the pairing check as an MSM. Expressed as methods
/// rather than operators so that both a lazy commitment and an MSM can play
/// the role.
pub(crate) trait BatchAccumulator<E: MultiMillerLoop + Debug>: Clone {
    /// Wrap a single group element, as read off the transcript.
    fn from_point(point: E::G1, label: PolynomialLabel) -> Self;

    /// Scale the accumulated linear combination by `factor`.
    fn scale(&mut self, factor: E::Fr);

    /// Add `other` into this linear combination.
    fn add(&mut self, other: &Self);

    /// Reduce the accumulated linear combination to a single term.
    #[cfg(feature = "truncated-challenges")]
    fn collapse(&mut self, label: PolynomialLabel);

    /// Convert into the MSM the pairing check consumes.
    fn into_msm(self) -> MSMKZG<E>;
}

impl<E: MultiMillerLoop + Debug> BatchAccumulator<E> for KZGCommitment<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn from_point(point: E::G1, label: PolynomialLabel) -> Self {
        KZGCommitment::Simple(point, label)
    }

    fn scale(&mut self, factor: E::Fr) {
        *self = self.clone() * factor;
    }

    fn add(&mut self, other: &Self) {
        *self = self.clone() + other.clone();
    }

    #[cfg(feature = "truncated-challenges")]
    fn collapse(&mut self, label: PolynomialLabel) {
        KZGCommitment::collapse(self, label)
    }

    fn into_msm(self) -> MSMKZG<E> {
        self.into()
    }
}

// fflonk accumulates directly in MSM space: its commitments are bundles, so the
// per-label sources the argument combines are already MSMs (one term for a
// bundle, several for a linearization commitment).
impl<E: MultiMillerLoop + Debug> BatchAccumulator<E> for MSMKZG<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn from_point(point: E::G1, label: PolynomialLabel) -> Self {
        MSMKZG::new(&[E::Fr::ONE], &[point], &[label])
    }

    fn scale(&mut self, factor: E::Fr) {
        MSM::scale(self, factor)
    }

    fn add(&mut self, other: &Self) {
        MSM::add_msm(self, other)
    }

    #[cfg(feature = "truncated-challenges")]
    fn collapse(&mut self, label: PolynomialLabel) {
        MSMKZG::collapse(self, label)
    }

    fn into_msm(self) -> MSMKZG<E> {
        self
    }
}

/// `sum_i coms[i] * scalars[i]`, in the accumulator's own representation.
fn com_inner_product<E: MultiMillerLoop + Debug, C: BatchAccumulator<E>>(
    coms: &[C],
    scalars: impl IntoIterator<Item = E::Fr>,
) -> C {
    let mut terms = coms.iter().zip(scalars).map(|(com, scalar)| {
        let mut com = com.clone();
        com.scale(scalar);
        com
    });
    let mut acc = terms.next().expect("empty inner product");
    for term in terms {
        acc.add(&term);
    }
    acc
}

/// Check the multi-point opening argument written by [`multi_open_core`],
/// returning the pairing accumulator to be verified.
///
/// `triples` are the `(label, point, eval)` claims after any scheme-specific
/// expansion, and `label_to_com` resolves each label to the commitment it
/// refers to. `read_point` reads one of the argument's two group elements off
/// the transcript; it is a parameter because each scheme serializes its
/// commitments differently, and both reads have to land at these exact points
/// of the transcript.
pub(crate) fn multi_prepare_core<E, C, T>(
    triples: &[(PolynomialLabel, E::Fr, E::Fr)],
    label_to_com: &HashMap<PolynomialLabel, C>,
    transcript: &mut T,
    read_point: impl Fn(&mut T) -> Result<E::G1, Error>,
) -> Result<DualMSM<E>, Error>
where
    E: MultiMillerLoop + Debug,
    E::Fr: PrimeField + Hash + Ord + Sampleable<T::Hash> + Hashable<T::Hash>,
    E::G1: CurveExt<ScalarExt = E::Fr>,
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    C: BatchAccumulator<E>,
    T: Transcript,
{
    let x1: E::Fr = transcript.squeeze_challenge();
    let x2: E::Fr = transcript.squeeze_challenge();

    let (commitment_map, point_sets) = construct_intermediate_sets(triples)?;

    let mut q_coms: Vec<Vec<C>> = vec![vec![]; point_sets.len()];
    let mut q_eval_sets = vec![vec![]; point_sets.len()];

    for com_data in commitment_map.into_iter() {
        let com = label_to_com
            .get(&com_data.label)
            .cloned()
            .expect("multi_prepare: no commitment registered for label");
        q_coms[com_data.set_index].push(com);
        q_eval_sets[com_data.set_index].push(com_data.evals);
    }

    let nb_x1_powers = q_coms.iter().map(Vec::len).max().unwrap_or(0);
    assert!(nb_x1_powers >= q_eval_sets.iter().map(Vec::len).max().unwrap_or(0));

    #[cfg(feature = "truncated-challenges")]
    let powers_x1 = truncated_powers(x1).take(nb_x1_powers).collect::<Vec<_>>();

    #[cfg(not(feature = "truncated-challenges"))]
    let powers_x1 = powers(x1).take(nb_x1_powers).collect::<Vec<_>>();

    let q_coms = q_coms
        .into_iter()
        .map(|coms| com_inner_product::<E, C>(&coms, powers_x1.clone()))
        .collect::<Vec<_>>();

    let q_eval_sets = q_eval_sets
        .iter()
        .map(|evals| evals_inner_product(evals, &powers_x1))
        .collect::<Vec<_>>();

    let (q_coms, q_eval_sets, point_sets) = {
        let order = point_set_order(&point_sets);
        let q_coms: Vec<_> = order.iter().map(|&i| q_coms[i].clone()).collect();
        let q_eval_sets: Vec<_> = order.iter().map(|&i| q_eval_sets[i].clone()).collect();
        let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
        (q_coms, q_eval_sets, point_sets)
    };

    let f_point = read_point(transcript)?;
    let f_com = C::from_point(f_point, PolynomialLabel::Custom(BATCH_LABEL.into()));

    // Sample a challenge x_3 for checking that f(X) was committed to correctly.
    let x3: E::Fr = transcript.squeeze_challenge();
    #[cfg(feature = "truncated-challenges")]
    let x3 = truncate(x3);

    let mut q_evals_on_x3 = Vec::<E::Fr>::with_capacity(q_eval_sets.len());
    for _ in 0..q_eval_sets.len() {
        q_evals_on_x3.push(transcript.read().map_err(|_| Error::SamplingError)?);
    }

    // We can compute the expected msm_eval at x_3 using the u provided
    // by the prover and from x_2
    let f_eval = point_sets.iter().zip(q_eval_sets.iter()).zip(q_evals_on_x3.iter()).rev().fold(
        E::Fr::ZERO,
        |acc_eval, ((points, evals), proof_eval)| {
            let r_poly = lagrange_interpolate(points, evals);
            let r_eval = eval_polynomial(&r_poly, x3);
            // eval = (proof_eval - r_eval) / prod_i (x3 - point_i)
            let den = points.iter().fold(E::Fr::ONE, |acc, point| acc * &(x3 - point));
            let eval = (*proof_eval - &r_eval) * den.invert().unwrap();
            acc_eval * &(x2) + &eval
        },
    );

    let x4: E::Fr = transcript.squeeze_challenge();

    let final_com = {
        let size = q_coms.len() + 1;
        let mut coms = q_coms;

        // Collapse all MSMs before combining with x4 powers, to match the
        // in-circuit verifier. Skip the first one since its x4 power is 1.
        #[cfg(feature = "truncated-challenges")]
        coms.iter_mut().skip(1).for_each(|c| c.collapse(PolynomialLabel::NoLabel));
        coms.push(f_com);

        #[cfg(feature = "truncated-challenges")]
        let powers = truncated_powers(x4);

        #[cfg(not(feature = "truncated-challenges"))]
        let powers = powers(x4);

        com_inner_product::<E, C>(&coms, powers.take(size))
    };

    let v = {
        let mut evals = q_evals_on_x3;
        evals.push(f_eval);

        #[cfg(feature = "truncated-challenges")]
        let powers = truncated_powers(x4);

        #[cfg(not(feature = "truncated-challenges"))]
        let powers = powers(x4);

        inner_product(&evals, powers)
    };

    let pi: E::G1 = read_point(transcript)?;

    let mut pi_msm = MSMKZG::<E>::init();
    pi_msm.append_term(E::Fr::ONE, pi, PolynomialLabel::Custom("π".into()));

    // - vG + zπ
    let extra_rhs = MSMKZG::new(
        &[v, x3],
        &[-E::G1::generator(), pi],
        &[
            PolynomialLabel::Custom("-G".into()),
            PolynomialLabel::Custom("π".into()),
        ],
    );

    // (π, C − vG + zπ)
    let mut msm_accumulator = DualMSM {
        left: pi_msm,
        right: final_com.into_msm(),
    };
    msm_accumulator.right.add_msm(&extra_rhs);

    Ok(msm_accumulator)
}

//! Implementation of ProtogalaxyProver that accepts a single round of folding, but
//! produces a succinct final proof.
#![allow(dead_code)]

use std::{hash::Hash, marker::PhantomData, time::Instant};
use std::ops::{Deref, DerefMut};

use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator};

use crate::{
    plonk::{
        compute_queries, compute_trace,
        traces::{FoldingProverTrace, ProverTrace},
        trash, write_evals_to_transcript, Circuit, Error, ProvingKey,
    },
    poly::{
        commitment::PolynomialCommitmentScheme, EvaluationDomain, ExtendedLagrangeCoeff,
        LagrangeCoeff, Polynomial, ProverQuery,
    },
    protogalaxy::{
        utils::linear_combination,
        FoldingPk,
    },
    utils::arithmetic::eval_polynomial,
};
use crate::protogalaxy::utils::LiftedFoldingTrace;

#[derive(Debug)]
/// Protogalaxy prover
pub struct ProtogalaxyProver<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    const K: usize,
> {
    _phantom_data: PhantomData<(F, CS)>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>, const K: usize>
    ProtogalaxyProver<F, CS, K>
{
    /// Fold circuits for the same relation. We assume that circuits.len() is a power of 2.
    pub fn fold<C, T>(
        params: &CS::Parameters,
        pk: ProvingKey<F, CS>,
        circuits: Vec<C>,
        nb_committed_instances: usize,
        instances: &[&[&[F]]],
        mut rng: impl CryptoRng + RngCore,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        C: Circuit<F>,
        T: Transcript,
        CS: PolynomialCommitmentScheme<F>,
        CS::Commitment: Hashable<T::Hash>,
        F: WithSmallOrderMulGroup<3>
            + Sampleable<T::Hash>
            + Hashable<T::Hash>
            + Hash
            + Ord
            + FromUniformBytes<64>,
    {
        assert_eq!(circuits.len(), instances.len());

        let pk_domain_size: usize = pk.vk.get_domain().n as usize;

        let now = Instant::now();
        // TODO: Bunch of optimisations here. We could compute the trace for all
        // circuits at the same time. But the goal eventually is to fold
        // different circuits at a time.

        let traces = circuits
            .into_iter()
            .zip(instances.iter())
            .map(|(c, instance)| {
                let trace = compute_trace(
                    params,
                    &pk,
                    &[c],
                    nb_committed_instances,
                    &[instance],
                    &mut rng,
                    transcript,
                )?;
                Ok(trace.into_folding_trace(pk.fixed_values.clone()))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        println!("Compute traces: {:?}", now.elapsed());
        let traces = traces.iter().collect::<Vec<_>>();

        let beta_pg = transcript.squeeze_challenge();

        let time = Instant::now();
        assert!(traces.len().is_power_of_two());

        // We now perform folding of the traces
        let dk_domain = EvaluationDomain::new(
            pk.vk.cs().folding_degree() as u32,
            traces.len().trailing_zeros(),
        );
        let folding_pk = FoldingPk::from(pk.clone());
        let folding_pk_time = time.elapsed().as_millis();

        // Compute evaluations of lagrange polynomials on beta_pg
        let lagrange_on_beta: Vec<F> = eval_lagrange_on_beta(pk.vk.get_domain(), &beta_pg);
        let lagrange_beta_time = time.elapsed().as_millis() - folding_pk_time;

        let (poly_g, poly_g_unbatched) =
            Self::compute_poly_g(&folding_pk, &dk_domain, &lagrange_on_beta, &traces);
        let poly_g_time = time.elapsed().as_millis() - lagrange_beta_time - folding_pk_time;

        let poly_k = dk_domain.divide_by_vanishing_poly(poly_g.clone());
        let poly_k_coeff = Polynomial {
            values: dk_domain.extended_to_coeff(poly_k),
            _marker: PhantomData,
        };

        transcript.write(&CS::commit(params, &poly_k_coeff))?;
        let k_poly = time.elapsed().as_millis() - poly_g_time - lagrange_beta_time - folding_pk_time;

        let gamma = transcript.squeeze_challenge();

        let k_in_gamma = eval_polynomial(&poly_k_coeff.values, gamma);

        transcript.write(&k_in_gamma)?;

        let error_terms =
            compute_error_terms(pk_domain_size, &dk_domain, &poly_g_unbatched, &gamma);

        // Update error term
        let folded_trace = Self::fold_traces(&dk_domain, &traces, &gamma);
        let rest_time = time.elapsed().as_millis() - k_poly - poly_g_time - lagrange_beta_time - folding_pk_time;

        println!("    Lagrange polynomials on beta      : {:?}ms",
            lagrange_beta_time
        );
        println!("    Poly G time                       : {:?}ms", poly_g_time);
        println!("    Divide vanishing                  : {:?}ms", k_poly);
        println!("    Compute error and fold traces     : {:?}ms", rest_time);

        let second_part_of_proof = Instant::now();
        // Now we need to generate the last proof.
        let error_lagrange: Polynomial<F, LagrangeCoeff> = Polynomial {
            values: error_terms.clone(),
            _marker: PhantomData,
        };
        let error_coeff = pk.vk.get_domain().lagrange_to_coeff(error_lagrange.clone());
        let committed_error = CS::commit_lagrange(params, &error_lagrange);

        transcript.write(&committed_error)?;

        // Now we need to create the final proof and verify that the opening of the
        // instance column evaluates at `e` in beta.
        // The PK needs to update the fixed values, as these are now folded
        let fixed_values = folded_trace.fixed_polys.clone();
        let fixed_polys = fixed_values
            .iter()
            .cloned()
            .map(|p| pk.vk.get_domain().lagrange_to_coeff(p))
            .collect::<Vec<_>>();
        let fixed_cosets = fixed_polys
            .iter()
            .cloned()
            .map(|p| pk.vk.get_domain().coeff_to_extended(p))
            .collect::<Vec<_>>();

        // We need to update the fixed polynomials from the proving key.
        let mut pk_final_proof = pk.clone();
        pk_final_proof.fixed_polys = fixed_polys;
        pk_final_proof.fixed_values = fixed_values;
        pk_final_proof.fixed_cosets = fixed_cosets;

        let folded_trace = ProverTrace::from_folding_trace(folded_trace.clone());

        // Now we need to finalise the proof. We do not use the finalise_proof function
        // as we need to 'correct' the plonk identity, with the error term from
        // protogalaxy.

        let domain = pk.get_vk().get_domain();
        let h_poly = crate::plonk::compute_h_poly(&pk_final_proof, &folded_trace);

        let ProverTrace {
            advice_polys,
            instance_polys,
            lookups,
            trashcans,
            permutations,
            vanishing,
            ..
        } = folded_trace;

        // When constructing the vanishing polynomial, we need to correct the identity.
        let correction = domain.coeff_to_extended(error_coeff.clone());
        let h = h_poly - &correction;
        let vanishing = vanishing.construct::<CS, T>(params, domain, h, transcript)?;

        let x: F = transcript.squeeze_challenge();

        let advice_polys = advice_polys
            .into_iter()
            .map(|a| a.into_iter().map(|p| domain.lagrange_to_coeff(p)).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        write_evals_to_transcript(
            &pk_final_proof,
            nb_committed_instances,
            &instance_polys,
            &advice_polys,
            x,
            transcript,
        )?;

        // We also add the evaluation of the correction polynomial
        let correction_eval = eval_polynomial(&error_coeff, x);
        transcript.write(&correction_eval)?;

        let vanishing = vanishing.evaluate(x, domain, transcript)?;
        pk_final_proof.permutation.evaluate(x, transcript)?;

        let permutations = permutations
            .into_iter()
            .map(|permutation| -> Result<_, _> {
                permutation.evaluate(&pk_final_proof, x, transcript)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let lookups = lookups
            .into_iter()
            .map(|lookups| -> Result<Vec<_>, _> {
                lookups
                    .into_iter()
                    .map(|p| p.evaluate(&pk_final_proof, x, transcript))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let trashcans: Vec<Vec<trash::prover::Evaluated<F>>> = trashcans
            .into_iter()
            .map(|trash| -> Result<Vec<_>, _> {
                trash
                    .into_iter()
                    .map(|p| p.evaluate(domain, x, transcript))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut queries = compute_queries(
            &pk_final_proof,
            nb_committed_instances,
            &instance_polys,
            &advice_polys,
            &permutations,
            &lookups,
            &trashcans,
            &vanishing,
            x,
        );

        // We push the query of the error polynomial in X and in Beta
        queries.push(ProverQuery {
            point: x,
            poly: &error_coeff,
        });

        queries.push(ProverQuery {
            point: beta_pg,
            poly: &error_coeff,
        });

        let res = CS::multi_open(params, &queries, transcript).map_err(|_| Error::ConstraintSystemFailure);

        println!("Second part of proof: {:?}", second_part_of_proof.elapsed().as_millis());
        res
    }

    fn compute_h(
        folding_pk: &FoldingPk<F>,
        folded_trace: &FoldingProverTrace<F>,
    ) -> Polynomial<F, LagrangeCoeff> {
        let FoldingProverTrace {
            fixed_polys,
            advice_polys,
            instance_values,
            lookups,
            permutations,
            trashcans,
            challenges,
            beta,
            gamma,
            theta,
            trash_challenge,
            y,
            ..
        } = folded_trace;

        folding_pk.ev.evaluate_h::<LagrangeCoeff>(
            &folding_pk.domain,
            &folding_pk.cs,
            &advice_polys.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &instance_values.iter().map(|i| i.as_slice()).collect::<Vec<_>>(),
            fixed_polys,
            challenges,
            y,
            *beta,
            *gamma,
            theta,
            *trash_challenge,
            lookups,
            trashcans,
            permutations,
            &folding_pk.l0,
            &folding_pk.l_last,
            &folding_pk.l_active_row,
            &folding_pk.permutation_pk_cosets,
        )
    }

    /// This function takes a domain, a slice of traces, and computes computes
    /// two FFTs per element in the trace.
    /// This allows to compute the following polynomial in extended form:
    ///
    /// ```text
    /// P(X) := ∑_{j ∈ [k]} Lⱼ(X)·ωⱼ)
    /// ```
    ///
    /// `P(X)` is represented as a trace, where each element in the trace is a
    /// polynomial. In evaluation form, `P(X)` will be simply the elements of
    /// `ωⱼ` at each root of unity. Therefore, to compute `P(X)` in extended
    /// form, we need to take each element of the trace, convert it to coefficient
    /// form, and then back to extended evaluation form.
    ///
    /// # Panics
    ///
    /// If the number of traces does not equal the size of the domain.
    #[allow(unsafe_code)]
    fn traces_fft(
        domain: &EvaluationDomain<F>,
        traces: &[&FoldingProverTrace<F>],
    ) -> LiftedFoldingTrace<F> {
        assert_eq!(domain.n as usize, traces.len());
        let k = traces.len();

        // TODO: if we handle different circuits, we'll need to be more generic here.
        let big_domain_size  = traces[0].fixed_polys[0].len();
        let len_fixed = traces[0].fixed_polys.len();
        let len_advice = traces[0].advice_polys[0].len();
        let len_instance = traces[0].instance_polys[0].len();
        let len_lookups = traces[0].lookups[0].len();
        let len_permutation_sets = traces[0].permutations[0].sets.len();
        let len_trash_cans = traces[0].trashcans[0].len();
        let len_challenges = traces[0].challenges.len();
        let len_theta = traces[0].theta.len();
        let len_y = traces[0].y[0].len();


        let now = Instant::now();

        let transposed_trace = (0..domain.extended_len()).into_par_iter().map(|_| FoldingProverTrace::with_same_dimensions(traces[0])).collect::<Vec<_>>();

        /// A no-op "lock" that just wraps a type for API compatibility.
        /// It implements `Sync` unsafely, asserting that the user ensures thread safety.
        pub struct NullLock<T>(pub T);

        unsafe impl<T> Sync for NullLock<T> {}
        unsafe impl<T> Send for NullLock<T> {}

        impl<T> NullLock<T> {
            pub fn lock(&self) -> NullGuard<T> {
                // Returns a fake guard (no locking)
                NullGuard(&self.0 as *const T as *mut T)
            }
        }

        pub struct NullGuard<T>(*mut T);

        impl<T> Deref for NullGuard<T> {
            type Target = T;
            fn deref(&self) -> &T {
                unsafe { &*self.0 }
            }
        }

        impl<T> DerefMut for NullGuard<T> {
            fn deref_mut(&mut self) -> &mut T {
                unsafe { &mut *self.0 }
            }
        }

        let buffer = NullLock(transposed_trace);

        println!("Initialise transposed trace: {:?}", now.elapsed());
        let now = Instant::now();


        #[allow(clippy::needless_range_loop)]
        (0..big_domain_size)
            .into_par_iter()
            .map(|_| (
                vec![vec![F::ZERO; domain.extended_len()]; len_fixed],
                vec![vec![F::ZERO; domain.extended_len()]; len_advice],
                vec![vec![F::ZERO; domain.extended_len()]; len_instance],
                vec![vec![F::ZERO; domain.extended_len()]; len_instance],
                vec![vec![F::ZERO; domain.extended_len()]; len_lookups],
                vec![vec![F::ZERO; domain.extended_len()]; len_lookups],
                vec![vec![F::ZERO; domain.extended_len()]; len_lookups],
                vec![vec![F::ZERO; domain.extended_len()]; len_permutation_sets],
                vec![vec![F::ZERO; domain.extended_len()]; len_trash_cans],
                vec![F::ZERO; domain.extended_len()],
            ))
            .enumerate()
            .for_each(|
            (i,
                (mut fixed, mut advice, mut instance_val, mut instance_polys, mut permuted_in, mut product_poly, mut permuted_table, mut permutation, mut trash, mut vanishing)
            )
        | {
            for j in 0..len_fixed {
                fixed[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].fixed_polys[j][i]);
                domain.back_and_forth_fft(&mut fixed[j]);
            }

            for j in 0..len_advice {
                advice[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].advice_polys[0][j][i]);
                domain.back_and_forth_fft(&mut advice[j]);
            }

            // TODO: We only need to keep one for folding
            for j in 0..len_instance {
                instance_val[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].instance_values[0][j][i]);
                domain.back_and_forth_fft(&mut instance_val[j]);

                instance_polys[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].instance_polys[0][j][i]);
                domain.back_and_forth_fft(&mut instance_polys[j]);
            }

            for j in 0..len_lookups {
                // Permuted input poly
                permuted_in[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].lookups[0][j].permuted_input_poly[i]);
                domain.back_and_forth_fft(&mut permuted_in[j]);

                // Product poly
                product_poly[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].lookups[0][j].product_poly[i]);
                domain.back_and_forth_fft(&mut product_poly[j]);

                // Permuted table poly
                permuted_table[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].lookups[0][j].permuted_table_poly[i]);
                domain.back_and_forth_fft(&mut permuted_table[j]);
            }

            for j in 0..len_permutation_sets {
                permutation[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].permutations[0].sets[j].permutation_product_poly[i]);
                domain.back_and_forth_fft(&mut permutation[j]);
            }

            for j in 0..len_trash_cans {
                trash[j][..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].trashcans[0][j].trash_poly[i]);
                domain.back_and_forth_fft(&mut trash[j]);
            }

            // Vanishing
            vanishing[..k].iter_mut().enumerate().for_each(|(idx, val)| *val = traces[idx].vanishing.random_poly[i]);
            domain.back_and_forth_fft(&mut vanishing);

                // (fixed, advice, instance_val, instance_polys, permuted_in, product_poly, permuted_table, permutation, trash, vanishing)

                let mut transposed_trace = buffer.lock();


                for new_i in 0..domain.extended_len() {
                    transposed_trace[new_i].fixed_polys.iter_mut().enumerate().for_each(|(j, fixed_poly)| fixed_poly[i] = fixed[j][new_i]);
                    transposed_trace[new_i].advice_polys[0].iter_mut().enumerate().for_each(|(j, advice_poly)| advice_poly[i] = advice[j][new_i]);
                    transposed_trace[new_i].instance_values[0].iter_mut().enumerate().for_each(|(j, instance_value)| instance_value[i] = instance_val[j][new_i]);
                    transposed_trace[new_i].instance_polys[0].iter_mut().enumerate().for_each(|(j, instance_poly)| instance_poly[i] = instance_polys[j][new_i]);
                    transposed_trace[new_i].lookups[0].iter_mut().enumerate().for_each(|(j, lookup)| lookup.permuted_input_poly[i] = permuted_in[j][new_i]);
                    transposed_trace[new_i].lookups[0].iter_mut().enumerate().for_each(|(j, lookup)| lookup.product_poly[i] = product_poly[j][new_i]);
                    transposed_trace[new_i].lookups[0].iter_mut().enumerate().for_each(|(j, lookup)| lookup.permuted_table_poly[i] = permuted_table[j][new_i]);
                    transposed_trace[new_i].permutations[0].sets.iter_mut().enumerate().for_each(|(j, perm_set)| perm_set.permutation_product_poly[i] = permutation[j][new_i]);
                    transposed_trace[new_i].trashcans[0].iter_mut().enumerate().for_each(|(j, trash_can)| trash_can.trash_poly[i] = trash[j][new_i]);

                    transposed_trace[new_i].vanishing.random_poly[i] = vanishing[new_i];
                }
        });
            // .collect::<Vec<_>>();

        // for new_i in 0..domain.extended_len() {
        //     foo.par_iter().enumerate().for_each(|(old_i, row)| {
        //         let mut transposed_trace = buffer.lock();
        //
        //         transposed_trace[new_i].fixed_polys.iter_mut().enumerate().for_each(|(j, fixed_poly)| fixed_poly[old_i] = row.0[j][new_i]);
        //         transposed_trace[new_i].advice_polys[0].iter_mut().enumerate().for_each(|(j, advice_poly)| advice_poly[old_i] = row.1[j][new_i]);
        //         transposed_trace[new_i].instance_values[0].iter_mut().enumerate().for_each(|(j, instance_value)| instance_value[old_i] = row.2[j][new_i]);
        //         transposed_trace[new_i].instance_polys[0].iter_mut().enumerate().for_each(|(j, instance_poly)| instance_poly[old_i] = row.3[j][new_i]);
        //         transposed_trace[new_i].lookups[0].iter_mut().enumerate().for_each(|(j, lookup)| lookup.permuted_input_poly[old_i] = row.4[j][new_i]);
        //         transposed_trace[new_i].lookups[0].iter_mut().enumerate().for_each(|(j, lookup)| lookup.product_poly[old_i] = row.5[j][new_i]);
        //         transposed_trace[new_i].lookups[0].iter_mut().enumerate().for_each(|(j, lookup)| lookup.permuted_table_poly[old_i] = row.6[j][new_i]);
        //         transposed_trace[new_i].permutations[0].sets.iter_mut().enumerate().for_each(|(j, perm_set)| perm_set.permutation_product_poly[old_i] = row.7[j][new_i]);
        //         transposed_trace[new_i].trashcans[0].iter_mut().enumerate().for_each(|(j, trash_can)| trash_can.trash_poly[old_i] = row.8[j][new_i]);
        //
        //         transposed_trace[new_i].vanishing.random_poly[old_i] = row.9[new_i];
        //     });
        // }
        // drop(foo);
        println!("Fill in big_trace: {:?}", now.elapsed());
        let now = Instant::now();

        let mut transposed_trace = buffer.0;

        for j in 0..len_challenges {
            let values = traces.iter().map(|trace| trace.challenges[j]).collect::<Vec<_>>();
            let coeff = domain.lagrange_to_coeff(Polynomial{ values, _marker: PhantomData});
            let extended = domain.coeff_to_extended(coeff);

            transposed_trace.iter_mut().enumerate().for_each(|(idx, buffer_trace)| {
                buffer_trace.challenges[j] = extended[idx];
            })
        }

        for j in 0..len_theta {
            let values = traces.iter().map(|trace| trace.theta[j]).collect::<Vec<_>>();
            let coeff = domain.lagrange_to_coeff(Polynomial{ values, _marker: PhantomData});
            let extended = domain.coeff_to_extended(coeff);

            transposed_trace.iter_mut().enumerate().for_each(|(idx, buffer_trace)| {
                buffer_trace.theta[j] = extended[idx];
            })
        }

        for j in 0..len_y {
            let values = traces.iter().map(|trace| trace.y[0][j]).collect::<Vec<_>>();
            let coeff = domain.lagrange_to_coeff(Polynomial{ values, _marker: PhantomData});
            let extended = domain.coeff_to_extended(coeff);

            transposed_trace.iter_mut().enumerate().for_each(|(idx, buffer_trace)| {
                buffer_trace.y[0][j] = extended[idx];
            })
        }

        // Beta
        let values = traces.iter().map(|trace| trace.beta).collect::<Vec<_>>();
        let coeff = domain.lagrange_to_coeff(Polynomial{ values, _marker: PhantomData});
        let extended = domain.coeff_to_extended(coeff);

        transposed_trace.iter_mut().enumerate().for_each(|(idx, buffer_trace)| {
            buffer_trace.beta = extended[idx];
        });

        // Gamma
        let values = traces.iter().map(|trace| trace.gamma).collect::<Vec<_>>();
        let coeff = domain.lagrange_to_coeff(Polynomial{ values, _marker: PhantomData});
        let extended = domain.coeff_to_extended(coeff);

        transposed_trace.iter_mut().enumerate().for_each(|(idx, buffer_trace)| {
            buffer_trace.gamma = extended[idx];
        });

        // Trash challenge
        let values = traces.iter().map(|trace| trace.trash_challenge).collect::<Vec<_>>();
        let coeff = domain.lagrange_to_coeff(Polynomial{ values, _marker: PhantomData});
        let extended = domain.coeff_to_extended(coeff);

        transposed_trace.iter_mut().enumerate().for_each(|(idx, buffer_trace)| {
            buffer_trace.trash_challenge = extended[idx];
        });

        println!("Finalise challenges: {:?}", now.elapsed());

        transposed_trace
    }

    /// Computes:
    ///
    /// ```text
    /// G(X) := ∑_{i ∈ [n]} pow_i(β*) · f_i(L₀(X)·ω + ∑_{j ∈ [k]} Lⱼ(X)·ωⱼ)} )
    /// ```
    ///
    /// where:
    /// - β* are the randomisation challenges,
    /// - f_i is the meta-identity (a linear combination of all identities) were
    ///   i represents each row of the trace,
    /// - L₀, Lⱼ are folding lagrange polynomials,
    /// - ω are the witness traces,
    /// - pow_i denotes the power function.
    ///
    /// We evaluate each `f_i` over a polynomial whose values are given in
    /// evaluation form on the *folding domain*, a domain of size `k * n`. In
    /// other words, instead of applying `f_i` to a trace represented by
    /// field elements directly, we apply it to a trace represented by `k *
    /// n` field elements.
    ///
    /// After evaluating `f_i`, we batch the resulting values with powers of β,
    /// producing a single vector of size `k * n`. This vector represents the
    /// polynomial `g` in evaluation form.
    ///
    /// Since each folded instance corresponds to a different evaluation point
    /// of the inner polynomial, we evaluate `f_i` at the *instance level*
    /// (i.e., each row for a single trace), and then apply batching with
    /// powers of β. This approach is more efficient than evaluating `f_i`
    /// row-by-row across all instances at once, as it allows us to take
    /// advantage of the `GraphEvaluator`.
    ///
    /// The resulting polynomial `g` is defined over the *folded domain*, which
    /// is much smaller. Each evaluation in this domain is obtained from the
    /// batched values computed above.
    /// This returns the aggregated polynomial G, as well as the vector of
    /// errors.
    fn compute_poly_g(
        folding_pk: &FoldingPk<F>,
        domain: &EvaluationDomain<F>,
        beta_coeffs: &[F],
        traces: &[&FoldingProverTrace<F>],
    ) -> (Polynomial<F, ExtendedLagrangeCoeff>, Vec<Vec<F>>) {
        let batch_trace = Instant::now();
        let lifted_folding_trace = Self::traces_fft(domain, traces);
        println!("Batch traces: {:?}", batch_trace.elapsed().as_millis());

        // In the future, we'll output simply a commitment to it, but
        // perhaps at an upper level function.
        let mut g_poly_unbatched =
            vec![vec![F::ZERO; folding_pk.domain.n as usize]; lifted_folding_trace.len()];
        let g_poly = g_poly_unbatched
            .par_iter_mut()
            .enumerate()
            .map(|(idx, g_poly)| {
                let witness_poly = Self::compute_h(folding_pk, &lifted_folding_trace[idx]);
                *g_poly = witness_poly.values;

                g_poly
                    .iter()
                    .zip(beta_coeffs.iter())
                    .map(|(witness, beta_coef)| *witness * beta_coef)
                    .reduce(|a, b| a + b)
                    .unwrap()
            })
            .collect();

        (
            Polynomial {
                values: g_poly,
                _marker: Default::default(),
            },
            g_poly_unbatched,
        )
    }

    /// Function to fold traces over an evaluation `\gamma`
    fn fold_traces(
        dk_domain: &EvaluationDomain<F>,
        traces: &[&FoldingProverTrace<F>],
        gamma: &F,
    ) -> FoldingProverTrace<F> {
        let lagrange_polys = (0..traces.len())
            .map(|i| {
                // For the moment we only support batching of traces of dimension one.
                // David: what does this mean?
                assert_eq!(traces[i].advice_polys.len(), 1);
                let mut l = dk_domain.empty_lagrange();
                l[i] = F::ONE;
                l
            })
            .map(|p| dk_domain.lagrange_to_coeff(p))
            .collect::<Vec<_>>();

        let buffer = FoldingProverTrace::with_same_dimensions(traces[0]);
        let lagranges_in_gamma = lagrange_polys
            .iter()
            .map(|poly| eval_polynomial(poly, *gamma))
            .collect::<Vec<_>>();

        linear_combination(buffer, traces, &lagranges_in_gamma)
    }
}

use crate::transcript::{Hashable, Sampleable, Transcript};

/// Computes the error terms t_i = f_i(w(\gamma)) where w(X) = ∑_{j ∈ [k]}
/// Lⱼ(X)·ωⱼ is the polynomial that interpolates the witnesses.
fn compute_error_terms<F: PrimeField + WithSmallOrderMulGroup<3>>(
    pk_domain_size: usize,
    dk_domain: &EvaluationDomain<F>,
    poly_g_unbatched: &[Vec<F>], // use slice instead of &Vec
    gamma_pg: &F,
) -> Vec<F> {
    let n_rows = poly_g_unbatched.len();

    // Parallel over columns j
    (0..pk_domain_size)
        .into_par_iter()
        .map(|j| {
            // Allocate buffer once per iteration
            let mut poly_evals = Vec::with_capacity(n_rows);
            for row in poly_g_unbatched {
                poly_evals.push(row[j]);
            }

            // Convert to coefficient basis
            let coeff_poly = dk_domain.extended_to_coeff(Polynomial {
                values: poly_evals,
                _marker: PhantomData,
            });

            // Evaluate at gamma_pg
            eval_polynomial(&coeff_poly, *gamma_pg)
        })
        .collect::<Vec<F>>() // collect the results into a Vec<F>
}

/// Computes the lagrange polynomials for a domain (with root omega)
/// Then, it evaluates them at 'beta', obtaining a vector of coefficients.
/// It uses the formula: L_i(beta) = Z(beta) * omega^i / (n * (beta - omega^i))
/// We decompose it into a fixed part [Z(beta) / n] and a variable part [omega^i / (beta - omega^i)]
pub fn eval_lagrange_on_beta<F: PrimeField + WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    beta: &F,
) -> Vec<F> {
    let pk_domain_size = domain.n as usize;
    let omega: F = domain.get_omega(); // generator of multiplicative subgroup

    let n_fe = F::from(pk_domain_size as u64);
    
    // fixed_term = Z(beta) / n = (beta^n - 1) / n
    let fixed_term = (beta.pow([pk_domain_size as u64]) - F::ONE) * n_fe.invert().unwrap();

    // Calculate all the omega powers and store them in a vector
    // TODO: parallelize? We could start from powers omega^0, omega^m, omega^2m, ...
    // Where for a domain of size n, m = n / #threads
    let mut omegas: Vec<F> = Vec::with_capacity(pk_domain_size);
    omegas.push(F::ONE);
    for _ in 0..(pk_domain_size - 1) {
        omegas.push(*omegas.last().unwrap() * omega);
    }

    omegas.into_par_iter()
        .map(|omega_i| {
            fixed_term * omega_i * (*beta - omega_i).invert().unwrap()
        })
        .collect()
}


#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ff::Field;
    use midnight_curves::{Bls12, Fq};
    use rand_chacha::ChaCha8Rng;
    use rand_core::{RngCore, SeedableRng};

    use crate::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk_with_k, prepare, Advice, Circuit, Column,
            ConstraintSystem, Constraints, Error, Expression, Selector, TableColumn,
        },
        poly::{
            kzg::{params::ParamsKZG, KZGCommitmentScheme},
            Rotation,
        },
        protogalaxy::{
            prover::{ProtogalaxyProver, eval_lagrange_on_beta},
            verifier::ProtogalaxyVerifierOneShot,
        },
        transcript::{CircuitTranscript, Transcript},
        utils::arithmetic::eval_polynomial,
    };

    #[derive(Clone, Copy)]
    struct TestCircuit {
        witness: [Value<Fq>; 1 << 8],
    }

    impl TestCircuit {
        fn from(witness: [Value<Fq>; 1 << 8]) -> Self {
            Self { witness }
        }
    }

    #[derive(Debug, Clone)]
    struct MyConfig {
        mul_selector: Selector,
        table_selector: Selector,
        table: TableColumn,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
    }

    impl Circuit<Fq> for TestCircuit {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                witness: [Value::unknown(); 1 << 8],
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fq>) -> MyConfig {
            let config = MyConfig {
                mul_selector: meta.complex_selector(),
                table_selector: meta.complex_selector(),
                table: meta.lookup_table_column(),
                a: meta.advice_column(),
                b: meta.advice_column(),
                c: meta.advice_column(),
            };

            meta.enable_equality(config.a);
            meta.enable_equality(config.b);

            meta.create_gate("mul", |meta| {
                let a = meta.query_advice(config.a, Rotation::cur());
                let b = meta.query_advice(config.b, Rotation::cur());
                let c = meta.query_advice(config.c, Rotation::cur());
                Constraints::with_selector(
                    config.mul_selector,
                    vec![a.clone() * a * b.clone() * b - c],
                )
            });

            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(config.table_selector);
                let not_selector = Expression::Constant(Fq::ONE) - selector.clone();

                let a = meta.query_advice(config.a, Rotation::cur());
                vec![(selector * a + not_selector, config.table)]
            });

            config
        }

        fn synthesize(
            &self,
            config: MyConfig,
            mut layouter: impl Layouter<Fq>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "8-bit table",
                |mut table| {
                    for row in 0u64..(1 << 8) {
                        table.assign_cell(
                            || format!("row {row}"),
                            config.table,
                            row as usize,
                            || Value::known(Fq::from(row + 1)),
                        )?;
                    }

                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "assign values",
                |mut region| {
                    for (offset, val) in self.witness.into_iter().enumerate() {
                        config.table_selector.enable(&mut region, offset)?;
                        config.mul_selector.enable(&mut region, offset)?;
                        let a = region.assign_advice(|| "a", config.a, offset, || val)?;
                        a.copy_advice(|| "copy a to b", &mut region, config.b, offset)?;
                        // region.assign_advice(|| "b", config.b, offset, || val)?;
                        region.assign_advice(
                            || "c",
                            config.c,
                            offset,
                            || val.map(|v| v * v * v * v),
                        )?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }
    use crate::poly::commitment::Guard;

    #[test]
    fn lagrange_poly_test() {

        const K: usize = 9;
        let k = 1; // number of folding instances

        let rng = ChaCha8Rng::from_seed([0u8; 32]);
        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K as u32, rng);

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        let mut rand_bytes = [0u8; 1 << 8];
        rng.fill_bytes(&mut rand_bytes);

        let witnesses = (0..k)
            .map(|_| {
                rand_bytes
                    .into_iter()
                    .map(|byte| Value::known(Fq::from((byte as u64) + 1)))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let circuits = witnesses.into_iter().map(TestCircuit::from).collect::<Vec<_>>();

        let vk =
            keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuits[0], K as u32)
                .expect("keygen_vk should not fail");

        let pk_domain_size = 1 << K;

        let beta = Fq::from(rand::random::<u64>());

        let lagrange_on_beta = eval_lagrange_on_beta(&vk.get_domain(), &beta);

        // Now we compute the same values using lagrange polynomials
        let mut lagrange_polys = Vec::with_capacity(pk_domain_size);
        for i in 0..pk_domain_size {
            let mut l_i = vk.get_domain().empty_lagrange();
            l_i[i] = Fq::ONE;

            let l_coeff = vk.get_domain().lagrange_to_coeff(l_i);
            lagrange_polys.push(l_coeff);
        }

            let pk_domain_size = vk.get_domain().n as usize;

        for i in 0..pk_domain_size {
            let eval = eval_polynomial(&lagrange_polys[i], beta);
            assert_eq!(eval, lagrange_on_beta[i]);
        }
    }


    #[test]
    fn folding_test_oneshot() {
        const K: usize = 15;
        let k = 4; // number of folding instances

        let rng = ChaCha8Rng::from_seed([0u8; 32]);
        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K as u32, rng);

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        let mut rand_bytes = [0u8; 1 << 8];
        rng.fill_bytes(&mut rand_bytes);

        let witnesses = (0..k)
            .map(|_| {
                rand_bytes
                    .into_iter()
                    .map(|byte| Value::known(Fq::from((byte as u64) + 1)))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let circuits = witnesses.into_iter().map(TestCircuit::from).collect::<Vec<_>>();

        let vk =
            keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuits[0], K as u32)
                .expect("keygen_vk should not fail");
        let pk = keygen_pk(vk.clone(), &circuits[0]).expect("keygen_pk should not fail");

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        // Normal proofs. We first generate normal proofs to test performance
        let normal_proving = Instant::now();
        for circuit in circuits.iter() {
            let mut transcript = CircuitTranscript::init();
            create_proof(
                &params,
                &pk,
                &[*circuit],
                0,
                &[&[]],
                &mut rng,
                &mut transcript,
            )
            .expect("Failed to produce a proof");

            let proof = transcript.finalize();
            let mut transcript = CircuitTranscript::init_from_bytes(&proof);
            prepare(&vk, &[&[]], &[&[]], &mut transcript)
                .unwrap()
                .verify(&params.verifier_params())
                .unwrap();
        }
        println!(
            "Time to generate {} proofs: {:?}",
            circuits.len(),
            normal_proving.elapsed()
        );

        // Fold proofs. We first initialise folding with the first circuit
        let folding = Instant::now();
        let mut transcript = CircuitTranscript::init();

        ProtogalaxyProver::<_, _, K>::fold(
            &params,
            pk.clone(),
            circuits,
            0,
            &[&[], &[], &[], &[]],
            &mut rng,
            &mut transcript,
        )
        .expect("Failed to fold many instances");
        println!("Time to fold: {:?}", folding.elapsed());

        let mut transcript = CircuitTranscript::init_from_bytes(&transcript.finalize());
        // Now we begin verification
        ProtogalaxyVerifierOneShot::<_, _, K>::fold(
            &vk,
            &[&[], &[], &[], &[]],
            &[&[], &[], &[], &[]],
            &mut transcript,
        )
        .expect("Failed to fold instances by the verifier")
        .verify(&params.verifier_params())
        .expect("Verification failed");

        println!("Folding was a success");
    }
}

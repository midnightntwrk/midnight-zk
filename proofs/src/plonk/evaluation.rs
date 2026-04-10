use ff::{PrimeField, WithSmallOrderMulGroup};
use group::ff::Field;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use super::{ConstraintSystem, Expression};
use crate::{
    plonk::{logup, permutation, trash, Any},
    poly::{EvaluationDomain, Polynomial, PolynomialRepresentation, Rotation},
    utils::arithmetic::parallelize,
};

/// Return the index in a polynomial of size `2^log_n` after applying
/// rotation `rot` scaled by `2^log_scale`.
///
/// - `idx`: current position in the evaluation domain.
/// - `rot`: rotation amount in base-domain steps (may be negative).
/// - `log_scale`: `log2(extended_domain_size / base_domain_size)`. Converts
///   base-domain rotations to evaluation-domain indices. Zero when
///   evaluating over the base domain itself.
/// - `log_n`: `log2(evaluation_domain_size)`. Must equal the actual domain
///   size used for indexing; the result is reduced modulo `2^log_n`.
#[inline]
pub(crate) fn get_rotation_idx(idx: usize, rot: i32, log_scale: u32, log_n: u32) -> usize {
    let mask = (1usize << log_n) - 1;
    idx.wrapping_add(((rot as isize) << log_scale) as usize) & mask
}

/// Value used in a calculation
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd)]
pub enum ValueSource {
    /// This is a constant value
    Constant(usize),
    /// This is an intermediate value
    Intermediate(usize),
    /// This is a fixed column
    Fixed(usize, usize),
    /// This is an advice (witness) column
    Advice(usize, usize),
    /// This is an instance (external) column
    Instance(usize, usize),
    /// This is a challenge
    Challenge(usize),
    /// beta
    Beta(),
    /// theta
    Theta(),
    /// trash challenge
    TrashChallenge(),
    /// y
    Y(),
    /// Previous value
    PreviousValue(),
}

impl Default for ValueSource {
    fn default() -> Self {
        ValueSource::Constant(0)
    }
}

impl ValueSource {
    /// Get the value for this source
    #[allow(clippy::too_many_arguments)]
    pub fn get<F: Field, B: PolynomialRepresentation>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        fixed_values: &[Polynomial<F, B>],
        advice_values: &[Polynomial<F, B>],
        instance_values: &[Polynomial<F, B>],
        challenges: &[F],
        beta: &F,
        theta: &F,
        trash_challenge: &F,
        y: &F,
        previous_value: &F,
    ) -> F {
        match self {
            ValueSource::Constant(idx) => constants[*idx],
            ValueSource::Intermediate(idx) => intermediates[*idx],
            ValueSource::Fixed(column_index, rotation) => {
                fixed_values[*column_index][rotations[*rotation]]
            }
            ValueSource::Advice(column_index, rotation) => {
                advice_values[*column_index][rotations[*rotation]]
            }
            ValueSource::Instance(column_index, rotation) => {
                instance_values[*column_index][rotations[*rotation]]
            }
            ValueSource::Challenge(index) => challenges[*index],
            ValueSource::Beta() => *beta,
            ValueSource::Theta() => *theta,
            ValueSource::TrashChallenge() => *trash_challenge,
            ValueSource::Y() => *y,
            ValueSource::PreviousValue() => *previous_value,
        }
    }
}

/// Calculation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Calculation {
    /// This is an addition
    Add(ValueSource, ValueSource),
    /// This is a subtraction
    Sub(ValueSource, ValueSource),
    /// This is a product
    Mul(ValueSource, ValueSource),
    /// This is a square
    Square(ValueSource),
    /// This is a double
    Double(ValueSource),
    /// This is a negation
    Negate(ValueSource),
    /// This is Horner's rule: `val = a; val = val * c + b[]`
    Horner(ValueSource, Vec<ValueSource>, ValueSource),
    /// This is a simple assignment
    Store(ValueSource),
}

impl Calculation {
    /// Get the resulting value of this calculation
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<F: Field, B: PolynomialRepresentation>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        fixed_values: &[Polynomial<F, B>],
        advice_values: &[Polynomial<F, B>],
        instance_values: &[Polynomial<F, B>],
        challenges: &[F],
        beta: &F,
        theta: &F,
        trash_challenge: &F,
        y: &F,
        previous_value: &F,
    ) -> F {
        let get_value = |value: &ValueSource| {
            value.get(
                rotations,
                constants,
                intermediates,
                fixed_values,
                advice_values,
                instance_values,
                challenges,
                beta,
                theta,
                trash_challenge,
                y,
                previous_value,
            )
        };
        match self {
            Calculation::Add(a, b) => get_value(a) + get_value(b),
            Calculation::Sub(a, b) => get_value(a) - get_value(b),
            Calculation::Mul(a, b) => get_value(a) * get_value(b),
            Calculation::Square(v) => get_value(v).square(),
            Calculation::Double(v) => get_value(v).double(),
            Calculation::Negate(v) => -get_value(v),
            Calculation::Horner(start_value, parts, factor) => {
                let factor = get_value(factor);
                let mut value = get_value(start_value);
                for part in parts.iter() {
                    value = value * factor + get_value(part);
                }
                value
            }
            Calculation::Store(v) => get_value(v),
        }
    }
}

/// Wraps a `GraphEvaluator` for lookups with named handles to the evaluator
/// outputs.
#[derive(Clone, Debug)]
pub struct LookupGraphEvaluator<F: PrimeField> {
    /// The underlying computation graph
    pub graph: GraphEvaluator<F>,
    /// Value containing the sum of partial products, Σⱼ ∏_{k≠j}(fₖ + β)
    pub sum_partial_products: ValueSource,
    /// Value containing the product, ∏ⱼ(fⱼ + β)
    pub product: ValueSource,
    /// Value containing the compressed table value (t + β)
    pub table: ValueSource,
    /// Selector of the lookup argument
    pub selector: ValueSource,
}

/// Evaluator
#[derive(Clone, Default, Debug)]
pub struct Evaluator<F: PrimeField> {
    ///  Custom gates evaluation
    pub custom_gates: GraphEvaluator<F>,
    ///  Lookups evaluation (one Vec per BatchedArgument, one entry per
    /// flattened arg)
    pub lookups: Vec<Vec<LookupGraphEvaluator<F>>>,
    ///  Trashcans evaluation
    pub trashcans: Vec<GraphEvaluator<F>>,
}

/// GraphEvaluator
#[derive(Clone, Debug)]
pub struct GraphEvaluator<F: PrimeField> {
    /// Constants
    pub constants: Vec<F>,
    /// Rotations
    pub rotations: Vec<i32>,
    /// Calculations
    pub calculations: Vec<CalculationInfo>,
    /// Number of intermediates
    pub num_intermediates: usize,
}

/// EvaluationData
#[derive(Default, Debug)]
pub struct EvaluationData<F: PrimeField> {
    /// Intermediates
    pub intermediates: Vec<F>,
    /// Rotations
    pub rotations: Vec<usize>,
}

impl<F: PrimeField> EvaluationData<F> {
    /// Resolve a `ValueSource::Intermediate` handle to its computed value.
    pub fn resolve(&self, vs: ValueSource) -> F {
        match vs {
            ValueSource::Intermediate(idx) => self.intermediates[idx],
            _ => unreachable!("expected Intermediate, got {vs:?}"),
        }
    }
}

/// CalculationInfo
#[derive(Clone, Debug)]
pub struct CalculationInfo {
    /// Calculation
    pub calculation: Calculation,
    /// Target
    pub target: usize,
}

impl<F: WithSmallOrderMulGroup<3>> Evaluator<F> {
    /// Creates a new evaluation structure
    pub fn new(cs: &ConstraintSystem<F>) -> Self {
        let mut ev = Evaluator::default();

        // Custom gates
        let mut parts = Vec::new();
        for gate in cs.gates.iter() {
            parts
                .extend(gate.polynomials().iter().map(|poly| ev.custom_gates.add_expression(poly)));
        }
        ev.custom_gates.add_calculation(Calculation::Horner(
            ValueSource::PreviousValue(),
            parts,
            ValueSource::Y(),
        ));

        // Lookups
        for lookup in cs.lookups.iter() {
            let lookup = lookup.chunk_by_degree(cs.degree());
            let flat_evals = lookup
                .input_expression_chunks()
                .iter()
                .map(|chunk| {
                    let mut graph = GraphEvaluator::default();

                    // Each input expression gets compressed with θ and shifted by β
                    let compressed_inputs_cosets: Vec<_> = chunk
                        .iter()
                        .map(|expressions| {
                            let parts =
                                expressions.iter().map(|expr| graph.add_expression(expr)).collect();
                            let compressed = graph.add_calculation(Calculation::Horner(
                                ValueSource::Constant(0),
                                parts,
                                ValueSource::Theta(),
                            ));

                            graph.add_calculation(Calculation::Add(compressed, ValueSource::Beta()))
                        })
                        .collect();

                    let table_parts: Vec<_> = lookup
                        .table_expressions()
                        .iter()
                        .map(|expr| graph.add_expression(expr))
                        .collect();
                    let compressed_table_coset = graph.add_calculation(Calculation::Horner(
                        ValueSource::Constant(0),
                        table_parts,
                        ValueSource::Theta(),
                    ));

                    let partial_products = (0..compressed_inputs_cosets.len())
                        .map(|i| {
                            let mut acc =
                                graph.add_calculation(Calculation::Store(ValueSource::Constant(1)));
                            for (j, coset) in compressed_inputs_cosets.iter().enumerate() {
                                if j != i {
                                    acc = graph.add_calculation(Calculation::Mul(acc, *coset));
                                }
                            }
                            acc
                        })
                        .collect::<Vec<_>>();

                    let mut sum_partial_products =
                        graph.add_calculation(Calculation::Store(partial_products[0]));
                    let mut product =
                        graph.add_calculation(Calculation::Store(compressed_inputs_cosets[0]));
                    // Compute ∏ⱼ(fⱼ + β) and Σⱼ ∏_{k≠j}(fₖ + β)
                    for (calculation, partial_prod) in compressed_inputs_cosets
                        .into_iter()
                        .zip(partial_products.into_iter())
                        .skip(1)
                    {
                        sum_partial_products = graph
                            .add_calculation(Calculation::Add(sum_partial_products, partial_prod));
                        product = graph.add_calculation(Calculation::Mul(product, calculation));
                    }

                    // Add β: compressed_table + β
                    let table = graph.add_calculation(Calculation::Add(
                        compressed_table_coset,
                        ValueSource::Beta(),
                    ));

                    let selector = graph.add_expression(lookup.selector_expression());
                    let selector = graph.add_calculation(Calculation::Store(selector));

                    LookupGraphEvaluator {
                        selector,
                        graph,
                        sum_partial_products,
                        product,
                        table,
                    }
                })
                .collect();

            ev.lookups.push(flat_evals);
        }

        // Trashcans
        for trash in cs.trashcans.iter() {
            let mut graph = GraphEvaluator::default();

            let parts = trash
                .constraint_expressions()
                .iter()
                .map(|expr| graph.add_expression(expr))
                .collect();

            graph.add_calculation(Calculation::Horner(
                ValueSource::Constant(0),
                parts,
                ValueSource::TrashChallenge(),
            ));

            ev.trashcans.push(graph);
        }

        ev
    }

    /// Evaluate numerator polynomial `nu(X)` of the quotient polynomial
    /// `h(X) = nu(X) / (X^n-1)`
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn evaluate_numerator<B: PolynomialRepresentation>(
        &self,
        domain: &EvaluationDomain<F>,
        cs: &ConstraintSystem<F>,
        advice: &[&[Polynomial<F, B>]],
        instance: &[&[Polynomial<F, B>]],
        fixed: &[Polynomial<F, B>],
        challenges: &[F],
        y: F,
        beta: F,
        gamma: F,
        theta: F,
        trash_challenge: F,
        lookups: &[Vec<logup::prover::Committed<F>>],
        trashcans: &[Vec<trash::prover::Committed<F>>],
        permutations: &[permutation::prover::Committed<F>],
        l0: &Polynomial<F, B>,
        l_last: &Polynomial<F, B>,
        l_active_row: &Polynomial<F, B>,
        permutation_pk_cosets: &[Polynomial<F, B>],
    ) -> Polynomial<F, B> {
        let size = B::len(domain);
        let log_scale = B::k(domain) - domain.k();
        let omega = B::omega(domain);
        let log_n = B::k(domain);
        let one = F::ONE;

        let p = &cs.permutation;

        let mut values = B::empty(domain);

        // Core expression evaluations
        let num_threads = rayon::current_num_threads();
        for ((((advice, instance), lookups), trashcans), permutation) in advice
            .iter()
            .zip(instance.iter())
            .zip(lookups.iter())
            .zip(trashcans.iter())
            .zip(permutations.iter())
        {
            // Custom gates
            rayon::scope(|scope| {
                let chunk_size = size.div_ceil(num_threads);
                for (thread_idx, values) in values.chunks_mut(chunk_size).enumerate() {
                    let start = thread_idx * chunk_size;
                    scope.spawn(move |_| {
                        let mut eval_data = self.custom_gates.instance();
                        for (i, value) in values.iter_mut().enumerate() {
                            let idx = start + i;
                            *value = self.custom_gates.evaluate::<B>(
                                &mut eval_data,
                                fixed,
                                advice,
                                instance,
                                challenges,
                                &beta,
                                &theta,
                                &trash_challenge,
                                &y,
                                value,
                                idx,
                                log_scale,
                                log_n,
                            );
                        }
                    });
                }
            });

            // Permutations
            let sets = &permutation.sets;
            if !sets.is_empty() {
                let blinding_factors = cs.blinding_factors();
                let last_rotation = Rotation(-((blinding_factors + 1) as i32));
                let chunk_len = cs.degree() - 2;
                let delta_start = beta * &B::g_coset(domain);

                let permutation_product_cosets: Vec<Polynomial<F, B>> = sets
                    .par_iter()
                    .map(|set| B::coeff_to_self(domain, set.permutation_product_poly.clone()))
                    .collect();

                let first_set_permutation_product_coset =
                    permutation_product_cosets.first().unwrap();
                let last_set_permutation_product_coset = permutation_product_cosets.last().unwrap();

                // Permutation constraints
                parallelize(&mut values, |values, start| {
                    let mut beta_term = omega.pow_vartime([start as u64, 0, 0, 0]);
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;
                        let r_next = get_rotation_idx(idx, 1, log_scale, log_n);
                        let r_last = get_rotation_idx(idx, last_rotation.0, log_scale, log_n);

                        // Enforce only for the first set.
                        // l_0(X) * (1 - z_0(X)) = 0
                        *value =
                            *value * y + (one - first_set_permutation_product_coset[idx]) * l0[idx];
                        // Enforce only for the last set.
                        // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
                        *value = *value * y
                            + (last_set_permutation_product_coset[idx]
                                * last_set_permutation_product_coset[idx]
                                - last_set_permutation_product_coset[idx])
                                * l_last[idx];
                        // Except for the first set, enforce.
                        // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
                        for set_idx in 1..sets.len() {
                            *value = *value * y
                                + (permutation_product_cosets[set_idx][idx]
                                    - permutation_product_cosets[set_idx - 1][r_last])
                                    * l0[idx];
                        }
                        // And for all the sets we enforce:
                        // (1 - (l_last(X) + l_blind(X))) * (
                        //   z_i(\omega X) \prod_j (p(X) + \beta s_j(X) + \gamma)
                        // - z_i(X) \prod_j (p(X) + \delta^j \beta X + \gamma)
                        // )
                        let mut current_delta = delta_start * beta_term;
                        for ((permutation_product_coset, columns), cosets) in
                            permutation_product_cosets
                                .iter()
                                .zip(p.columns.chunks(chunk_len))
                                .zip(permutation_pk_cosets.chunks(chunk_len))
                        {
                            let mut left = permutation_product_coset[r_next];
                            for (values, permutation) in columns
                                .iter()
                                .map(|&column| match column.column_type() {
                                    Any::Advice(_) => &advice[column.index()],
                                    Any::Fixed => &fixed[column.index()],
                                    Any::Instance => &instance[column.index()],
                                })
                                .zip(cosets.iter())
                            {
                                left *= values[idx] + beta * permutation[idx] + gamma;
                            }

                            let mut right = permutation_product_coset[idx];
                            for values in columns.iter().map(|&column| match column.column_type() {
                                Any::Advice(_) => &advice[column.index()],
                                Any::Fixed => &fixed[column.index()],
                                Any::Instance => &instance[column.index()],
                            }) {
                                right *= values[idx] + current_delta + gamma;
                                current_delta *= &F::DELTA;
                            }

                            *value = *value * y + (left - right) * l_active_row[idx];
                        }
                        beta_term *= &omega;
                    }
                });
            }

            // Pre-compute all lookup cosets in parallel. This trades peak memory
            // for parallelism: the FFTs for different lookups can now overlap.
            let all_lookup_cosets: Vec<_> = lookups
                .par_iter()
                .map(|lookup| {
                    let helper_cosets: Vec<_> = lookup
                        .helper_polys
                        .iter()
                        .map(|h| B::coeff_to_self(domain, h.clone()))
                        .collect();
                    let aggregator_coset = B::coeff_to_self(domain, lookup.aggregator_poly.clone());
                    let multiplicities_coset =
                        B::coeff_to_self(domain, lookup.multiplicities.clone());
                    (helper_cosets, aggregator_coset, multiplicities_coset)
                })
                .collect();

            // Pre-compute all trash cosets in parallel (lookup cosets
            // are already pre-computed above).
            let trash_cosets: Vec<_> = trashcans
                .par_iter()
                .map(|trash| B::coeff_to_self(domain, trash.trash_poly.clone()))
                .collect();

            // Fused lookup + trash constraint evaluation in a single pass
            // over `values`. This keeps values[idx] in L1/L2 across all
            // lookups and trash arguments, avoiding re-reads between passes.
            parallelize(&mut values, |values, start| {
                // Per-thread eval data for all lookups.
                let mut all_lookup_eval_datas: Vec<Vec<_>> = self
                    .lookups
                    .iter()
                    .map(|le| le.iter().map(|l| l.graph.instance()).collect())
                    .collect();
                // Per-thread eval data for all trash arguments.
                let mut trash_eval_datas: Vec<_> =
                    self.trashcans.iter().map(|te| te.instance()).collect();

                for (i, value) in values.iter_mut().enumerate() {
                    let idx = start + i;
                    let r_next = get_rotation_idx(idx, 1, log_scale, log_n);

                    // --- Lookup constraints ---
                    for (n, (helper_cosets, aggregator_coset, multiplicities_coset)) in
                        all_lookup_cosets.iter().enumerate()
                    {
                        let lookup_eval = &self.lookups[n];
                        let eval_datas = &mut all_lookup_eval_datas[n];

                        *value = *value * y + aggregator_coset[idx] * (l0[idx] + l_last[idx]);

                        let mut sum_helpers = F::ZERO;
                        let mut table_value = F::ZERO;
                        let mut selector = F::ZERO;
                        for (fi, lookup_eval) in lookup_eval.iter().enumerate() {
                            lookup_eval.graph.evaluate(
                                &mut eval_datas[fi],
                                fixed,
                                advice,
                                instance,
                                challenges,
                                &beta,
                                &theta,
                                &trash_challenge,
                                &y,
                                &F::ZERO,
                                idx,
                                log_scale,
                                log_n,
                            );

                            let sum_partial_products =
                                eval_datas[fi].resolve(lookup_eval.sum_partial_products);
                            let product = eval_datas[fi].resolve(lookup_eval.product);

                            if fi == 0 {
                                table_value = eval_datas[fi].resolve(lookup_eval.table);
                                selector = eval_datas[fi].resolve(lookup_eval.selector);
                            }

                            *value = *value * y + helper_cosets[fi][idx] * product
                                - sum_partial_products;

                            sum_helpers += helper_cosets[fi][idx];
                        }

                        *value = *value * y
                            + l_active_row[idx]
                                * ((aggregator_coset[r_next]
                                    - aggregator_coset[idx]
                                    - selector * sum_helpers)
                                    * table_value
                                    + multiplicities_coset[idx]);
                    }

                    // --- Trash constraints ---
                    for (n, trash_poly) in trash_cosets.iter().enumerate() {
                        let trash_evaluator = &self.trashcans[n];
                        let argument = &cs.trashcans[n];

                        let compressed_expression = trash_evaluator.evaluate(
                            &mut trash_eval_datas[n],
                            fixed,
                            advice,
                            instance,
                            challenges,
                            &beta,
                            &theta,
                            &trash_challenge,
                            &y,
                            &F::ZERO,
                            idx,
                            log_scale,
                            log_n,
                        );

                        let q = match argument.selector() {
                            Expression::Fixed(query) => fixed[query.column_index()][idx],
                            _ => unreachable!(),
                        };

                        *value = *value * y + (compressed_expression - (one - q) * trash_poly[idx]);
                    }
                }
            });
        }
        values
    }
}

impl<F: PrimeField> Default for GraphEvaluator<F> {
    fn default() -> Self {
        Self {
            // Fixed positions to allow easy access
            constants: vec![F::ZERO, F::ONE, F::from(2u64)],
            rotations: Vec::new(),
            calculations: Vec::new(),
            num_intermediates: 0,
        }
    }
}

impl<F: PrimeField> GraphEvaluator<F> {
    /// Adds a rotation
    fn add_rotation(&mut self, rotation: &Rotation) -> usize {
        let position = self.rotations.iter().position(|&c| c == rotation.0);
        match position {
            Some(pos) => pos,
            None => {
                self.rotations.push(rotation.0);
                self.rotations.len() - 1
            }
        }
    }

    /// Adds a constant
    fn add_constant(&mut self, constant: &F) -> ValueSource {
        let position = self.constants.iter().position(|&c| c == *constant);
        ValueSource::Constant(match position {
            Some(pos) => pos,
            None => {
                self.constants.push(*constant);
                self.constants.len() - 1
            }
        })
    }

    /// Adds a calculation.
    /// Currently does the simplest thing possible: just stores the
    /// resulting value so the result can be reused  when that calculation
    /// is done multiple times.
    fn add_calculation(&mut self, calculation: Calculation) -> ValueSource {
        let existing_calculation = self.calculations.iter().find(|c| c.calculation == calculation);
        match existing_calculation {
            Some(existing_calculation) => ValueSource::Intermediate(existing_calculation.target),
            None => {
                let target = self.num_intermediates;
                self.calculations.push(CalculationInfo {
                    calculation,
                    target,
                });
                self.num_intermediates += 1;
                ValueSource::Intermediate(target)
            }
        }
    }

    /// Generates an optimized evaluation for the expression
    fn add_expression(&mut self, expr: &Expression<F>) -> ValueSource {
        match expr {
            Expression::Constant(scalar) => self.add_constant(scalar),
            Expression::Selector(_selector) => unreachable!(),
            Expression::Fixed(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Fixed(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Advice(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Advice(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Instance(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Instance(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Challenge(challenge) => self.add_calculation(Calculation::Store(
                ValueSource::Challenge(challenge.index()),
            )),
            Expression::Negated(a) => match **a {
                Expression::Constant(scalar) => self.add_constant(&-scalar),
                _ => {
                    let result_a = self.add_expression(a);
                    match result_a {
                        ValueSource::Constant(0) => result_a,
                        _ => self.add_calculation(Calculation::Negate(result_a)),
                    }
                }
            },
            Expression::Sum(a, b) => {
                // Undo subtraction stored as a + (-b) in expressions
                match &**b {
                    Expression::Negated(b_int) => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b_int);
                        if result_a == ValueSource::Constant(0) {
                            self.add_calculation(Calculation::Negate(result_b))
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else {
                            self.add_calculation(Calculation::Sub(result_a, result_b))
                        }
                    }
                    _ => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b);
                        if result_a == ValueSource::Constant(0) {
                            result_b
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else if result_a <= result_b {
                            self.add_calculation(Calculation::Add(result_a, result_b))
                        } else {
                            self.add_calculation(Calculation::Add(result_b, result_a))
                        }
                    }
                }
            }
            Expression::Product(a, b) => {
                let result_a = self.add_expression(a);
                let result_b = self.add_expression(b);
                if result_a == ValueSource::Constant(0) || result_b == ValueSource::Constant(0) {
                    ValueSource::Constant(0)
                } else if result_a == ValueSource::Constant(1) {
                    result_b
                } else if result_b == ValueSource::Constant(1) {
                    result_a
                } else if result_a == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_b))
                } else if result_b == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_a))
                } else if result_a == result_b {
                    self.add_calculation(Calculation::Square(result_a))
                } else if result_a <= result_b {
                    self.add_calculation(Calculation::Mul(result_a, result_b))
                } else {
                    self.add_calculation(Calculation::Mul(result_b, result_a))
                }
            }
            Expression::Scaled(a, f) => {
                if *f == F::ZERO {
                    ValueSource::Constant(0)
                } else if *f == F::ONE {
                    self.add_expression(a)
                } else {
                    let cst = self.add_constant(f);
                    let result_a = self.add_expression(a);
                    self.add_calculation(Calculation::Mul(result_a, cst))
                }
            }
        }
    }

    /// Creates a new evaluation structure
    pub fn instance(&self) -> EvaluationData<F> {
        EvaluationData {
            intermediates: vec![F::ZERO; self.num_intermediates],
            rotations: vec![0usize; self.rotations.len()],
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<B: PolynomialRepresentation>(
        &self,
        data: &mut EvaluationData<F>,
        fixed: &[Polynomial<F, B>],
        advice: &[Polynomial<F, B>],
        instance: &[Polynomial<F, B>],
        challenges: &[F],
        beta: &F,
        theta: &F,
        trash_challenge: &F,
        y: &F,
        previous_value: &F,
        idx: usize,
        log_scale: u32,
        log_n: u32,
    ) -> F {
        // All rotation index values
        for (rot_idx, rot) in self.rotations.iter().enumerate() {
            data.rotations[rot_idx] = get_rotation_idx(idx, *rot, log_scale, log_n);
        }

        // All calculations, with cached intermediate results
        for calc in self.calculations.iter() {
            data.intermediates[calc.target] = calc.calculation.evaluate(
                &data.rotations,
                &self.constants,
                &data.intermediates,
                fixed,
                advice,
                instance,
                challenges,
                beta,
                theta,
                trash_challenge,
                y,
                previous_value,
            );
        }

        // Return the result of the last calculation (if any)
        if let Some(calc) = self.calculations.last() {
            data.intermediates[calc.target]
        } else {
            F::ZERO
        }
    }
}

/// Simple evaluation of an expression
pub fn evaluate<F: Field, B: PolynomialRepresentation>(
    expression: &Expression<F>,
    log_n: u32,
    log_scale: u32,
    fixed: &[Polynomial<F, B>],
    advice: &[Polynomial<F, B>],
    instance: &[Polynomial<F, B>],
    challenges: &[F],
) -> Vec<F> {
    let size = 1usize << log_n;
    let mut values = vec![F::ZERO; size];
    parallelize(&mut values, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = start + i;
            *value = expression.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| {
                    fixed[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, log_scale, log_n)]
                },
                &|query| {
                    advice[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, log_scale, log_n)]
                },
                &|query| {
                    instance[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, log_scale, log_n)]
                },
                &|challenge| challenges[challenge.index()],
                &|a| -a,
                &|a, b| a + b,
                &|a, b| a * b,
                &|a, scalar| a * scalar,
            );
        }
    });
    values
}

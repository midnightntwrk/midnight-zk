use ff::{PrimeField, WithSmallOrderMulGroup};
use group::ff::Field;

use super::{ConstraintSystem, Expression};
use crate::{
    plonk::{logup, permutation, trash, Any},
    poly::{EvaluationDomain, Polynomial, PolynomialRepresentation, Rotation},
    utils::arithmetic::parallelize,
};

/// Return the index in the polynomial of size `isize` after rotation `rot`.
pub(crate) fn get_rotation_idx(idx: usize, rot: i32, rot_scale: i32, isize: i32) -> usize {
    (((idx as i32) + (rot * rot_scale)).rem_euclid(isize)) as usize
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
#[derive(Clone, Debug)]
pub struct Evaluator<F: PrimeField> {
    ///  Custom gates evaluation
    pub custom_gates: GraphEvaluator<F>,
    /// Flattened custom gates for fast evaluation.
    pub custom_gates_flat: FlatGraphEvaluator<F>,
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

// ---------------------------------------------------------------------------
// Flattened graph evaluator — pre-resolves all ValueSource lookups into
// unified buffer indices for a tighter evaluation loop.
// ---------------------------------------------------------------------------

/// Operation kind for the flattened evaluator.
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum FlatOpKind {
    Add,
    Sub,
    Mul,
    Square,
    Double,
    Negate,
    /// Fused multiply-add: `dst = a * b + c`. Used for Horner steps.
    MulAdd,
}

/// A single flattened operation. All operands are indices into the unified
/// values buffer — no enum dispatch needed at evaluation time.
#[derive(Clone, Copy, Debug)]
pub struct FlatOp {
    pub kind: FlatOpKind,
    pub dst: u32,
    /// Source operands (indices into the values buffer).
    /// - Binary ops use `a` and `b`.
    /// - Unary ops use `a` only.
    /// - MulAdd uses `a`, `b`, and `c`.
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

/// Column read: load a value from a polynomial column at a rotated index.
#[derive(Clone, Copy, Debug)]
pub struct ColumnRead {
    /// 0 = Fixed, 1 = Advice, 2 = Instance, 3 = Challenge.
    pub col_type: u8,
    /// Column index within its type.
    pub col_idx: u16,
    /// Index into the rotations array (for Fixed/Advice/Instance).
    /// For Challenge: the challenge index.
    pub rot_or_idx: u8,
    /// Destination index in the values buffer.
    pub dst: u32,
}

/// Pre-flattened graph for fast evaluation. Built from a [`GraphEvaluator`]
/// at keygen time via [`GraphEvaluator::flatten`].
///
/// The values buffer layout:
/// ```text
/// [0 .. C)                   constants (static)
/// [C .. C+5)                 beta, theta, trash_challenge, y, previous_value
/// [C+5 .. C+5+R)             column read results (loaded per element)
/// [C+5+R .. C+5+R+I)         intermediates (computed per element)
/// ```
#[derive(Clone, Debug)]
pub struct FlatGraphEvaluator<F> {
    /// Pre-loaded constants (copied into values buffer once per prove).
    pub constants: Vec<F>,
    /// Rotation values (same as GraphEvaluator::rotations).
    pub rotations: Vec<i32>,
    /// Column reads to perform at the start of each element.
    pub column_reads: Vec<ColumnRead>,
    /// Flattened operations.
    pub ops: Vec<FlatOp>,
    /// Total values buffer length.
    pub values_len: usize,
    /// Index offsets for named slots.
    pub beta_idx: u32,
    pub theta_idx: u32,
    pub trash_challenge_idx: u32,
    pub y_idx: u32,
    pub previous_value_idx: u32,
    /// Index of the final result.
    pub result_idx: u32,
}

impl<F: PrimeField> GraphEvaluator<F> {
    /// Convert this graph into a flattened evaluator for faster evaluation.
    pub fn flatten(&self) -> FlatGraphEvaluator<F> {
        let num_constants = self.constants.len();
        let challenge_offset = num_constants;
        let beta_idx = challenge_offset as u32;
        let theta_idx = (challenge_offset + 1) as u32;
        let trash_challenge_idx = (challenge_offset + 2) as u32;
        let y_idx = (challenge_offset + 3) as u32;
        let previous_value_idx = (challenge_offset + 4) as u32;

        let column_read_offset = challenge_offset + 5;

        // First pass: collect column reads and assign their buffer indices.
        let mut column_reads = Vec::new();
        let mut column_read_map: Vec<(ValueSource, u32)> = Vec::new();

        fn find_column_reads(
            calc: &Calculation,
            reads: &mut Vec<(ValueSource, u32)>,
            column_reads: &mut Vec<ColumnRead>,
            base_offset: usize,
        ) {
            let mut check = |vs: &ValueSource| {
                if matches!(
                    vs,
                    ValueSource::Fixed(..)
                        | ValueSource::Advice(..)
                        | ValueSource::Instance(..)
                        | ValueSource::Challenge(..)
                ) {
                    if !reads.iter().any(|(v, _)| *v == *vs) {
                        let dst = (base_offset + reads.len()) as u32;
                        let cr = match *vs {
                            ValueSource::Fixed(c, r) => ColumnRead {
                                col_type: 0,
                                col_idx: c as u16,
                                rot_or_idx: r as u8,
                                dst,
                            },
                            ValueSource::Advice(c, r) => ColumnRead {
                                col_type: 1,
                                col_idx: c as u16,
                                rot_or_idx: r as u8,
                                dst,
                            },
                            ValueSource::Instance(c, r) => ColumnRead {
                                col_type: 2,
                                col_idx: c as u16,
                                rot_or_idx: r as u8,
                                dst,
                            },
                            ValueSource::Challenge(i) => ColumnRead {
                                col_type: 3,
                                col_idx: i as u16,
                                rot_or_idx: 0,
                                dst,
                            },
                            _ => unreachable!(),
                        };
                        column_reads.push(cr);
                        reads.push((*vs, dst));
                    }
                }
            };

            match calc {
                Calculation::Add(a, b)
                | Calculation::Sub(a, b)
                | Calculation::Mul(a, b) => {
                    check(a);
                    check(b);
                }
                Calculation::Square(a)
                | Calculation::Double(a)
                | Calculation::Negate(a)
                | Calculation::Store(a) => {
                    check(a);
                }
                Calculation::Horner(s, parts, f) => {
                    check(s);
                    check(f);
                    for p in parts {
                        check(p);
                    }
                }
            }
        }

        for calc_info in &self.calculations {
            find_column_reads(
                &calc_info.calculation,
                &mut column_read_map,
                &mut column_reads,
                column_read_offset,
            );
        }

        let num_column_reads = column_reads.len();
        let intermediates_offset = column_read_offset + num_column_reads;

        // Resolve a ValueSource to a values-buffer index.
        let resolve = |vs: &ValueSource| -> u32 {
            match *vs {
                ValueSource::Constant(idx) => idx as u32,
                ValueSource::Intermediate(idx) => (intermediates_offset + idx) as u32,
                ValueSource::Beta() => beta_idx,
                ValueSource::Theta() => theta_idx,
                ValueSource::TrashChallenge() => trash_challenge_idx,
                ValueSource::Y() => y_idx,
                ValueSource::PreviousValue() => previous_value_idx,
                ValueSource::Fixed(..)
                | ValueSource::Advice(..)
                | ValueSource::Instance(..)
                | ValueSource::Challenge(..) => {
                    column_read_map
                        .iter()
                        .find(|(v, _)| *v == *vs)
                        .unwrap()
                        .1
                }
            }
        };

        // Second pass: flatten calculations into FlatOps.
        let mut ops = Vec::with_capacity(self.calculations.len() * 2);

        for calc_info in &self.calculations {
            let dst = (intermediates_offset + calc_info.target) as u32;
            match &calc_info.calculation {
                Calculation::Add(a, b) => ops.push(FlatOp {
                    kind: FlatOpKind::Add,
                    dst,
                    a: resolve(a),
                    b: resolve(b),
                    c: 0,
                }),
                Calculation::Sub(a, b) => ops.push(FlatOp {
                    kind: FlatOpKind::Sub,
                    dst,
                    a: resolve(a),
                    b: resolve(b),
                    c: 0,
                }),
                Calculation::Mul(a, b) => ops.push(FlatOp {
                    kind: FlatOpKind::Mul,
                    dst,
                    a: resolve(a),
                    b: resolve(b),
                    c: 0,
                }),
                Calculation::Square(v) => ops.push(FlatOp {
                    kind: FlatOpKind::Square,
                    dst,
                    a: resolve(v),
                    b: 0,
                    c: 0,
                }),
                Calculation::Double(v) => ops.push(FlatOp {
                    kind: FlatOpKind::Double,
                    dst,
                    a: resolve(v),
                    b: 0,
                    c: 0,
                }),
                Calculation::Negate(v) => ops.push(FlatOp {
                    kind: FlatOpKind::Negate,
                    dst,
                    a: resolve(v),
                    b: 0,
                    c: 0,
                }),
                Calculation::Store(v) => {
                    // Store is a copy from a column/constant/etc into an intermediate.
                    // In the flattened format, the column read is pre-loaded, so this
                    // is just a copy: dst = src.
                    let src = resolve(v);
                    // Optimization: if dst == src, skip the copy. Otherwise emit Add with 0.
                    if dst != src {
                        ops.push(FlatOp {
                            kind: FlatOpKind::Add,
                            dst,
                            a: src,
                            b: 0, // Constant(0) = F::ZERO, add identity.
                            c: 0,
                        });
                    }
                }
                Calculation::Horner(start, parts, factor) => {
                    let start_idx = resolve(start);
                    let factor_idx = resolve(factor);
                    // First: dst = start_value.
                    if dst != start_idx {
                        ops.push(FlatOp {
                            kind: FlatOpKind::Add,
                            dst,
                            a: start_idx,
                            b: 0,
                            c: 0,
                        });
                    }
                    // Then: dst = dst * factor + part[i].
                    for part in parts {
                        ops.push(FlatOp {
                            kind: FlatOpKind::MulAdd,
                            dst,
                            a: dst,
                            b: factor_idx,
                            c: resolve(part),
                        });
                    }
                }
            }
        }

        let values_len = intermediates_offset + self.num_intermediates;
        let result_idx = ops.last().map_or(0, |op| op.dst);

        FlatGraphEvaluator {
            constants: self.constants.clone(),
            rotations: self.rotations.clone(),
            column_reads,
            ops,
            values_len,
            beta_idx,
            theta_idx,
            trash_challenge_idx,
            y_idx,
            previous_value_idx,
            result_idx,
        }
    }
}

impl<F: PrimeField> FlatGraphEvaluator<F> {
    /// Create a fresh values buffer, pre-filled with constants.
    pub fn new_values_buffer(&self, beta: &F, theta: &F, trash_challenge: &F, y: &F) -> Vec<F> {
        let mut values = vec![F::ZERO; self.values_len];
        values[..self.constants.len()].copy_from_slice(&self.constants);
        values[self.beta_idx as usize] = *beta;
        values[self.theta_idx as usize] = *theta;
        values[self.trash_challenge_idx as usize] = *trash_challenge;
        values[self.y_idx as usize] = *y;
        values
    }

    /// Evaluate the graph at one domain element. The `values` buffer is reused
    /// across elements (only column reads and intermediates are overwritten).
    #[inline]
    pub fn evaluate<B: PolynomialRepresentation>(
        &self,
        values: &mut [F],
        fixed: &[Polynomial<F, B>],
        advice: &[Polynomial<F, B>],
        instance: &[Polynomial<F, B>],
        challenges: &[F],
        rotations: &[usize],
        previous_value: &F,
    ) -> F {
        values[self.previous_value_idx as usize] = *previous_value;

        // Step 1: Load column values into the buffer.
        for cr in &self.column_reads {
            values[cr.dst as usize] = match cr.col_type {
                0 => fixed[cr.col_idx as usize][rotations[cr.rot_or_idx as usize]],
                1 => advice[cr.col_idx as usize][rotations[cr.rot_or_idx as usize]],
                2 => instance[cr.col_idx as usize][rotations[cr.rot_or_idx as usize]],
                3 => challenges[cr.col_idx as usize],
                _ => unreachable!(),
            };
        }

        // Step 2: Evaluate flattened operations.
        for op in &self.ops {
            let d = op.dst as usize;
            values[d] = match op.kind {
                FlatOpKind::Add => values[op.a as usize] + values[op.b as usize],
                FlatOpKind::Sub => values[op.a as usize] - values[op.b as usize],
                FlatOpKind::Mul => values[op.a as usize] * values[op.b as usize],
                FlatOpKind::Square => values[op.a as usize].square(),
                FlatOpKind::Double => values[op.a as usize].double(),
                FlatOpKind::Negate => -values[op.a as usize],
                FlatOpKind::MulAdd => {
                    values[op.a as usize] * values[op.b as usize] + values[op.c as usize]
                }
            };
        }

        values[self.result_idx as usize]
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluator<F> {
    /// Creates a new evaluation structure
    pub fn new(cs: &ConstraintSystem<F>) -> Self {
        let dummy_flat = FlatGraphEvaluator {
            constants: Vec::new(),
            rotations: Vec::new(),
            column_reads: Vec::new(),
            ops: Vec::new(),
            values_len: 0,
            beta_idx: 0,
            theta_idx: 0,
            trash_challenge_idx: 0,
            y_idx: 0,
            previous_value_idx: 0,
            result_idx: 0,
        };
        let mut ev = Evaluator {
            custom_gates: GraphEvaluator::default(),
            custom_gates_flat: dummy_flat,
            lookups: Vec::new(),
            trashcans: Vec::new(),
        };

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

        // Flatten the custom gates graph for faster evaluation.
        ev.custom_gates_flat = ev.custom_gates.flatten();
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
        let rot_scale = 1 << (B::k(domain) - domain.k());
        let omega = B::omega(domain);
        let isize = size as i32;
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
            // Custom gates — use the flattened evaluator for reduced dispatch overhead.
            let flat = &self.custom_gates_flat;
            parallelize(&mut values, |values, start| {
                let mut buf = flat.new_values_buffer(&beta, &theta, &trash_challenge, &y);
                let mut rot_indices = vec![0usize; flat.rotations.len()];
                for (i, value) in values.iter_mut().enumerate() {
                    let idx = start + i;
                    for (ri, rot) in flat.rotations.iter().enumerate() {
                        rot_indices[ri] = get_rotation_idx(idx, *rot, rot_scale, isize);
                    }
                    *value = flat.evaluate::<B>(
                        &mut buf, fixed, advice, instance, challenges, &rot_indices, value,
                    );
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
                    .iter()
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
                        let r_next = get_rotation_idx(idx, 1, rot_scale, isize);
                        let r_last = get_rotation_idx(idx, last_rotation.0, rot_scale, isize);

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
                        for set_idx in 0..sets.len() {
                            if set_idx != 0 {
                                *value = *value * y
                                    + (permutation_product_cosets[set_idx][idx]
                                        - permutation_product_cosets[set_idx - 1][r_last])
                                        * l0[idx];
                            }
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

            // Lookups
            for (n, lookup) in lookups.iter().enumerate() {
                // Polynomials required for this lookup.
                // Calculated here so these only have to be kept in memory for the short time
                // they are actually needed.
                let helper_cosets: Vec<_> = lookup
                    .helper_polys
                    .iter()
                    .map(|h| B::coeff_to_self(domain, h.clone()))
                    .collect();
                let aggregator_coset = B::coeff_to_self(domain, lookup.aggregator_poly.clone());
                let multiplicities_coset = B::coeff_to_self(domain, lookup.multiplicities.clone());

                // Lookup constraints
                parallelize(&mut values, |values, start| {
                    let lookup_eval = &self.lookups[n];
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;
                        let r_next = get_rotation_idx(idx, 1, rot_scale, isize);

                        // (l_0(X) + l_last(X)) * Z(X) = 0
                        *value = *value * y + aggregator_coset[idx] * (l0[idx] + l_last[idx]);

                        let mut sum_helpers = F::ZERO;
                        let mut table_value = F::ZERO;
                        let mut selector = F::ZERO;
                        for (fi, lookup_eval) in lookup_eval.iter().enumerate() {
                            let mut eval_data = lookup_eval.graph.instance();
                            lookup_eval.graph.evaluate(
                                &mut eval_data,
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
                                rot_scale,
                                isize,
                            );

                            let sum_partial_products =
                                eval_data.resolve(lookup_eval.sum_partial_products);
                            let product = eval_data.resolve(lookup_eval.product);

                            // We only resolve the table and selector in the first batch
                            if fi == 0 {
                                table_value = eval_data.resolve(lookup_eval.table);
                                selector = eval_data.resolve(lookup_eval.selector);
                            }

                            // Helper constraint: h(X) · ∏ⱼ(fⱼ(X) + β) = Σⱼ ∏_{k≠j}(fₖ(X) + β)
                            *value = *value * y + helper_cosets[fi][idx] * product
                                - sum_partial_products;

                            sum_helpers += helper_cosets[fi][idx];
                        }

                        // Accumulator constraint:
                        // (Z(ωX) - Z(X)- s·Σᵢhᵢ(X))·(t(X) + β) + m(X) = 0
                        *value = *value * y
                            + l_active_row[idx]
                                * ((aggregator_coset[r_next]
                                    - aggregator_coset[idx]
                                    - selector * sum_helpers)
                                    * table_value
                                    + multiplicities_coset[idx]);
                    }
                });
            }

            // Trashcans
            for (n, trash) in trashcans.iter().enumerate() {
                // Polynomials required for this trash argument.
                // Calculated here so these only have to be kept in memory for the short time
                // they are actually needed.
                let trash_poly = B::coeff_to_self(domain, trash.trash_poly.clone());

                // Trash argument constraints.
                parallelize(&mut values, |values, start| {
                    let trash_evaluator = &self.trashcans[n];
                    let argument = &cs.trashcans[n];
                    let mut eval_data = trash_evaluator.instance();
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;

                        let compressed_expression = trash_evaluator.evaluate(
                            &mut eval_data,
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
                            rot_scale,
                            isize,
                        );

                        let q = match argument.selector() {
                            Expression::Fixed(query) => fixed[query.column_index()][idx],
                            _ => unreachable!(),
                        };

                        // compressed_expressions - (1 - q) * trash
                        *value = *value * y + (compressed_expression - (one - q) * trash_poly[idx]);
                    }
                });
            }
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
        rot_scale: i32,
        isize: i32,
    ) -> F {
        // All rotation index values
        for (rot_idx, rot) in self.rotations.iter().enumerate() {
            data.rotations[rot_idx] = get_rotation_idx(idx, *rot, rot_scale, isize);
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
    size: usize,
    rot_scale: i32,
    fixed: &[Polynomial<F, B>],
    advice: &[Polynomial<F, B>],
    instance: &[Polynomial<F, B>],
    challenges: &[F],
) -> Vec<F> {
    let mut values = vec![F::ZERO; size];
    let isize = size as i32;
    parallelize(&mut values, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = start + i;
            *value = expression.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| {
                    fixed[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, rot_scale, isize)]
                },
                &|query| {
                    advice[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, rot_scale, isize)]
                },
                &|query| {
                    instance[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, rot_scale, isize)]
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

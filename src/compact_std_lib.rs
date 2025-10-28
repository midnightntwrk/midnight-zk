//! A collection of a full set of functionalities needed by compact &
//! other components of Midnight's stack.
//!
//! This library uses a fixed configuration, meaning that regardless of what one
//! uses, it will always consist of the same columns, lookups, permutation
//! enabled columns, or gates. The motivation for this is twofold:
//!
//! * It facilitates recursion (we always aggregate circuits that have the same
//!   verification logic).
//!
//! * We could optimise the verifier, who can store part of the circuit
//!   description in memory and does not need to reproduce it everytime it
//!   receives a new proof.

use std::{cell::RefCell, cmp::max, convert::TryInto, fmt::Debug, rc::Rc};

use halo2_proofs::{
    circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, ErrorFront as Error, ProvingKey, VerifyingKey},
    poly::kzg::commitment::ParamsKZG,
};
use halo2curves::secp256k1::{self, Secp256k1};
use num_bigint::BigUint;

use crate::{
    biguint::biguint_gadget::BigUintGadget,
    ecc::{
        foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
        hash_to_curve::HashToCurveGadget,
        native::{EccChip, EccConfig, NB_EDWARDS_COLS},
    },
    field::{
        decomposition::{
            chip::{P2RDecompositionChip, P2RDecompositionConfig},
            pow2range::{Pow2RangeChip, NB_POW2RANGE_COLS},
        },
        foreign::{
            nb_field_chip_columns, params::MultiEmulationParams, FieldChip, FieldChipConfig,
        },
        native::NB_ARITH_COLS,
        NativeChip, NativeConfig, NativeGadget,
    },
    hash::{
        poseidon::{poseidon_gadget::PoseidonGadget, P128Pow5T3, Pow5Chip, Pow5Config},
        sha256::{Sha256, Table11Chip, Table11Config},
    },
    instructions::{
        hash_to_curve::HashToCurveInstructions, ArithInstructions, AssertionInstructions,
        AssignmentInstructions, BinaryInstructions, BitwiseInstructions, CanonicityInstructions,
        ComparisonInstructions, ControlFlowInstructions, ConversionInstructions,
        DecompositionInstructions, EqualityInstructions, FieldInstructions, HashInstructions,
        PublicInputInstructions, RangeCheckInstructions, ZeroInstructions,
    },
    types::{
        AssignedBit, AssignedByte, AssignedNative, AssignedNativePoint, Bit, InnerValue,
        Instantiable,
    },
    utils::{BlstRealTest, ComposableChip},
};

const SHA256_SIZE_IN_WORDS: usize = 8;
const SHA256_SIZE_IN_BYTES: usize = 4 * SHA256_SIZE_IN_WORDS;

type C = blstrs::ExtendedPoint;
type F = blstrs::Scalar;

// Type aliases, for readability.
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
type Secp256k1BaseChip = FieldChip<F, secp256k1::Fp, MultiEmulationParams, NG>;
type Secp256k1ScalarChip = FieldChip<F, secp256k1::Fq, MultiEmulationParams, NG>;
type Secp256k1Chip = ForeignEccChip<F, Secp256k1, MultiEmulationParams, Secp256k1ScalarChip, NG>;

#[derive(Debug, Clone)]
/// Configured chips for [ZkStdLib].
pub struct ZkStdLibConfig {
    native_config: NativeConfig,
    core_decomposition_config: P2RDecompositionConfig,
    ecc_config: EccConfig,
    table11_config: Table11Config,
    pow5_config: Pow5Config<F, 3, 2>,
    secp256k1_scalar_config: FieldChipConfig,
    secp256k1_config: ForeignEccConfig<Secp256k1>,
}

/// The `ZkStdLib` exposes all tools that are used in circuit generation.
#[derive(Debug, Clone)]
pub struct ZkStdLib {
    native_gadget: NG,
    core_decomposition_chip: P2RDecompositionChip<F>,
    ecc_chip: EccChip<C>,
    sha256_chip: Table11Chip<F>,
    poseidon_gadget: PoseidonGadget<F>,
    htc_gadget: HashToCurveGadget<F, C, AssignedNative<F>, PoseidonGadget<F>, EccChip<C>>,
    biguint_gadget: BigUintGadget<F, NG>,
    secp256k1_scalar_chip: Secp256k1ScalarChip,
    secp256k1_curve_chip: Secp256k1Chip,

    // A flag that indicates if the SHA chip has been used. This way we can load the SHA table only
    // when necessary (thus reducing the min_k in some cases).
    used_sha: Rc<RefCell<bool>>,
}

impl ZkStdLib {
    /// Creates a new [ZkStdLib] given its config
    pub fn new(config: &ZkStdLibConfig, max_bit_len: usize) -> Self {
        let native_chip = NativeChip::new(&config.native_config, &());
        let core_decomposition_chip =
            P2RDecompositionChip::new(&config.core_decomposition_config, &max_bit_len);
        let native_gadget = NativeGadget::new(core_decomposition_chip.clone(), native_chip.clone());
        let ecc_chip = EccChip::new(&config.ecc_config, &native_gadget);
        let sha256_chip = Table11Chip::construct(config.table11_config.clone());
        let pow5_chip = Pow5Chip::construct(config.pow5_config.clone());
        let poseidon_gadget = PoseidonGadget::new(&pow5_chip);
        let htc_gadget = HashToCurveGadget::new(&poseidon_gadget, &ecc_chip);
        let biguint_gadget = BigUintGadget::new(&native_gadget);
        let secp256k1_scalar_chip = FieldChip::new(&config.secp256k1_scalar_config, &native_gadget);
        let secp256k1_curve_chip = ForeignEccChip::new(
            &config.secp256k1_config,
            &native_gadget,
            &secp256k1_scalar_chip,
        );

        Self {
            native_gadget,
            core_decomposition_chip,
            ecc_chip,
            sha256_chip,
            poseidon_gadget,
            htc_gadget,
            biguint_gadget,
            secp256k1_scalar_chip,
            secp256k1_curve_chip,
            used_sha: Rc::new(RefCell::new(false)),
        }
    }

    /// Configure [ZkStdLib] from scratch.
    pub fn configure(meta: &mut ConstraintSystem<F>) -> ZkStdLibConfig {
        let nb_advice_cols = [
            NB_ARITH_COLS,
            NB_POW2RANGE_COLS,
            4, // The columns for Poseidon
            9, // The shared columns of SHA256 (Table11)
            NB_EDWARDS_COLS,
            nb_field_chip_columns::<F, secp256k1::Fq, MultiEmulationParams>(),
            nb_foreign_ecc_chip_columns::<F, Secp256k1, MultiEmulationParams, secp256k1::Fq>(),
        ]
        .iter()
        .fold(0, |acc, n| max(acc, *n));

        let nb_fixed_cols = [
            NB_ARITH_COLS + 4,
            6, // Shared fixed columns of Poseidon
        ]
        .iter()
        .fold(0, |acc, n| max(acc, *n));

        let advice_columns = (0..nb_advice_cols)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();
        let fixed_columns = (0..nb_fixed_cols)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();
        let instance_column = meta.instance_column();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_columns[..(NB_ARITH_COLS + 4)].try_into().unwrap(),
                instance_column,
            ),
        );

        let core_decomposition_config = {
            let q_pow2range = meta.complex_selector();
            let tag_col = meta.fixed_column();
            let t_tag = meta.lookup_table_column();
            let t_val = meta.lookup_table_column();
            let pow2range_config = Pow2RangeChip::configure(
                meta,
                &advice_columns[1..NB_POW2RANGE_COLS + 1],
                tag_col,
                q_pow2range,
                t_tag,
                t_val,
            );
            P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2range_config))
        };

        let ecc_config =
            EccChip::<C>::configure(meta, &advice_columns[..NB_EDWARDS_COLS].try_into().unwrap());

        let table11_config = Table11Chip::configure(
            meta,
            &advice_columns[..9].try_into().unwrap(),
            fixed_columns[0..4].try_into().unwrap(),
        );

        let pow5_config = Pow5Chip::configure::<P128Pow5T3>(
            meta,
            advice_columns[..3].try_into().unwrap(),
            advice_columns[3],
            fixed_columns[..3].try_into().unwrap(),
            fixed_columns[3..6].try_into().unwrap(),
        );

        let secp256k1_scalar_config = Secp256k1ScalarChip::configure(meta, &advice_columns);

        let secp256k1_config = {
            let base_config = Secp256k1BaseChip::configure(meta, &advice_columns);
            Secp256k1Chip::configure(meta, &base_config, &advice_columns)
        };

        // FIXME: Some chips need this, should we unify the treatment of constants?
        let constants_column = meta.fixed_column();
        meta.enable_constant(constants_column);

        ZkStdLibConfig {
            native_config,
            core_decomposition_config,
            ecc_config,
            table11_config,
            pow5_config,
            secp256k1_scalar_config,
            secp256k1_config,
        }
    }

    /// Load all the tables used by the ZkStdLib chips.
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Table11Chip::load(self.sha256_chip.config().clone(), layouter)?;
        self.core_decomposition_chip.load(layouter)
    }
}

impl ZkStdLib {
    /// Native EccChip.
    pub fn jubjub(&self) -> &EccChip<C> {
        &self.ecc_chip
    }

    /// Gadget for performing in-circuit big-unsigned integer operations.
    pub fn biguint(&self) -> &BigUintGadget<F, NG> {
        &self.biguint_gadget
    }

    /// Chip for performing in-circuit operations over the Secp256k1 scalar
    /// field.
    pub fn secp256k1_scalar(&self) -> &Secp256k1ScalarChip {
        &self.secp256k1_scalar_chip
    }

    /// Chip for performing in-circuit operations over the Secp256k1 curve.
    pub fn secp256k1_curve(&self) -> &Secp256k1Chip {
        &self.secp256k1_curve_chip
    }

    /// Assert that a given assigned bit is true.
    ///
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 10, {
    /// let input: AssignedBit<F> = chip.assign_fixed(layouter, Bit(true))?;
    /// chip.assert_true(layouter, &input)?;
    /// # });
    /// ```
    pub fn assert_true(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_equal_to_fixed(layouter, input, Bit(true))
    }

    /// Assert that a given assigned bit is false
    pub fn assert_false(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_equal_to_fixed(layouter, input, Bit(false))
    }

    /// Returns `1` iff `x < y`.
    ///
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 10, {
    /// let x: AssignedNative<F> = chip.assign_fixed(layouter, F::from(127))?;
    /// let y: AssignedNative<F> = chip.assign_fixed(layouter, F::from(212))?;
    /// let condition = chip.lower_than(layouter, &x, &y, 8)?;
    ///
    /// chip.assert_true(layouter, &condition)?;
    /// # });
    /// ```
    ///
    /// # Panics
    ///
    /// Both `x` and `y` are asserted to be in the range `[0, 2^n)`, if this
    /// condition is violated, the circuit becomes unsatisfiable.
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 10, {
    /// let x: AssignedNative<F> = chip.assign_fixed(layouter, F::from(127))?;
    /// let y: AssignedNative<F> = chip.assign_fixed(layouter, F::from(212))?;
    /// let _condition = chip.lower_than(layouter, &x, &y, 7)?;
    /// # });
    /// ```
    ///
    /// Setting `n > (F::NUM_BITS - 1) / 2` will result in a compile-time
    /// error.
    pub fn lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        n: u32,
    ) -> Result<AssignedBit<F>, Error> {
        let bounded_x = self
            .native_gadget
            .bounded_of_element(layouter, n as usize, x)?;
        let bounded_y = self
            .native_gadget
            .bounded_of_element(layouter, n as usize, y)?;
        self.native_gadget
            .lower_than(layouter, &bounded_x, &bounded_y)
    }

    /// Poseidon hash from a slice of native valure into a native value.
    ///
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 10, {
    /// let x: AssignedNative<F> = chip.assign_fixed(layouter, F::from(127))?;
    /// let y: AssignedNative<F> = chip.assign_fixed(layouter, F::from(212))?;
    ///
    /// let _hash = chip.poseidon(layouter, &[x, y])?;
    /// # });
    /// ```
    pub fn poseidon(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedNative<F>],
    ) -> Result<AssignedNative<F>, Error> {
        self.poseidon_gadget.hash(layouter, input)
    }

    /// Hashes a slice of assigned values into `(x,y)` coordinates which are
    /// guaranteed to be in the curve `C`. For usage, see [HashToCurveGadget].
    pub fn hash_to_curve(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedNative<F>,
    ) -> Result<AssignedNativePoint<C>, Error> {
        self.htc_gadget.hash_to_curve(layouter, input)
    }

    /// Sha256.
    /// Takes as input a slice of assigned bytes and returns the assigned
    /// input/output in bytes.
    /// We assume the field uses little endian encoding.
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 13, {
    /// let input = chip.assign_many(
    ///     layouter,
    ///     &[
    ///         Value::known(Byte(13)),
    ///         Value::known(Byte(226)),
    ///         Value::known(Byte(119)),
    ///         Value::known(Byte(5)),
    ///     ],
    /// )?;
    ///
    /// let _hash = chip.sha256(layouter, &input)?;
    /// # });
    /// ```
    pub fn sha256(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>], // F -> decompose_bytes -> hash
    ) -> Result<[AssignedByte<F>; SHA256_SIZE_IN_BYTES], Error> {
        *self.used_sha.borrow_mut() = true;

        let hasher = Sha256::new(self.sha256_chip.clone(), self.native_gadget.clone())?;
        hasher.hash(layouter, input)
    }
}

impl<T> AssignmentInstructions<F, T> for ZkStdLib
where
    T: Instantiable<F>,
    T::Element: Clone,
    NG: AssignmentInstructions<F, T>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<T::Element>,
    ) -> Result<T, Error> {
        self.native_gadget.assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: T::Element,
    ) -> Result<T, Error> {
        self.native_gadget.assign_fixed(layouter, constant)
    }

    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<T::Element>],
    ) -> Result<Vec<T>, Error> {
        self.native_gadget.assign_many(layouter, values)
    }
}

impl<T> PublicInputInstructions<F, T> for ZkStdLib
where
    T: Instantiable<F>,
    T::Element: Clone,
    NG: PublicInputInstructions<F, T>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_gadget.as_public_input(layouter, assigned)
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<(), Error> {
        self.native_gadget
            .constrain_as_public_input(layouter, assigned)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<<T>::Element>,
    ) -> Result<T, Error> {
        self.native_gadget.assign_as_public_input(layouter, value)
    }
}

impl<T> AssertionInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    NG: AssertionInstructions<F, T>,
{
    fn assert_equal(&self, layouter: &mut impl Layouter<F>, x: &T, y: &T) -> Result<(), Error> {
        self.native_gadget.assert_equal(layouter, x, y)
    }

    fn assert_not_equal(&self, layouter: &mut impl Layouter<F>, x: &T, y: &T) -> Result<(), Error> {
        self.native_gadget.assert_not_equal(layouter, x, y)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_equal_to_fixed(layouter, x, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_not_equal_to_fixed(layouter, x, constant)
    }
}

impl<T> EqualityInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    NG: EqualityInstructions<F, T>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        y: &T,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_equal(layouter, x, y)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_equal_to_fixed(layouter, x, constant)
    }
}

impl<T1, T2> ConversionInstructions<F, T1, T2> for ZkStdLib
where
    T1: InnerValue,
    T2: InnerValue,
    NG: ConversionInstructions<F, T1, T2>,
{
    fn convert_value(&self, x: &T1::Element) -> Option<T2::Element> {
        ConversionInstructions::<_, T1, T2>::convert_value(&self.native_gadget, x)
    }

    fn convert(&self, layouter: &mut impl Layouter<F>, x: &T1) -> Result<T2, Error> {
        self.native_gadget.convert(layouter, x)
    }
}

impl CanonicityInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn le_bits_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.le_bits_lower_than(layouter, bits, bound)
    }

    fn le_bits_geq_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.le_bits_geq_than(layouter, bits, bound)
    }
}

impl DecompositionInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn assigned_to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        self.native_gadget
            .assigned_to_le_bits(layouter, x, nb_bits, enforce_canonical)
    }

    fn assigned_to_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        self.native_gadget
            .assigned_to_le_bytes(layouter, x, nb_bytes)
    }

    fn assigned_to_le_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits_per_chunk: usize,
        nb_chunks: Option<usize>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_gadget
            .assigned_to_le_chunks(layouter, x, nb_bits_per_chunk, nb_chunks)
    }
}

impl ArithInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(F, AssignedNative<F>)],
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget
            .linear_combination(layouter, terms, constant)
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        multiplying_constant: Option<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.mul(layouter, x, y, multiplying_constant)
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.div(layouter, x, y)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.inv(layouter, x)
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.inv0(layouter, x)
    }
}

impl ZeroInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl ControlFlowInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.select(layouter, cond, x, y)
    }
}

impl FieldInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn order(&self) -> BigUint {
        self.native_gadget.order()
    }
}

impl RangeCheckInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn assign_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        bound: &BigUint,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget
            .assign_lower_than_fixed(layouter, value, bound)
    }

    fn assert_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bound: &BigUint,
    ) -> Result<(), Error> {
        self.native_gadget
            .assert_lower_than_fixed(layouter, x, bound)
    }
}

impl BinaryInstructions<F> for ZkStdLib {
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.and(layouter, bits)
    }

    fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.or(layouter, bits)
    }

    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.xor(layouter, bits)
    }

    fn not(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.not(layouter, bit)
    }
}

impl BitwiseInstructions<F, AssignedNative<F>> for ZkStdLib {}

/// Circuit structure which is used to create any circuit that can be compiled
/// into keys using the ZK standard library.
#[derive(Clone, Debug, Default)]
pub struct MidnightCircuit<R: Relation>(R);

impl<R: Relation> From<R> for MidnightCircuit<R> {
    fn from(relation: R) -> Self {
        Self(relation)
    }
}

/// Helper trait, used to abstract the circuit developer from Halo2's
/// boilerplate.
///
/// All implementors of this trait can be used to create a [MidnightCircuit] via
/// `MidnightCircuit::new()`.
///
/// `Relation` has a default implementation for loading only the tables
/// needed for the requested chips. The developer needs to implement the
/// function [Relation::circuit], which essentially contains the
/// statement of the proof we are creating.
///
/// # Example
///
/// ```
/// # use blstrs::G1Affine;
/// # use halo2_proofs::{
/// #     circuit::{Layouter, Value},
/// #     plonk::ErrorFront as Error,
/// #     poly::kzg::commitment::ParamsKZG,
/// # };
/// # use midnight_circuits::{
/// #     instructions::{AssignmentInstructions, PublicInputInstructions},
/// #     types::{AssignedByte, Byte, Instantiable},
/// #     testing_utils::{real_test_api::{check_vk, BlstRealTest}},
/// #     compact_std_lib::{self, MidnightCircuit, Relation, ZkStdLib},
/// # };
/// # use rand::{Rng, SeedableRng};
/// # use rand_chacha::ChaCha8Rng;
/// # use sha2::Digest;
/// #
/// type F = blstrs::Scalar;
///
/// #[derive(Clone, Default)]
/// struct ShaPreImageCircuit {
///     input_bytes: [Value<Byte>; 24], // 192 = 24 * 8
/// }
///
/// impl Relation for ShaPreImageCircuit {
///     // When defining a circuit, one must clearly state the instance and the witness
///     // of the underlying NP-relation.
///     type Instance = [u8; 32];
///     type Witness = [u8; 24];
///
///     // The log2 of the number of rows in the circuit table.
///     const K: u32 = 13;
///
///     // We must specify how the instance is converted into raw field elements to
///     // be process by the prover/verifier. The order here must be consistent with
///     // the order in which public inputs are constrained/assigned in [circuit].
///     fn format_instance(instance: &Self::Instance) -> Vec<F> {
///         instance
///             .iter()
///             .flat_map(|b| AssignedByte::<F>::as_public_input(&Byte(*b)))
///             .collect()
///     }
///
///     fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
///         ShaPreImageCircuit {
///             input_bytes: witness.map(Byte).map(Value::known),
///         }
///     }
///
///     // Define the logic of the NP-relation being proved.
///     fn circuit(
///         &self,
///         std_lib: &ZkStdLib,
///         layouter: &mut impl Layouter<F>,
///     ) -> Result<(), Error> {
///         let assigned_input = std_lib.assign_many(layouter, &self.input_bytes)?;
///         let output = std_lib.sha256(layouter, &assigned_input)?;
///         output
///             .iter()
///             .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
///     }
/// }
///
/// const K: u32 = 13;
///
/// let srs: ParamsKZG<_> = BlstRealTest::<MidnightCircuit<ShaPreImageCircuit>>::gen_srs(K, false);
///
/// let vk = compact_std_lib::setup_vk::<ShaPreImageCircuit>(&srs);
/// let pk = compact_std_lib::setup_pk::<ShaPreImageCircuit>(&srs, &vk);
///
/// let mut rng = ChaCha8Rng::from_entropy();
/// let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
/// let instance = sha2::Sha256::digest(witness).into();
///
/// let proof = compact_std_lib::prove::<ShaPreImageCircuit>(&srs, &pk, &instance, &witness);
///
/// compact_std_lib::verify::<ShaPreImageCircuit>(&srs, &vk, &instance, proof)
/// ```
pub trait Relation: Clone + Default + Sized {
    /// The instance of the NP-relation described by this circuit.
    type Instance;

    /// The witness of the NP-relation described by this circuit.
    type Witness;

    /// An upper-bound on the circuit size (log2 of number of rows).
    ///
    /// It is recommended to pick the minimum `K` possible. For that, once you
    /// have a valid upper-bound, you can compute the min key of a circuit
    /// with [halo2_proofs::dev::cost_model::from_circuit_to_cost_model_options],
    /// passing as arguments `(k_upper_bound, circuit, instance)`.
    const K: u32;

    /// Produces a vector of field elements in PLONK format representing the
    /// given [Self::Instance].
    fn format_instance(instance: &Self::Instance) -> Vec<F>;

    /// Creates a circuit, ready to be proved, from an instance-witness pair.
    fn from_statement(instance: &Self::Instance, witness: &Self::Witness) -> Self;

    /// Defines the circuit's logic.
    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error>;
}

impl<R: Relation> Circuit<F> for MidnightCircuit<R> {
    type Config = ZkStdLibConfig;

    // FIXME: this could be parametrised by MidnightCircuit.
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ZkStdLib::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let zk_std_lib = ZkStdLib::new(&config, R::K as usize - 2);

        self.0.circuit(
            &zk_std_lib,
            &mut layouter.namespace(|| "Running logic circuit"),
        )?;

        // We load the tables at the end, once we have figured out what chips/gadgets
        // were actually used.
        zk_std_lib.core_decomposition_chip.load(&mut layouter)?;
        if *zk_std_lib.used_sha.borrow() {
            Table11Chip::load(zk_std_lib.sha256_chip.config().clone(), &mut layouter)?;
        }

        Ok(())
    }
}

/// Generates a verifying key for a `MidnightCircuit<R>` circuit.
pub fn setup_vk<R: Relation>(params: &ParamsKZG<blstrs::Bls12>) -> VerifyingKey<blstrs::G1Affine> {
    BlstRealTest::<MidnightCircuit<R>>::setup_vk(params, &MidnightCircuit::<R>::default())
}

/// Generates a proving key for a `MidnightCircuit<R>` circuit.
pub fn setup_pk<R: Relation>(
    params: &ParamsKZG<blstrs::Bls12>,
    vk: &VerifyingKey<blstrs::G1Affine>,
) -> ProvingKey<blstrs::G1Affine> {
    BlstRealTest::<MidnightCircuit<R>>::setup_pk(params, &MidnightCircuit::<R>::default(), vk)
}

/// Produces a proof of relation `R` for the given instance (using the given
/// proving key and witness).
pub fn prove<R: Relation>(
    params: &ParamsKZG<blstrs::Bls12>,
    pk: &ProvingKey<blstrs::G1Affine>,
    instance: &R::Instance,
    witness: &R::Witness,
) -> Vec<u8> {
    let circuit: MidnightCircuit<R> = R::from_statement(instance, witness).into();
    let pi = R::format_instance(instance);
    BlstRealTest::<MidnightCircuit<R>>::prove(params, pk, &circuit, &[&pi])
}

/// Verifies the given proof of relation `R` with respect to the given instance.
/// Panics if the proof is not valid.
pub fn verify<R: Relation>(
    params: &ParamsKZG<blstrs::Bls12>,
    vk: &VerifyingKey<blstrs::G1Affine>,
    instance: &R::Instance,
    proof: Vec<u8>,
) {
    let pi = R::format_instance(instance);
    BlstRealTest::<MidnightCircuit<R>>::verify(params, vk, &[&pi], proof)
}

use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use ff::Field;
use group::Group;
use midnight_circuits::compact_std_lib::{self, MidnightCircuit};
use midnight_curves::{Fr as JubjubFr, JubjubSubgroup};
use midnight_proofs::{
    circuit::Value, dev::cost_model::dummy_synthesize_run, plonk, poly::kzg::params::ParamsKZG,
};
use midnight_zkir::{
    Error, Instruction, IrType, IrValue,
    Operation::{self, *},
    ZkirRelation,
};
use num_bigint::BigUint;
use num_traits::Num;
use rand_chacha::rand_core::OsRng;

type F = midnight_curves::Fq;

/// Macro to simplify witness HashMap construction
macro_rules! witness {
    ($($key:expr => $value:expr),* $(,)?) => {
        HashMap::from_iter([$(($key, $value.into())),*])
    };
}

#[test]
fn test_load() {
    let load_bool = Load(IrType::Bool);

    // Arity validation: Load requires at least one output.
    assert_invalid_arity(load_bool, vec![], vec![]);

    // Valid arity: One or more outputs is accepted.
    test_static_pass(&[(load_bool, vec![], vec!["out"])], None);
    test_static_pass(&[(load_bool, vec![], vec!["out1", "out2"])], None);

    // Arity validation: Load requires zero inputs.
    assert_invalid_arity(load_bool, vec!["inp"], vec!["out"]);

    // Name uniqueness: Duplicate output names within the same instruction are
    // rejected.
    test_without_witness(
        &[(load_bool, vec![], vec!["out", "out"])],
        Some(Error::DuplicatedName("out".to_string())),
    );

    // Name uniqueness: Variable names must be unique across all instructions.
    test_without_witness(
        &[
            (load_bool, vec![], vec!["out"]),
            (load_bool, vec![], vec!["out"]),
        ],
        Some(Error::DuplicatedName("out".to_string())),
    );

    // Witness validation: Missing witness values produce NotFound errors.
    test_with_witness(
        &[(load_bool, vec![], vec!["out"])],
        witness!("outt" => true),
        vec![],
        Some(Error::NotFound("out".to_string())),
    );

    // Type checking: Witness values must match the declared type.
    test_with_witness(
        &[(load_bool, vec![], vec!["out"])],
        witness!("out" => F::ONE),
        vec![],
        Some(Error::ExpectingType(IrType::Bool, IrType::Native)),
    );

    // Success case: Load with correct witness value and type.
    test_with_witness(
        &[(load_bool, vec![], vec!["out"])],
        witness!("out" => true),
        vec![],
        None,
    );
}

#[test]
fn test_publish() {
    // Arity validation: Publish requires at least one input.
    assert_invalid_arity(Publish, vec![], vec![]);

    // Arity validation: Publish must have zero outputs.
    assert_invalid_arity(Publish, vec!["inp"], vec!["out"]);

    // Valid arity: One or more inputs with no outputs.
    test_static_pass(&[(Publish, vec!["inp"], vec![])], None);
    test_static_pass(&[(Publish, vec!["inp1", "inp2"], vec![])], None);

    // Variable resolution: Published variables must be defined.
    test_without_witness(
        &[(Publish, vec!["x"], vec![])],
        Some(Error::ParsingError(IrType::Bool, "x".to_string())),
    );
    test_without_witness(
        &[
            (Load(IrType::Native), vec![], vec!["x"]),
            (Publish, vec!["x"], vec![]),
        ],
        None,
    );

    // Success case: Publishing a native field element as public input.
    let neg_one = -F::ONE;
    test_with_witness(
        &[
            (Load(IrType::Native), vec![], vec!["x"]),
            (Publish, vec!["x"], vec![]),
        ],
        witness!("x" => neg_one),
        vec![(neg_one.into(), IrType::Native)],
        None,
    );

    // Multiple publications: The same value can be published multiple times.
    test_with_witness(
        &[
            (Load(IrType::Bool), vec![], vec!["a", "b"]),
            (Publish, vec!["b", "b", "a"], vec![]),
            (Publish, vec!["b"], vec![]),
        ],
        witness!("a" => false, "b" => true),
        vec![
            (true.into(), IrType::Bool),
            (true.into(), IrType::Bool),
            (false.into(), IrType::Bool),
            (true.into(), IrType::Bool),
        ],
        None,
    );
}

#[test]
fn test_assert_equal() {
    // Arity validation: AssertEqual requires exactly 2 inputs and 0 outputs.
    assert_invalid_arity(AssertEqual, vec!["x", "y"], vec!["z"]);
    assert_invalid_arity(AssertEqual, vec!["x", "y", "z"], vec![]);
    test_static_pass(&[(AssertEqual, vec!["x", "y"], vec![])], None);

    // Type support: JubjubScalars do not support equality assertions.
    assert_unsupported(
        AssertEqual,
        vec![IrType::JubjubScalar, IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (AssertEqual, vec!["x", "x"], vec![]),
        ],
    );

    // Type compatibility: Both values must have the same type.
    assert_unsupported(
        AssertEqual,
        vec![IrType::JubjubPoint, IrType::Native],
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Load(IrType::Native), vec![], vec!["x"]),
            (AssertEqual, vec!["p", "x"], vec![]),
        ],
    );

    // Type compatibility: Byte vectors must have the same length.
    assert_unsupported(
        AssertEqual,
        vec![IrType::Bytes(2), IrType::Bytes(3)],
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (Load(IrType::Bytes(3)), vec![], vec!["w"]),
            (AssertEqual, vec!["v", "w"], vec![]),
        ],
    );

    // Success case: Asserting equality of BigUint values.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x"]),
            (AssertEqual, vec!["x", "x"], vec![]),
        ],
        witness!("x" => biguint_from_hex("deadbeef")),
        vec![],
        None,
    );
}

#[test]
fn test_assert_not_equal() {
    // Arity validation: AssertNotEqual requires exactly 2 inputs and 0 outputs.
    assert_invalid_arity(AssertNotEqual, vec!["x", "y"], vec!["z"]);
    assert_invalid_arity(AssertNotEqual, vec!["x", "y", "z"], vec![]);
    test_static_pass(&[(AssertNotEqual, vec!["x", "y"], vec![])], None);

    // Type support: JubjubScalars do not support inequality assertions.
    assert_unsupported(
        AssertNotEqual,
        vec![IrType::JubjubScalar, IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (AssertNotEqual, vec!["x", "x"], vec![]),
        ],
    );

    // Type compatibility: Both values must have the same type.
    assert_unsupported(
        AssertNotEqual,
        vec![IrType::JubjubPoint, IrType::Native],
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Load(IrType::Native), vec![], vec!["x"]),
            (AssertNotEqual, vec!["p", "x"], vec![]),
        ],
    );

    // Type compatibility: Byte vectors must have the same length.
    assert_unsupported(
        AssertNotEqual,
        vec![IrType::Bytes(2), IrType::Bytes(3)],
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (Load(IrType::Bytes(3)), vec![], vec!["w"]),
            (AssertNotEqual, vec!["v", "w"], vec![]),
        ],
    );

    // Success case: Asserting inequality of Bytes(2).
    test_with_witness(
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v", "w"]),
            (AssertNotEqual, vec!["v", "w"], vec![]),
        ],
        witness!("v" => vec![255, 0], "w" => vec![255, 1]),
        vec![],
        None,
    );

    // Success case: Asserting equality of BigUint values.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x", "y"]),
            (AssertNotEqual, vec!["x", "y"], vec![]),
        ],
        witness!("x" => biguint_from_hex("deadbeef"),   "y" => biguint_from_hex("cafebabe")),
        vec![],
        None,
    );
}

#[test]
fn test_is_equal() {
    // Arity validation: IsEqual requires exactly 2 inputs and 1 output.
    assert_invalid_arity(IsEqual, vec!["x", "y"], vec![]);
    assert_invalid_arity(IsEqual, vec!["x", "y", "z"], vec!["r"]);
    test_static_pass(&[(IsEqual, vec!["x", "y"], vec!["r"])], None);

    // Type support: JubjubScalars do not support equality comparisons.
    assert_unsupported(
        IsEqual,
        vec![IrType::JubjubScalar, IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["s"]),
            (IsEqual, vec!["s", "s"], vec!["b"]),
        ],
    );

    // Type compatibility: Both values must have the same type.
    assert_unsupported(
        IsEqual,
        vec![IrType::Bytes(2), IrType::Bytes(3)],
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (Load(IrType::Bytes(3)), vec![], vec!["w"]),
            (IsEqual, vec!["v", "w"], vec!["b"]),
        ],
    );

    // Success case: Comparing byte vectors and asserting the result is true.
    test_with_witness(
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (IsEqual, vec!["v", "v"], vec!["b"]),
            (AssertEqual, vec!["b", "1"], vec![]),
        ],
        witness!("v" => vec![42u8, 255u8]),
        vec![],
        None,
    );
}

#[test]
fn test_add() {
    // Arity validation: Add requires exactly 2 inputs and 1 output.
    assert_invalid_arity(Add, vec!["x"], vec!["z"]);
    assert_invalid_arity(Add, vec!["x", "y"], vec![]);
    test_static_pass(&[(Add, vec!["x", "y"], vec!["z"])], None);

    // Type support: JubjubScalars do not support addition.
    assert_unsupported(
        Add,
        vec![IrType::JubjubScalar, IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Add, vec!["x", "x"], vec!["z"]),
        ],
    );

    // Success case: Adding large BigUint values.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x"]),
            (Add, vec!["x", "x"], vec!["z"]),
        ],
        witness!("x" => biguint_from_hex("fffffffffffffffffffffffffffffffffffffffffffffffff")),
        vec![],
        None,
    );
}

#[test]
fn test_sub() {
    // Arity validation: Sub requires exactly 2 inputs and 1 output.
    assert_invalid_arity(Sub, vec!["x"], vec!["z"]);
    assert_invalid_arity(Sub, vec!["x", "y"], vec![]);
    test_static_pass(&[(Sub, vec!["x", "y"], vec!["z"])], None);

    // Type support: JubjubScalars do not support subtraction.
    assert_unsupported(
        Sub,
        vec![IrType::JubjubScalar, IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Sub, vec!["x", "x"], vec!["z"]),
        ],
    );

    // Success case: Subtracting BigUint values (x - x = 0).
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x"]),
            (Sub, vec!["x", "x"], vec!["z"]),
        ],
        witness!("x" => biguint_from_hex("deadbeef")),
        vec![],
        None,
    );
}

#[test]
fn test_mul() {
    // Arity validation: Mul requires exactly 2 inputs and 1 output.
    assert_invalid_arity(Mul, vec!["x"], vec!["z"]);
    assert_invalid_arity(Mul, vec!["x", "y"], vec![]);
    test_static_pass(&[(Mul, vec!["x", "y"], vec!["z"])], None);

    // Type support: JubjubScalar-JubjubScalar multiplication is not supported.
    assert_unsupported(
        Mul,
        vec![IrType::JubjubScalar, IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Mul, vec!["x", "x"], vec!["z"]),
        ],
    );

    // Success case: Scalar multiplication of a Jubjub point.
    let (p, s) = (JubjubSubgroup::random(OsRng), JubjubFr::random(OsRng));
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Load(IrType::JubjubScalar), vec![], vec!["s"]),
            (Mul, vec!["s", "p"], vec!["q"]),
        ],
        witness!("p" => p, "s" => s),
        vec![],
        None,
    );
}

#[test]
fn test_neg() {
    // Arity validation: Neg requires exactly 1 input and 1 output.
    assert_invalid_arity(Neg, vec![], vec!["z"]);
    assert_invalid_arity(Neg, vec!["x"], vec![]);
    test_static_pass(&[(Neg, vec!["x"], vec!["z"])], None);

    // Type support: Negation is not supported for JubjubScalars.
    assert_unsupported(
        Neg,
        vec![IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Neg, vec!["x"], vec!["z"]),
        ],
    );

    // Success case: Negating a JubjubPoint and publishing the result.
    let p: IrValue = JubjubSubgroup::random(OsRng).into();
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Neg, vec!["p"], vec!["q"]),
            (Publish, vec!["q"], vec![]),
        ],
        witness!("p" => p.clone()),
        vec![(-p, IrType::JubjubPoint)],
        None,
    );
}

#[test]
fn test_mod_exp() {
    // Arity validation: ModExp(n) requires exactly 2 input and 1 output.
    assert_invalid_arity(ModExp(65537), vec![], vec!["out"]);
    assert_invalid_arity(ModExp(65537), vec!["x"], vec!["out"]);
    test_static_pass(&[(ModExp(65537), vec!["x", "m"], vec!["out"])], None);

    // Type support: ModExp(n) is not supported for Natives.
    assert_unsupported(
        ModExp(123),
        vec![IrType::Native, IrType::Native],
        &[
            (Load(IrType::Native), vec![], vec!["x", "m"]),
            (ModExp(123), vec!["x", "m"], vec!["z"]),
        ],
    );

    // Success case. Modular exponentiation of BigUint values.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x", "m"]),
            (ModExp(65537), vec!["x", "m"], vec!["out"]),
            (Publish, vec!["out"], vec![]),
        ],
        witness!("x" => biguint_from_hex("deadbeef") , "m" => biguint_from_hex("7a0b1e3ae205a1c7")),
        vec![(
            biguint_from_hex("1423d96999521749").into(),
            IrType::BigUint(1024),
        )],
        None,
    );
}

#[test]
fn test_inner_product() {
    // Arity validation: InnerProduct requires an even, positive number of inputs
    // and 1 output.
    assert_invalid_arity(InnerProduct, vec!["x"], vec!["z"]);
    assert_invalid_arity(InnerProduct, vec!["x", "y"], vec![]);
    test_static_pass(&[(InnerProduct, vec!["x", "y"], vec!["z"])], None);

    // Type compatibility: All inputs must be compatible for inner product
    // computation.
    assert_unsupported(
        InnerProduct,
        vec![IrType::Native, IrType::BigUint(10)],
        &[
            (Load(IrType::Native), vec![], vec!["x"]),
            (Load(IrType::BigUint(10)), vec![], vec!["n"]),
            (InnerProduct, vec!["x", "n"], vec!["z"]),
        ],
    );

    // Type mismatch: Scalars and points must be properly paired.
    test_without_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["s", "p", "q"]),
            (Load(IrType::JubjubScalar), vec![], vec!["r"]),
            (InnerProduct, vec!["r", "s", "p", "q"], vec!["result"]),
        ],
        Some(Error::Other(
            "cannot convert JubjubPoint to \"JubjubScalar\"".to_string(),
        )),
    );

    // Success case: Computing scalar-point inner product (MSM).
    let [p, q] = core::array::from_fn(|_| JubjubSubgroup::random(OsRng));
    let [r, s] = core::array::from_fn(|_| JubjubFr::random(OsRng));
    let result = p * r + q * s;
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p", "q"]),
            (Load(IrType::JubjubScalar), vec![], vec!["r", "s"]),
            (InnerProduct, vec!["r", "s", "p", "q"], vec!["result"]),
            (Publish, vec!["result"], vec![]),
        ],
        witness!("p" => p, "q" => q, "r" => r, "s" => s),
        vec![(result.into(), IrType::JubjubPoint)],
        None,
    );
}

#[test]
fn test_affine_coordinates() {
    // Arity validation: AffineCoordinates requires 1 input and 2 outputs (x, y).
    assert_invalid_arity(AffineCoordinates, vec!["P"], vec!["Px"]);
    assert_invalid_arity(AffineCoordinates, vec!["P", "Q"], vec!["Px", "Py"]);
    test_static_pass(&[(AffineCoordinates, vec!["P"], vec!["Px", "Py"])], None);

    // Type support: Only elliptic curve points support coordinate extraction.
    assert_unsupported(
        AffineCoordinates,
        vec![IrType::Native],
        &[
            (Load(IrType::Native), vec![], vec!["P"]),
            (AffineCoordinates, vec!["P"], vec!["x", "y"]),
        ],
    );

    // Success case: Extracting coordinates and verifying the Edwards curve
    // equation. Edwards curve equation: y^2 - x^2 = 1 + d*x^2*y^2
    const EDWARDS_D: &str =
        "Native:0x2a9318e74bfa2b48f5fd9207e6bd7fd4292d7f6d37579d2601065fd6d6343eb1";
    let p = JubjubSubgroup::random(OsRng);
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (AffineCoordinates, vec!["p"], vec!["x", "y"]),
            (Mul, vec!["x", "x"], vec!["x2"]),
            (Mul, vec!["y", "y"], vec!["y2"]),
            (Sub, vec!["y2", "x2"], vec!["lhs"]),
            (Mul, vec!["x2", "y2"], vec!["x2y2"]),
            (Mul, vec![EDWARDS_D, "x2y2"], vec!["prod"]),
            (Add, vec!["prod", "Native:0x01"], vec!["rhs"]),
            (AssertEqual, vec!["lhs", "rhs"], vec![]),
        ],
        witness!("p" => p),
        vec![],
        None,
    );
}

#[test]
fn test_into_bytes() {
    // Arity validation: IntoBytes requires exactly 1 input and 1 output.
    assert_invalid_arity(IntoBytes(32), vec!["x"], vec!["bytes", "foo"]);
    assert_invalid_arity(IntoBytes(32), vec!["x", "y"], vec!["bytes"]);
    test_static_pass(&[(IntoBytes(32), vec!["x"], vec!["bytes"])], None);

    // Type support: Booleans cannot be converted to bytes.
    assert_unsupported(
        IntoBytes(1),
        vec![IrType::Bool],
        &[
            (Load(IrType::Bool), vec![], vec!["b"]),
            (IntoBytes(1), vec!["b"], vec!["w"]),
        ],
    );

    // Type support: Byte vectors cannot be converted to bytes (already bytes).
    assert_unsupported(
        IntoBytes(10),
        vec![IrType::Bytes(10)],
        &[
            (Load(IrType::Bytes(10)), vec![], vec!["v"]),
            (IntoBytes(10), vec!["v"], vec!["w"]),
        ],
    );

    // Length validation: JubjubPoint requires exactly 32 bytes, not 31.
    assert_unsupported(
        IntoBytes(31),
        vec![IrType::JubjubPoint],
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (IntoBytes(31), vec!["p"], vec!["bytes"]),
        ],
    );

    // Type support: JubjubScalar cannot be converted to bytes.
    assert_unsupported(
        IntoBytes(32),
        vec![IrType::JubjubScalar],
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["s"]),
            (IntoBytes(32), vec!["s"], vec!["bytes"]),
        ],
    );

    // Success case: Converting a small BigUint to a single byte.
    test_with_witness(
        &[
            (Load(IrType::BigUint(16)), vec![], vec!["n"]),
            (IntoBytes(1), vec!["n"], vec!["n_bytes"]),
        ],
        witness!("n" => BigUint::from(255u64)),
        vec![],
        None,
    );
}

#[test]
fn test_from_bytes() {
    // Arity validation: FromBytes requires exactly 1 input and 1 output.
    assert_invalid_arity(FromBytes(IrType::Native), vec!["bytes"], vec!["x", "y"]);
    assert_invalid_arity(FromBytes(IrType::Bool), vec!["bytes"], vec![]);
    test_static_pass(
        &[(FromBytes(IrType::BigUint(1024)), vec!["bytes"], vec!["N"])],
        None,
    );

    // Type support: Bytes cannot be parsed as Booleans.
    assert_unsupported(
        FromBytes(IrType::Bool),
        vec![IrType::Bytes(1)],
        &[
            (Load(IrType::Bytes(1)), vec![], vec!["bytes"]),
            (FromBytes(IrType::Bool), vec!["bytes"], vec!["b"]),
        ],
    );

    // Length validation: JubjubPoint requires exactly 32 bytes, not 33.
    assert_unsupported(
        FromBytes(IrType::JubjubPoint),
        vec![IrType::Bytes(33)],
        &[
            (Load(IrType::Bytes(33)), vec![], vec!["bytes"]),
            (FromBytes(IrType::JubjubPoint), vec!["bytes"], vec!["p"]),
        ],
    );

    // Success case: Parsing 4 bytes as a BigUint.
    test_with_witness(
        &[
            (Load(IrType::Bytes(4)), vec![], vec!["bytes"]),
            (FromBytes(IrType::BigUint(32)), vec!["bytes"], vec!["N"]),
        ],
        witness!("bytes" => vec![0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8]),
        vec![],
        None,
    );
}

#[test]
fn test_bytes_conversion_round_trip() {
    // Test round-trip conversions: value -> bytes -> value and bytes -> value ->
    // bytes This ensures IntoBytes and FromBytes are consistent inverses.
    [
        (IrType::Native, F::random(OsRng).into(), 32),
        (IrType::BigUint(64), biguint_from_hex("abcd1357").into(), 8),
        (
            IrType::JubjubPoint,
            JubjubSubgroup::random(OsRng).into(),
            32,
        ),
    ]
    .into_iter()
    .for_each(|(t, x, n): (IrType, IrValue, usize)| {
        // Forward: value -> bytes -> value (should recover original value)
        test_with_witness(
            &[
                (Load(t), vec![], vec!["x"]),
                (IntoBytes(n), vec!["x"], vec!["bytes"]),
                (FromBytes(t), vec!["bytes"], vec!["x'"]),
                (AssertEqual, vec!["x", "x'"], vec![]),
            ],
            HashMap::from_iter([("x", x.clone())]),
            vec![],
            None,
        );

        // Backward: bytes -> value -> bytes (should recover original bytes)
        test_with_witness(
            &[
                (Load(IrType::Bytes(n)), vec![], vec!["bytes"]),
                (FromBytes(t), vec!["bytes"], vec!["x"]),
                (IntoBytes(n), vec!["x"], vec!["bytes'"]),
                (AssertEqual, vec!["bytes", "bytes'"], vec![]),
            ],
            HashMap::from_iter([("bytes", IrValue::into_bytes(x, n).unwrap())]),
            vec![],
            None,
        )
    });
}

#[test]
fn test_poseidon() {
    // Arity validation: Poseidon requires some inputs and 1 output.
    assert_invalid_arity(Poseidon, vec!["x"], vec!["h1", "h2"]);
    assert_invalid_arity(Poseidon, vec![], vec!["h"]);
    test_static_pass(&[(Poseidon, vec!["x", "y"], vec!["h"])], None);

    // Type support: Poseidon expects Natives.
    test_without_witness(
        &[
            (Load(IrType::Bytes(10)), vec![], vec!["bytes"]),
            (Poseidon, vec!["bytes"], vec!["h"]),
        ],
        Some(Error::Other(
            "cannot convert Bytes(10) to \"Native\"".into(),
        )),
    );

    // Success case: hashing 3 inputs.
    test_with_witness(
        &[
            (Load(IrType::Native), vec![], vec!["x", "y", "z"]),
            (Poseidon, vec!["x", "y", "z"], vec!["h"]),
        ],
        witness!("x" => F::random(OsRng), "y" => F::random(OsRng), "z" => F::random(OsRng)),
        vec![],
        None,
    );
}

#[test]
fn test_sha256() {
    // Arity validation: SHA-256 requires 1 input and 1 output.
    assert_invalid_arity(Sha256, vec!["x"], vec!["h1", "h2"]);
    assert_invalid_arity(Sha256, vec![], vec!["h"]);
    test_static_pass(&[(Sha256, vec!["x"], vec!["h"])], None);

    // Type support: SHA-256 expects Bytes.
    test_without_witness(
        &[
            (Load(IrType::Bytes(10)), vec![], vec!["bytes"]),
            (Sha256, vec!["bytes"], vec!["h"]),
        ],
        None,
    );
    test_without_witness(
        &[
            (Load(IrType::Bool), vec![], vec!["b"]),
            (Sha256, vec!["b"], vec!["h"]),
        ],
        Some(Error::Other("cannot convert Bool to \"Bytes\"".into())),
    );

    // Success case: hashing 1024 bytes.
    test_with_witness(
        &[
            (Load(IrType::Bytes(1024)), vec![], vec!["preimage"]),
            (Sha256, vec!["preimage"], vec!["h"]),
        ],
        witness!("preimage" => vec![0u8; 1024]),
        vec![],
        None,
    );
}

#[test]
fn test_sha512() {
    // Arity validation: SHA-512 requires 1 input and 1 output.
    assert_invalid_arity(Sha512, vec!["x"], vec!["h1", "h2"]);
    assert_invalid_arity(Sha512, vec![], vec!["h"]);
    test_static_pass(&[(Sha512, vec!["x"], vec!["h"])], None);

    // Type support: SHA-512 expects Bytes.
    test_without_witness(
        &[
            (Load(IrType::Bytes(10)), vec![], vec!["bytes"]),
            (Sha512, vec!["bytes"], vec!["h"]),
        ],
        None,
    );
    test_without_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["b"]),
            (Sha512, vec!["b"], vec!["h"]),
        ],
        Some(Error::Other(
            "cannot convert JubjubPoint to \"Bytes\"".into(),
        )),
    );

    // Success case: hashing 1024 bytes.
    test_with_witness(
        &[
            (Load(IrType::Bytes(1024)), vec![], vec!["preimage"]),
            (Sha512, vec!["preimage"], vec!["h"]),
        ],
        witness!("preimage" => vec![255u8; 1024]),
        vec![],
        None,
    );
}

/// Converts raw instruction tuples into structured `Instruction` objects.
fn build_instructions(
    raw_instructions: &[(Operation, Vec<&'static str>, Vec<&'static str>)],
) -> Vec<Instruction> {
    raw_instructions
        .iter()
        .map(|(op, inputs, outputs)| Instruction {
            operation: *op,
            inputs: inputs.iter().map(|s| s.to_string()).collect(),
            outputs: outputs.iter().map(|s| s.to_string()).collect(),
        })
        .collect()
}

/// Tests static validation of ZKIR programs without witness values.
///
/// This function validates compile-time properties such as:
/// - Operation arity (correct number of inputs/outputs)
/// - Type system constraints
/// - Instruction format correctness
///
/// Use this when testing properties that can be validated before witness
/// assignment.
fn test_static_pass(
    raw_instructions: &[(Operation, Vec<&'static str>, Vec<&'static str>)],
    expected_error: Option<Error>,
) {
    let instructions = build_instructions(raw_instructions);
    assert_eq!(
        ZkirRelation::from_instructions(&instructions).map(|_| ()),
        expected_error.map(Err).unwrap_or(Ok(()))
    );
}

/// Tests circuit structure without concrete witness values.
///
/// This function validates the circuit synthesis with unknown witness values,
/// checking:
/// - Variable name uniqueness and scoping
/// - Type compatibility between operations
/// - Circuit structure consistency
///
/// Use this when testing properties that depend on the circuit structure but
/// not on specific witness values.
fn test_without_witness(
    raw_instructions: &[(Operation, Vec<&'static str>, Vec<&'static str>)],
    expected_error: Option<Error>,
) {
    let instructions = build_instructions(raw_instructions);
    let relation = ZkirRelation::from_instructions(&instructions).unwrap();
    let circuit = MidnightCircuit::new(&relation, Value::unknown(), Value::unknown(), Some(8));
    assert_eq!(
        dummy_synthesize_run(&circuit).map_err(|e| e.to_string()).map(|_| ()),
        expected_error
            .map(|e| Err(Into::<plonk::Error>::into(e).to_string()))
            .unwrap_or(Ok(()))
    );
}

/// Tests full end-to-end proof generation and verification with concrete
/// witness values.
///
/// This function performs a complete proof lifecycle:
/// 1. Off-circuit computation to derive public inputs
/// 2. Circuit synthesis with concrete witness values
/// 3. Proof generation using KZG commitment scheme
///
/// Use this for comprehensive testing that validates both off-circuit and
/// in-circuit behavior, including constraint satisfaction and proof soundness.
///
/// # Parameters
/// - `raw_instructions`: The ZKIR program to test
/// - `witness`: Private input values for the circuit
/// - `expected_public_inputs`: Expected public outputs with their types
/// - `expected_error`: Expected error, or `None` if the test should succeed
fn test_with_witness(
    raw_instructions: &[(Operation, Vec<&'static str>, Vec<&'static str>)],
    witness: HashMap<&'static str, IrValue>,
    expected_public_inputs: Vec<(IrValue, IrType)>,
    expected_error: Option<Error>,
) {
    let instructions = build_instructions(raw_instructions);
    let relation = ZkirRelation::from_instructions(&instructions).unwrap();

    let k = MidnightCircuit::from_relation(&relation).min_k();
    let srs = ParamsKZG::unsafe_setup(k, OsRng);

    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let pi_result = relation.public_inputs(witness.clone());

    // Assert that the off-circuit pass produces the expected result.
    assert_eq!(
        pi_result.clone().map(|_| ()),
        expected_error.clone().map(Err).unwrap_or(Ok(()))
    );

    if let Ok(pi) = pi_result {
        assert_eq!(pi, expected_public_inputs);
    }

    let proof_result = compact_std_lib::prove::<_, Blake2b>(
        &srs,
        &pk,
        &relation,
        &expected_public_inputs,
        witness,
        OsRng,
    );

    // Assert that the in-circuit pass produces the expected result.
    assert_eq!(
        proof_result.map_err(|e| e.to_string()).map(|_| ()),
        expected_error
            .map(|e| Err(Into::<plonk::Error>::into(e).to_string()))
            .unwrap_or(Ok(()))
    )
}

/// Helper to create a BigUint from a hex string
fn biguint_from_hex(hex_str: &str) -> BigUint {
    BigUint::from_str_radix(hex_str, 16).unwrap()
}

/// Helper to test that an operation requires a specific arity
fn assert_invalid_arity(op: Operation, inputs: Vec<&'static str>, outputs: Vec<&'static str>) {
    test_static_pass(&[(op, inputs, outputs)], Some(Error::InvalidArity(op)));
}

/// Helper to test that an operation is unsupported for given types
fn assert_unsupported(
    op: Operation,
    input_types: Vec<IrType>,
    setup: &[(Operation, Vec<&'static str>, Vec<&'static str>)],
) {
    test_without_witness(setup, Some(Error::Unsupported(op, input_types)));
}

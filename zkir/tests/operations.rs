use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use group::Group;
use midnight_circuits::{
    compact_std_lib::{self, MidnightCircuit},
    halo2curves::ff::Field,
};
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

#[test]
fn test_load() {
    // A load instruction with no outputs should return an Error::InvalidArity.
    test_static_pass(
        &[(Load(IrType::Bool), vec![], vec![])],
        Some(Error::InvalidArity(Load(IrType::Bool))),
    );

    // With at least one output, everything should be fine.
    test_static_pass(&[(Load(IrType::Bool), vec![], vec!["out"])], None);
    test_static_pass(&[(Load(IrType::Bool), vec![], vec!["out1", "out2"])], None);

    // But it should take no inputs.
    test_static_pass(
        &[(Load(IrType::Bool), vec!["inp"], vec!["out"])],
        Some(Error::InvalidArity(Load(IrType::Bool))),
    );

    // Names should be unique, loading "out" twice will result in an
    // Error::DuplicatedName.
    test_without_witness(
        &[(Load(IrType::Bool), vec![], vec!["out", "out"])],
        Some(Error::DuplicatedName("out".to_string())),
    );

    // Using the same name even if in two different instructions should fail.
    test_without_witness(
        &[
            (Load(IrType::Bool), vec![], vec!["out"]),
            (Load(IrType::Bool), vec![], vec!["out"]),
        ],
        Some(Error::DuplicatedName("out".to_string())),
    );

    // If the value for the loaded variable is not provided in the witness, we
    // should get a NotFound error.
    test_with_witness(
        &[(Load(IrType::Bool), vec![], vec!["out"])],
        HashMap::from_iter([("outt", true.into())]),
        vec![],
        Some(Error::NotFound("out".to_string())),
    );

    // If "out" is in the witness, but with an incorrect type, we should get an
    // Error::ExpectingType.
    test_with_witness(
        &[(Load(IrType::Bool), vec![], vec!["out"])],
        HashMap::from_iter([("out", F::ONE.into())]),
        vec![],
        Some(Error::ExpectingType(IrType::Bool, IrType::Native)),
    );

    // If "out" is provided in the witness and it has the correct type, we are good.
    test_with_witness(
        &[(Load(IrType::Bool), vec![], vec!["out"])],
        HashMap::from_iter([("out", true.into())]),
        vec![],
        None,
    );
}

#[test]
fn test_publish() {
    // A publish instruction with no inputs should return an Error::InvalidArity.
    test_static_pass(
        &[(Publish, vec![], vec![])],
        Some(Error::InvalidArity(Publish)),
    );

    // A publish instruction with outputs should return an Error::InvalidArity.
    test_static_pass(
        &[(Publish, vec!["inp"], vec!["out"])],
        Some(Error::InvalidArity(Publish)),
    );

    // With at least one input and not outputs, everything should be fine.
    test_static_pass(&[(Publish, vec!["inp"], vec![])], None);
    test_static_pass(&[(Publish, vec!["inp1", "inp2"], vec![])], None);

    // Published inputs must exist.
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

    // A successful execution.
    test_with_witness(
        &[
            (Load(IrType::Native), vec![], vec!["x"]),
            (Publish, vec!["x"], vec![]),
        ],
        HashMap::from_iter([("x", (-F::ONE).into())]),
        vec![((-F::ONE).into(), IrType::Native)],
        None,
    );

    // We can also publish the same value several times.
    test_with_witness(
        &[
            (Load(IrType::Bool), vec![], vec!["a", "b"]),
            (Publish, vec!["b", "b", "a"], vec![]),
            (Publish, vec!["b"], vec![]),
        ],
        HashMap::from_iter([("a", false.into()), ("b", true.into())]),
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
    // Equality assertions expect 2 inputs and no outputs.
    test_static_pass(
        &[(AssertEqual, vec!["x", "y"], vec!["z"])],
        Some(Error::InvalidArity(AssertEqual)),
    );

    test_static_pass(
        &[(AssertEqual, vec!["x", "y", "z"], vec![])],
        Some(Error::InvalidArity(AssertEqual)),
    );

    test_static_pass(&[(AssertEqual, vec!["x", "y"], vec![])], None);

    // Unsupported equality assertion on JubjubScalars.
    test_without_witness(
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (AssertEqual, vec!["x", "x"], vec![]),
        ],
        Some(Error::Unsupported(
            AssertEqual,
            vec![IrType::JubjubScalar, IrType::JubjubScalar],
        )),
    );

    // Compared values must be of the same type.
    test_without_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Load(IrType::Native), vec![], vec!["x"]),
            (AssertEqual, vec!["p", "x"], vec![]),
        ],
        Some(Error::Unsupported(
            AssertEqual,
            vec![IrType::JubjubPoint, IrType::Native],
        )),
    );

    test_without_witness(
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (Load(IrType::Bytes(3)), vec![], vec!["w"]),
            (AssertEqual, vec!["v", "w"], vec![]),
        ],
        Some(Error::Unsupported(
            AssertEqual,
            vec![IrType::Bytes(2), IrType::Bytes(3)],
        )),
    );

    // A successful execution.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x"]),
            (AssertEqual, vec!["x", "x"], vec![]),
        ],
        HashMap::from_iter([("x", biguint_from_hex("deadbeef").into())]),
        vec![],
        None,
    );
}

#[test]
fn test_is_equal() {
    // Equality comparisons expect 2 inputs and 1 output.
    test_static_pass(
        &[(IsEqual, vec!["x", "y"], vec![])],
        Some(Error::InvalidArity(IsEqual)),
    );

    test_static_pass(
        &[(IsEqual, vec!["x", "y", "z"], vec!["r"])],
        Some(Error::InvalidArity(IsEqual)),
    );

    test_static_pass(&[(IsEqual, vec!["x", "y"], vec!["r"])], None);

    // Unsupported equality comparison on JubjubScalars.
    test_without_witness(
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["s"]),
            (IsEqual, vec!["s", "s"], vec!["b"]),
        ],
        Some(Error::Unsupported(
            IsEqual,
            vec![IrType::JubjubScalar, IrType::JubjubScalar],
        )),
    );

    // Compared values must be of the same type.
    test_without_witness(
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (Load(IrType::Bytes(3)), vec![], vec!["w"]),
            (IsEqual, vec!["v", "w"], vec!["b"]),
        ],
        Some(Error::Unsupported(
            IsEqual,
            vec![IrType::Bytes(2), IrType::Bytes(3)],
        )),
    );

    // A successful execution.
    test_with_witness(
        &[
            (Load(IrType::Bytes(2)), vec![], vec!["v"]),
            (IsEqual, vec!["v", "v"], vec!["b"]),
            (AssertEqual, vec!["b", "1"], vec![]),
        ],
        HashMap::from_iter([("v", vec![42u8, 255u8].into())]),
        vec![],
        None,
    );
}

#[test]
fn test_add() {
    // An add instruction should have 2 inputs and 1 output.
    test_static_pass(
        &[(Add, vec!["x"], vec!["z"])],
        Some(Error::InvalidArity(Add)),
    );

    test_static_pass(
        &[(Add, vec!["x", "y"], vec![])],
        Some(Error::InvalidArity(Add)),
    );

    test_static_pass(&[(Add, vec!["x", "y"], vec!["z"])], None);

    // Unsupported addition on JubjubScalars.
    test_without_witness(
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Add, vec!["x", "x"], vec!["z"]),
        ],
        Some(Error::Unsupported(
            Add,
            vec![IrType::JubjubScalar, IrType::JubjubScalar],
        )),
    );

    // A successful execution.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x"]),
            (Add, vec!["x", "x"], vec!["z"]),
        ],
        HashMap::from_iter([(
            "x",
            biguint_from_hex("fffffffffffffffffffffffffffffffffffffffffffffffff").into(),
        )]),
        vec![],
        None,
    );
}

#[test]
fn test_sub() {
    // A sub instruction should have 2 inputs and 1 output.
    test_static_pass(
        &[(Sub, vec!["x"], vec!["z"])],
        Some(Error::InvalidArity(Sub)),
    );

    test_static_pass(
        &[(Sub, vec!["x", "y"], vec![])],
        Some(Error::InvalidArity(Sub)),
    );

    test_static_pass(&[(Sub, vec!["x", "y"], vec!["z"])], None);

    // Unsupported subtraction on JubjubScalars.
    test_without_witness(
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Sub, vec!["x", "x"], vec!["z"]),
        ],
        Some(Error::Unsupported(
            Sub,
            vec![IrType::JubjubScalar, IrType::JubjubScalar],
        )),
    );

    // A successful execution.
    test_with_witness(
        &[
            (Load(IrType::BigUint(1024)), vec![], vec!["x"]),
            (Sub, vec!["x", "x"], vec!["z"]),
        ],
        HashMap::from_iter([("x", biguint_from_hex("deadbeef").into())]),
        vec![],
        None,
    );
}

#[test]
fn test_mul() {
    // A mul instruction should have 2 inputs and 1 output.
    test_static_pass(
        &[(Mul, vec!["x"], vec!["z"])],
        Some(Error::InvalidArity(Mul)),
    );

    test_static_pass(
        &[(Mul, vec!["x", "y"], vec![])],
        Some(Error::InvalidArity(Mul)),
    );

    test_static_pass(&[(Mul, vec!["x", "y"], vec!["z"])], None);

    // Unsupported multiplication on JubjubScalars.
    test_without_witness(
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Mul, vec!["x", "x"], vec!["z"]),
        ],
        Some(Error::Unsupported(
            Mul,
            vec![IrType::JubjubScalar, IrType::JubjubScalar],
        )),
    );

    // A successful execution.
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Load(IrType::JubjubScalar), vec![], vec!["s"]),
            (Mul, vec!["s", "p"], vec!["q"]),
        ],
        HashMap::from_iter([
            ("p", JubjubSubgroup::random(OsRng).into()),
            ("s", JubjubFr::random(OsRng).into()),
        ]),
        vec![],
        None,
    );
}

#[test]
fn test_neg() {
    // A neg instruction should have 1 inputs and 1 output.
    test_static_pass(&[(Neg, vec![], vec!["z"])], Some(Error::InvalidArity(Neg)));
    test_static_pass(&[(Neg, vec!["x"], vec![])], Some(Error::InvalidArity(Neg)));
    test_static_pass(&[(Neg, vec!["x"], vec!["z"])], None);

    // Unsupported negation on JubjubScalars.
    test_without_witness(
        &[
            (Load(IrType::JubjubScalar), vec![], vec!["x"]),
            (Neg, vec!["x"], vec!["z"]),
        ],
        Some(Error::Unsupported(Neg, vec![IrType::JubjubScalar])),
    );

    // A successful execution.
    let p: IrValue = JubjubSubgroup::random(OsRng).into();
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p"]),
            (Neg, vec!["p"], vec!["q"]),
            (Publish, vec!["q"], vec![]),
        ],
        HashMap::from_iter([("p", p.clone())]),
        vec![(-p, IrType::JubjubPoint)],
        None,
    );
}

#[test]
fn test_inner_product() {
    // An inner_product should take an even number of inputs > 0 and 1 output.
    test_static_pass(
        &[(InnerProduct, vec!["x"], vec!["z"])],
        Some(Error::InvalidArity(InnerProduct)),
    );

    test_static_pass(
        &[(InnerProduct, vec!["x", "y"], vec![])],
        Some(Error::InvalidArity(InnerProduct)),
    );

    test_static_pass(&[(InnerProduct, vec!["x", "y"], vec!["z"])], None);

    // Unsupported IP on mixed types.
    test_without_witness(
        &[
            (Load(IrType::Native), vec![], vec!["x"]),
            (Load(IrType::BigUint(10)), vec![], vec!["n"]),
            (InnerProduct, vec!["x", "n"], vec!["z"]),
        ],
        Some(Error::Unsupported(
            InnerProduct,
            vec![IrType::Native, IrType::BigUint(10)],
        )),
    );

    // Incompatible types.
    test_without_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["s", "p", "q"]),
            (Load(IrType::JubjubScalar), vec![], vec!["r"]),
            (InnerProduct, vec!["r", "s", "p", "q"], vec!["result"]),
        ],
        Some(Error::Other(format!(
            "cannot convert JubjubPoint to \"JubjubScalar\"",
        ))),
    );

    // A successful execution.
    let [p, q] = core::array::from_fn(|_| JubjubSubgroup::random(OsRng));
    let [r, s] = core::array::from_fn(|_| JubjubFr::random(OsRng));
    test_with_witness(
        &[
            (Load(IrType::JubjubPoint), vec![], vec!["p", "q"]),
            (Load(IrType::JubjubScalar), vec![], vec!["r", "s"]),
            (InnerProduct, vec!["r", "s", "p", "q"], vec!["result"]),
            (Publish, vec!["result"], vec![]),
        ],
        HashMap::from_iter([
            ("p", p.into()),
            ("q", q.into()),
            ("r", r.into()),
            ("s", s.into()),
        ]),
        vec![((p * r + q * s).into(), IrType::JubjubPoint)],
        None,
    );
}

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

/// Util function for testing static conditions of a ZKIR program (e.g. arity
/// mismatches) without actually "executing" the program.
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

/// Util function for testing the execution of a ZKIR program with a certain
/// witness and no public inputs.
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

/// Util function for testing the execution of a ZKIR program with a certain
/// witness. We provide the expected vector of public inputs, and assert
/// that it coincides with the derived public inputs from the off-circuit
/// execution (when `expected_error = None`).
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

fn biguint_from_hex(hex_str: &str) -> BigUint {
    BigUint::from_str_radix(hex_str, 16).unwrap()
}

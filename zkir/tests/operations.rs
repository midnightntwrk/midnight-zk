use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use midnight_circuits::{
    compact_std_lib::{self, MidnightCircuit},
    halo2curves::ff::Field,
};
use midnight_proofs::{
    circuit::Value, dev::cost_model::dummy_synthesize_run, plonk, poly::kzg::params::ParamsKZG,
};
use midnight_zkir::{
    Error, Instruction, IrType, IrValue,
    Operation::{self, *},
    ZkirRelation,
};
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
        Some(Error::NotFound("x".to_string())),
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

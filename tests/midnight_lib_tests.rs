use blstrs::{ExtendedPoint as Jubjub, Scalar as JubjubBase};
use ff::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    dev::MockProver,
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib::{MidnightCircuit, Relation, ZkStdLib},
    ecc::curves::CircuitCurve,
    instructions::*,
    types::Bit,
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

#[test]
fn arith_ops() {
    #[derive(Clone, Default)]
    struct Logic;

    impl Relation for Logic {
        type Witness = ();

        type Instance = ();

        const K: u32 = 10;

        fn from_statement(_instance: &Self::Instance, _witness: &Self::Witness) -> Self {
            Logic
        }

        fn format_instance(_instance: &Self::Instance) -> Vec<JubjubBase> {
            vec![]
        }

        fn circuit(
            &self,
            std_lib: &ZkStdLib,
            layouter: &mut impl Layouter<<Jubjub as CircuitCurve>::Base>,
        ) -> Result<(), Error> {
            let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
            let inputs: [JubjubBase; 4] = [
                JubjubBase::random(&mut rng),
                JubjubBase::random(&mut rng),
                JubjubBase::random(&mut rng),
                JubjubBase::random(&mut rng),
            ];

            let expected_sub = inputs[0] - inputs[1];
            let expected_neg = -inputs[0];
            let expected_add = inputs.iter().sum::<JubjubBase>();

            let inputs = std_lib.assign_many(
                layouter,
                &inputs.into_iter().map(Value::known).collect::<Vec<_>>(),
            )?;

            let res_sub = std_lib.sub(layouter, &inputs[0], &inputs[1])?;
            let res_neg = std_lib.neg(layouter, &inputs[0])?;
            let res_add = std_lib.linear_combination(
                layouter,
                &inputs
                    .into_iter()
                    .map(|x| (JubjubBase::ONE, x))
                    .collect::<Vec<_>>(),
                JubjubBase::ZERO,
            )?;

            std_lib.assert_equal_to_fixed(layouter, &res_sub, expected_sub)?;
            std_lib.assert_equal_to_fixed(layouter, &res_neg, expected_neg)?;
            std_lib.assert_equal_to_fixed(layouter, &res_add, expected_add)?;

            Ok(())
        }
    }

    let circuit: MidnightCircuit<_> = Logic.into();
    let prover = MockProver::run(17, &circuit, vec![vec![]]).expect("Failed to generate proof");
    prover.assert_satisfied();
}

#[test]
fn less_than() {
    #[derive(Clone, Default)]
    struct LessThan;

    impl Relation for LessThan {
        type Witness = ();

        type Instance = ();

        const K: u32 = 10;

        fn from_statement(_instance: &Self::Instance, _witness: &Self::Witness) -> Self {
            LessThan
        }

        fn format_instance(_instance: &Self::Instance) -> Vec<JubjubBase> {
            vec![]
        }

        fn circuit(
            &self,
            std_lib: &ZkStdLib,
            layouter: &mut impl Layouter<<Jubjub as CircuitCurve>::Base>,
        ) -> Result<(), Error> {
            let limit_range = JubjubBase::from(2 << 11);
            let lt = JubjubBase::from((2 << 1) - 1);
            let gt = JubjubBase::from((2 << 11) + 1); // larger than limit

            let limit = std_lib.assign(layouter, Value::known(limit_range))?;
            let lt = std_lib.assign(layouter, Value::known(lt))?;
            let gt = std_lib.assign(layouter, Value::known(gt))?;
            let equal = std_lib.assign(layouter, Value::known(limit_range))?;

            let lt_true = std_lib.lower_than(layouter, &lt, &limit, 127)?;
            let lt_false = std_lib.lower_than(layouter, &gt, &limit, 127)?;
            let equal = std_lib.lower_than(layouter, &equal, &limit, 127)?;

            std_lib.assert_true(layouter, &lt_true)?;
            std_lib.assert_false(layouter, &lt_false)?;
            std_lib.assert_false(layouter, &equal)?;

            Ok(())
        }
    }

    let circuit: MidnightCircuit<_> = LessThan.into();

    let prover = MockProver::run(17, &circuit, vec![vec![]]).expect(
        "Failed
to generate proof",
    );
    prover.assert_satisfied();
}

#[test]
fn conditional_select() {
    #[derive(Clone, Default)]
    struct CondSelect;

    impl Relation for CondSelect {
        type Witness = ();

        type Instance = ();

        const K: u32 = 10;

        fn from_statement(_instance: &Self::Instance, _witness: &Self::Witness) -> Self {
            CondSelect
        }

        fn format_instance(_instance: &Self::Instance) -> Vec<JubjubBase> {
            vec![]
        }

        fn circuit(
            &self,
            std_lib: &ZkStdLib,
            layouter: &mut impl Layouter<<Jubjub as CircuitCurve>::Base>,
        ) -> Result<(), Error> {
            let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
            let value_1 = JubjubBase::random(&mut rng);
            let value_2 = JubjubBase::random(&mut rng);

            let assigned_value_1 = std_lib.assign(layouter, Value::known(value_1))?;
            let assigned_value_2 = std_lib.assign(layouter, Value::known(value_2))?;

            let one = std_lib.assign_fixed(layouter, Bit(true))?;
            let zero = std_lib.assign_fixed(layouter, Bit(false))?;

            let select_one =
                std_lib.select(layouter, &one, &assigned_value_1, &assigned_value_2)?;
            let select_zero =
                std_lib.select(layouter, &zero, &assigned_value_1, &assigned_value_2)?;
            std_lib.assert_equal(layouter, &select_zero, &assigned_value_2)?;
            std_lib.assert_equal(layouter, &select_one, &assigned_value_1)?;

            Ok(())
        }
    }

    let circuit: MidnightCircuit<_> = CondSelect.into();
    let prover = MockProver::run(10, &circuit, vec![vec![]]).expect(
        "Failed to
generate proof",
    );
    prover.assert_satisfied();
}

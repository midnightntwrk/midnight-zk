use std::collections::HashMap;

use midnight_circuits::compact_std_lib::ZkStdLib;
use midnight_proofs::circuit::{Layouter, Value};

use crate::{
    instructions::{
        operations::{
            add_incircuit, assert_equal_incircuit, inner_product_incircuit, is_equal_incircuit,
            load_incircuit, mul_incircuit, neg_incircuit, publish_incircuit, sub_incircuit,
            Operation::*,
        },
        Instruction,
    },
    types::{CircuitValue, IrType, IrValue},
    utils::{constants::assign_constant, get_t, insert_many, F},
    Error,
};

pub struct Parser {
    memory: HashMap<String, CircuitValue>,
    witness: Value<HashMap<&'static str, IrValue>>,
    public_input_types: Vec<IrType>,
}

impl Parser {
    pub fn new(witness: Value<HashMap<&'static str, IrValue>>) -> Self {
        Self {
            memory: HashMap::new(),
            witness,
            public_input_types: vec![],
        }
    }

    pub fn public_input_types(self) -> Vec<IrType> {
        self.public_input_types
    }

    pub fn process_instruction(
        &mut self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instruction: &Instruction,
    ) -> Result<(), Error> {
        let inps = instruction
            .inputs
            .iter()
            .map(|name| match self.memory.get(name).cloned() {
                Some(v) => Ok(v),
                None => assign_constant(std_lib, layouter, name),
            })
            .collect::<Result<Vec<CircuitValue>, Error>>()?;

        let outputs = match instruction.operation {
            Load(t) => {
                let values: Vec<_> = instruction
                    .outputs
                    .iter()
                    .map(|name| self.witness.as_ref().map_with_result(|m| get_t(m, t, name)))
                    .collect::<Result<_, Error>>()?;
                load_incircuit(std_lib, layouter, t, &values)?
            }
            Publish => {
                inps.iter().try_for_each(|v| {
                    self.public_input_types.push(v.get_type());
                    publish_incircuit(std_lib, layouter, v)
                })?;
                vec![]
            }
            AssertEqual => {
                assert_equal_incircuit(std_lib, layouter, &inps[0], &inps[1])?;
                vec![]
            }
            IsEqual => vec![is_equal_incircuit(std_lib, layouter, &inps[0], &inps[1])?],
            Add => vec![add_incircuit(std_lib, layouter, &inps[0], &inps[1])?],
            Sub => vec![sub_incircuit(std_lib, layouter, &inps[0], &inps[1])?],
            Mul => vec![mul_incircuit(std_lib, layouter, &inps[0], &inps[1])?],
            Neg => vec![neg_incircuit(std_lib, layouter, &inps[0])?],
            InnerProduct => vec![inner_product_incircuit(
                std_lib,
                layouter,
                &inps[..inps.len() / 2],
                &inps[inps.len() / 2..],
            )?],
        };

        insert_many(&mut self.memory, &instruction.outputs, &outputs)
    }
}

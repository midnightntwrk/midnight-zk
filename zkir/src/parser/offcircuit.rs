use std::collections::HashMap;

use crate::{
    instructions::{
        operations::{
            add_offcircuit, inner_product_offcircuit, load_offcircuit, mul_offcircuit,
            neg_offcircuit, sub_offcircuit, Operation::*,
        },
        Instruction,
    },
    types::IrValue,
    utils::{get_t, insert_many},
    Error,
};

pub struct Parser {
    witness: HashMap<&'static str, IrValue>,
    memory: HashMap<String, IrValue>,
    public_inputs: Vec<IrValue>,
}

impl Parser {
    pub fn new(witness: HashMap<&'static str, IrValue>) -> Self {
        Self {
            witness,
            memory: HashMap::new(),
            public_inputs: vec![],
        }
    }

    pub fn public_inputs(self) -> Vec<IrValue> {
        self.public_inputs
    }

    /// Instructions are assumed to have the right arity.
    pub fn process_instruction(&mut self, instruction: &Instruction) -> Result<(), Error> {
        let inps = instruction
            .inputs
            .iter()
            .map(|name| match self.memory.get(name).cloned() {
                Some(v) => Ok(v),
                None => name.as_str().try_into(),
            })
            .collect::<Result<Vec<IrValue>, Error>>()?;

        let outputs: Vec<IrValue> = match instruction.operation {
            Load(t) => {
                let values: Vec<_> = instruction
                    .outputs
                    .iter()
                    .map(|name| get_t(&self.witness, t, name))
                    .collect::<Result<_, Error>>()?;
                load_offcircuit(t, &values)?
            }
            Publish => {
                inps.into_iter().for_each(|v| self.public_inputs.push(v));
                vec![]
            }
            AssertEqual => {
                if inps[0] != inps[1] {
                    return Err(Error::Other(format!(
                        "assertion violated: {:?} == {:?}",
                        inps[0], inps[1]
                    )));
                }
                vec![]
            }
            IsEqual => vec![IrValue::Bool(inps[0] == inps[1])],
            Add => vec![add_offcircuit(&inps[0], &inps[1])?],
            Sub => vec![sub_offcircuit(&inps[0], &inps[1])?],
            Mul => vec![mul_offcircuit(&inps[0], &inps[1])?],
            Neg => vec![neg_offcircuit(&inps[0])?],
            InnerProduct => vec![inner_product_offcircuit(
                &inps[..inps.len() / 2],
                &inps[inps.len() / 2..],
            )?],
        };

        insert_many(&mut self.memory, &instruction.outputs, &outputs)
    }
}

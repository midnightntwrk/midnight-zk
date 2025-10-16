use std::collections::HashMap;

use crate::{
    instructions::{
        operations::{add_offcircuit, load_offcircuit, Operation::*},
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
                None => Err(Error::NotFound(name.clone())),
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
            Add => vec![add_offcircuit(&inps[0], &inps[1])?],
        };

        insert_many(&mut self.memory, &instruction.outputs, &outputs)
    }
}

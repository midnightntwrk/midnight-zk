use std::collections::HashMap;

use crate::{
    instructions::{
        operations::{
            add_offcircuit, affine_coordinates_offcircuit, inner_product_offcircuit,
            load_offcircuit, mod_exp_offcircuit, mul_offcircuit, neg_offcircuit,
            poseidon_offcircuit, sha256_offcircuit, sha512_offcircuit, sub_offcircuit,
            Operation::*,
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
                None => name.as_str().try_into().map_err(|_| Error::NotFound(name.clone())),
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
            AssertNotEqual => {
                if inps[0] == inps[1] {
                    return Err(Error::Other(format!(
                        "assertion violated: {:?} != {:?}",
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
            ModExp(n) => vec![mod_exp_offcircuit(&inps[0], n, &inps[1])?],
            InnerProduct => vec![inner_product_offcircuit(
                &inps[..inps.len() / 2],
                &inps[inps.len() / 2..],
            )?],
            AffineCoordinates => {
                let (x, y) = affine_coordinates_offcircuit(&inps[0])?;
                vec![x, y]
            }
            IntoBytes(n) => vec![inps[0].clone().into_bytes(n)?],
            FromBytes(t) => {
                if let IrValue::Bytes(v) = &inps[0] {
                    vec![IrValue::from_bytes(t, v)?]
                } else {
                    return Err(Error::Other(format!(
                        "expecting Bytes(n), got {:?}",
                        inps[0].get_type()
                    )));
                }
            }
            Poseidon => vec![poseidon_offcircuit(&inps)?],
            Sha256 => vec![sha256_offcircuit(&inps[0])?],
            Sha512 => vec![sha512_offcircuit(&inps[0])?],
        };

        insert_many(&mut self.memory, &instruction.outputs, &outputs)
    }
}

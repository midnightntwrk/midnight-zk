use std::{cell::RefCell, collections::HashMap, io, rc::Rc};

use bincode::{Decode, Encode};
use midnight_circuits::compact_std_lib::{MidnightCircuit, Relation, ZkStdLib, ZkStdLibArch};
use midnight_proofs::{
    circuit::{Layouter, Value},
    dev::cost_model::dummy_synthesize_run,
    plonk,
};
use serde::{Deserialize, Serialize};

use crate::{
    instructions::{operations::Operation, Instruction},
    parser,
    types::{CircuitValue, IrType, IrValue},
    utils::F,
    Error,
};

#[derive(Clone, Debug, Encode, Decode, Serialize, Deserialize)]
struct Program {
    instructions: Vec<Instruction>,
}

#[derive(Clone, Debug)]
/// A ZKIR relation, described by a ZKIR program (a list of ZKIR instructions).
pub struct ZkirRelation {
    program: Program,
    public_input_types: Rc<RefCell<Vec<IrType>>>,
}

impl ZkirRelation {
    /// Creates a new ZKIR relation from the given ZKIR instructions.
    pub fn from_instructions(instructions: &[Instruction]) -> Result<Self, Error> {
        instructions.iter().try_for_each(|instr| instr.check_arity())?;
        let program = Program {
            instructions: instructions.to_vec(),
        };
        Ok(Self {
            program,
            public_input_types: Rc::new(RefCell::new(Vec::new())),
        })
    }

    /// Reads a ZKIR relation from a JSON string.
    pub fn read(raw: &'static str) -> Result<Self, Error> {
        let p: Program = serde_json::from_str(raw).map_err(|e| Error::Other(e.to_string()))?;
        Self::from_instructions(&p.instructions)
    }

    /// Returns a vector of raw PLONK public inputs (paired with their types),
    /// which are automatically computed from the witness seed via an
    /// off-circuit execution of the underlying ZKIR program.
    ///
    /// The public input types are automatically derived via a dummy in-circuit
    /// run if necessary.
    pub fn public_inputs(
        &self,
        witness: HashMap<&'static str, IrValue>,
    ) -> Result<Vec<(IrValue, IrType)>, Error> {
        let mut parser = parser::offcircuit::Parser::new(witness);
        (self.program.instructions.iter()).try_for_each(|i| parser.process_instruction(i))?;
        let pis = parser.public_inputs();
        let pi_types = self.public_input_types.borrow().clone();

        if pis.len() == pi_types.len() {
            return Ok(pis.into_iter().zip(pi_types).collect());
        }

        // If the public input types are not known, we can initialize them with an
        // in-circuit parser pass.
        dummy_synthesize_run(&MidnightCircuit::from_relation(self))?;
        let pi_types = self.public_input_types.borrow().clone();
        assert_eq!(pis.len(), pi_types.len());
        Ok(pis.into_iter().zip(pi_types).collect())
    }
}

impl Relation for ZkirRelation {
    type Instance = Vec<(IrValue, IrType)>;

    type Witness = HashMap<&'static str, IrValue>;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, plonk::Error> {
        instance
            .iter()
            .map(|(v, t)| CircuitValue::as_public_input(v, *t))
            .collect::<Result<Vec<_>, Error>>()
            .map(|vec| vec.concat())
            .map_err(|_| plonk::Error::InvalidInstances)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), plonk::Error> {
        let mut parser = parser::incircuit::Parser::new(witness);

        for instruction in self.program.instructions.iter() {
            parser.process_instruction(std_lib, layouter, instruction)?
        }

        *self.public_input_types.borrow_mut() = parser.public_input_types();

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        use Operation::*;

        let operations: Vec<_> =
            self.program.instructions.iter().map(|instr| instr.operation).collect();

        let loads_types = |target_types: &[IrType]| -> bool {
            operations
                .iter()
                .any(|op| matches!(op, Load(val_t) if target_types.contains(val_t)))
        };

        ZkStdLibArch {
            jubjub: loads_types(&[IrType::JubjubPoint, IrType::JubjubScalar]),
            poseidon: false,
            sha256: false,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            nr_pow2range_cols: 4,
            automaton: false,
            base64: false,
        }
    }

    fn write_relation<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        bincode::encode_into_std_write(self.program.clone(), writer, bincode::config::standard())
            .map(|_nb_bytes_written| ())
            .map_err(io::Error::other)
    }

    fn read_relation<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let program = bincode::decode_from_std_read(reader, bincode::config::standard())
            .map(|(program, _bytes_read): (Program, usize)| program)
            .map_err(io::Error::other)?;

        Self::from_instructions(&program.instructions)
            .map_err(|e| io::Error::other(format!("{e:?}")))
    }
}

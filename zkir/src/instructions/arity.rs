use std::fmt;

use crate::{
    instructions::{operations::Operation, Instruction},
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arity {
    Fixed(usize),
    Some,
    SomeEven,
}

impl fmt::Display for Arity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arity::Fixed(n) => write!(f, "{n}"),
            Arity::Some => write!(f, "some"),
            Arity::SomeEven => write!(f, "even"),
        }
    }
}

impl Operation {
    pub(crate) fn input_arity(&self) -> Arity {
        use Arity::*;
        use Operation::*;
        match self {
            Load(_) => Fixed(0), // `Load` takes witnesess, not actual inputs
            Publish => Some,
            AssertEqual => Fixed(2),
            IsEqual => Fixed(2),
            Add => Fixed(2),
            Sub => Fixed(2),
            Mul => Fixed(2),
            Neg => Fixed(1),
            InnerProduct => SomeEven,
        }
    }

    pub(crate) fn output_arity(&self) -> Arity {
        use Arity::*;
        use Operation::*;
        match self {
            Load(_) => Some,
            Publish => Fixed(0), // `Publish` increases the `instances` but does not return outputs
            AssertEqual => Fixed(0),
            IsEqual => Fixed(1),
            Add => Fixed(1),
            Sub => Fixed(1),
            Mul => Fixed(1),
            Neg => Fixed(1),
            InnerProduct => Fixed(1),
        }
    }
}

impl Arity {
    fn check(self, len: usize, op: &Operation) -> Result<(), Error> {
        match self {
            Arity::Fixed(n) if n != len => Err(Error::InvalidArity(*op)),
            Arity::Some if len == 0 => Err(Error::InvalidArity(*op)),
            Arity::SomeEven if len % 2 != 0 || len == 0 => Err(Error::InvalidArity(*op)),
            _ => Ok(()),
        }
    }
}

impl Instruction {
    pub(crate) fn check_arity(&self) -> Result<(), Error> {
        let op = &self.operation;
        op.input_arity().check(self.inputs.len(), op)?;
        op.output_arity().check(self.outputs.len(), op)
    }
}

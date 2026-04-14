use std::{collections::HashMap, fmt::Debug, hash::Hash, iter::repeat_n};

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use super::{
    der_encoding::{decode_length, decode_tag},
    Asn1Block, Asn1RawData, Asn1RawDataInternal, Asn1Spec, Asn1Tlv,
};
use crate::{
    field::AssignedNative,
    instructions::{
        arithmetic::ArithInstructions, assertions::AssertionInstructions,
        assignments::AssignmentInstructions, control_flow::ControlFlowInstructions,
        equality::EqualityInstructions, RangeCheckInstructions, ZeroInstructions,
    },
    parsing::scanner::{varlen::ScannerVec, AutomatonParser, ScannerChip, StdLibParser},
    types::{AssignedByte, InnerValue},
    CircuitField,
};

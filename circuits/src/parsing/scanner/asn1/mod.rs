//! ASN.1 parsing support: off-circuit encoding helpers, spec descriptor
//! types, and circuit-level structure verification. Follows the DER wire
//! format but does not enforce minimality of tag/length encodings.

pub mod der_encoding;
mod parser;
use std::{fmt::Debug, hash::Hash};

use midnight_proofs::circuit::Value;

use crate::parsing::scanner::asn1::der_encoding::encode_length;


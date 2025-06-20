//! Module implementing chips and gadgets to process JSON objects.

mod automaton_chip;
mod base64_chip;
mod data_types;
mod parser_gadget;

/// A module to convert regular expressions to finite automata that can be used
/// as basis for circuit gates.
pub mod automaton;
/// A module to specify languages as regular expressions and convert them into
/// finite automata.
pub mod regex;

/// A letter from the automaton alphabet.
pub type RegexLetter = u8;
/// Maximal size of the alphabet, since input characters are represented by
/// `AssignedByte`. The parser (`automaton_chip::parse`) is using this
/// information to store automaton final states in the transition table, by
/// encoding them as impossible transitions starting from the said state, and
/// labelled with letter `REGEX_ALPHABET_MAX_SIZE`.
pub const REGEX_ALPHABET_MAX_SIZE: usize = 256;

mod table;

pub use automaton_chip::AutomatonChip;
pub use base64_chip::*;
pub use data_types::{DateFormat, Separator};
pub use parser_gadget::*;

use bincode::{Decode, Encode};
use midnight_curves::{Fr as JubjubScalar, JubjubSubgroup};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use crate::{utils::*, Error};

/// Type of IR values.
#[derive(Clone, Copy, Debug, PartialEq, Encode, Decode, Serialize, Deserialize)]
pub enum IrType {
    /// Boolean (true or false)
    Bool,

    /// Array of bytes of the given length.
    Bytes(usize),

    /// Element of the BLS12-381 scalar field, a.k.a. the native field.
    /// This is also the base field of Jubjub.
    Native,

    /// Unsigned integer of the given length in bits. That is, BigUint(n) is an
    /// integer in the range [0, 2^n).
    BigUint(u32),

    /// Point of the Jubjub elliptic curve.
    JubjubPoint,

    /// Element of the scalar field of Jubjub.
    JubjubScalar,
}

/// Off-circuit IR value carrying actual data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrValue {
    /// A Boolean value.
    Bool(bool),

    /// An array of bytes.
    // We internally represent this type as a u8 vector, but note that its
    // length in the IR program is a hard-coded constant. Thus, this value
    // is actually an array and not a vector.
    Bytes(Vec<u8>),

    /// BLS12-381 scalar.
    Native(F),

    /// Big unsigned integer.
    BigUint(BigUint),

    /// Jubjub point.
    JubjubPoint(JubjubSubgroup),

    /// Jubjub scalar field value.
    JubjubScalar(JubjubScalar),
}

/// In-circuit IR value, it is a placeholder for an [IrValue], a circuit
/// variable that does not necessarily carry actual data.
/// (It will carry data during the proving process, but not during the circuit
/// compilation.)
#[derive(Clone, Debug)]
pub enum CircuitValue {
    Bool(AssignedBit),
    Bytes(Vec<AssignedByte>),
    Native(AssignedNative),
    BigUint(AssignedBigUint),
    JubjubPoint(AssignedJubjubPoint),
    JubjubScalar(AssignedJubjubScalar),
}

impl IrValue {
    pub(crate) fn get_type(&self) -> IrType {
        match self {
            IrValue::Bool(_) => IrType::Bool,
            IrValue::Bytes(v) => IrType::Bytes(v.len()),
            IrValue::Native(_) => IrType::Native,
            IrValue::BigUint(big) => IrType::BigUint(big.bits() as u32),
            IrValue::JubjubPoint(_) => IrType::JubjubPoint,
            IrValue::JubjubScalar(_) => IrType::JubjubScalar,
        }
    }

    pub(crate) fn check_type(&self, t: IrType) -> Result<(), Error> {
        if self.get_type() == t {
            return Ok(());
        }

        if let (IrValue::BigUint(big), IrType::BigUint(n)) = (self, t) {
            if big.bits() as u32 <= n {
                return Ok(());
            }
        }

        Err(Error::ExpectingType(t, self.get_type()))
    }
}

impl CircuitValue {
    pub fn get_type(&self) -> IrType {
        match self {
            CircuitValue::Bool(_) => IrType::Bool,
            CircuitValue::Bytes(v) => IrType::Bytes(v.len()),
            CircuitValue::Native(_) => IrType::Native,
            CircuitValue::BigUint(big) => IrType::BigUint(big.nb_bits()),
            CircuitValue::JubjubPoint(_) => IrType::JubjubPoint,
            CircuitValue::JubjubScalar(_) => IrType::JubjubScalar,
        }
    }
}

/// Implements both `From<T> for Enum` (wrap) and `TryFrom<Enum> for T` (unwrap)
/// for the specified enum variants.
macro_rules! impl_enum_from_try_from {
    ($enum:ident { $($variant:ident => $t:ty),* $(,)? }) => {
        $(
            // Wrap: From<T> -> Enum
            impl From<$t> for $enum {
                fn from(value: $t) -> Self {
                    $enum::$variant(value)
                }
            }

            // Unwrap: TryFrom<Enum> -> T
            impl std::convert::TryFrom<$enum> for $t {
                type Error = Error;

                fn try_from(value: $enum) -> Result<Self, Self::Error> {
                    match &value {
                        $enum::$variant(inner) => Ok(inner.clone()),
                        other => Err(Error::Other(format!("cannot convert {:?} to {:?}", other.get_type(), stringify!($variant)))),
                    }
                }
            }
        )*
    };
}

// Derives implementations, for every basic type T:
//  - From<T> for IrValue
//  - TryFrom<IrValue> for T
impl_enum_from_try_from!(IrValue {
    Bool => bool,
    Bytes => Vec<u8>,
    Native => F,
    BigUint => BigUint,
    JubjubPoint => JubjubSubgroup,
    JubjubScalar => JubjubScalar,
});

// Derives implementations, for every basic type T:
//  - From<T> for CircuitValue
//  - TryFrom<CircuitValue> for T
impl_enum_from_try_from!(CircuitValue {
    Bool => AssignedBit,
    Bytes => Vec<AssignedByte>,
    Native => AssignedNative,
    BigUint => AssignedBigUint,
    JubjubPoint => AssignedJubjubPoint,
    JubjubScalar => AssignedJubjubScalar,
});

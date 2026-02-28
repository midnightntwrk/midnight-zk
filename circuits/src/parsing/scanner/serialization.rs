use std::hash::Hash;

use rustc_hash::{FxHashMap, FxHashSet};

use super::automaton::Automaton;

/// Serialization of a data type into a vector of bytes (little-endian
/// convention).
pub(super) trait Serialize: Sized {
    /// Extends `buf` with a byte-vector representation of `self` (little
    /// endian).
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>);

    /// Converts the first elements of `buf` into a piece of data of type
    /// `Self`. Returns an error if the buffer does not encode a valid piece of
    /// data, or if `buf` does not contain enough bytes to encode one. If the
    /// result is not an error, the buffer is updated to start after
    /// the converted bytes.
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String>;

    /// Deserializes a the content of a slice, and returns the result, panicking
    /// with the corresponding error message in case the `Result` of
    /// `self.deserialize` is an `Error`.
    fn deserialize_unwrap(serialization: &[u8]) -> Self {
        let mut buf = serialization;
        match Self::deserialize(&mut buf) {
            Ok(x) => x,
            Err(msg) => panic!(
                "Deserialization error. Error message:\n=====\n{}\n=====",
                msg
            ),
        }
    }
}

macro_rules! ensure_buf_len {
    ($buf:expr, $required:expr, $type:ty) => {
        if $buf.len() < $required {
            return Err(format!(
                "Buffer underflow: expected at least {} bytes for deserializing `{}`, only got {}.\n>> Buffer:\n{:?}",
                $required,
                stringify!($type),
                $buf.len(),
                $buf,
            ));
        }
    };
}

impl Serialize for u8 {
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        buf.push(*self)
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        ensure_buf_len!(buf, 1, Self);
        let res = buf[0];
        *buf = &buf[1..];
        Ok(res)
    }
}

impl Serialize for u64 {
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        buf.extend(&self.to_le_bytes())
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        const U64_BYTES: usize = u64::BITS as usize / 8;
        ensure_buf_len!(buf, U64_BYTES, Self);
        let res = Self::from_le_bytes(buf[..U64_BYTES].try_into().unwrap());
        *buf = &buf[U64_BYTES..];
        Ok(res)
    }
}

// `usize` is serialized as `u64` to avoid the issue where the serializing and
// deserializing machines have different architectures.
impl Serialize for usize {
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        (*self as u64).serialize(buf)
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        let val = u64::deserialize(buf)?;
        if val > (usize::MAX as u64) {
            Err(format!(
                "Cannot deserialize value {} into usize on this platform",
                val
            ))
        } else {
            Ok(val as usize)
        }
    }
}

// It could be possible to optimise the serialization of booleans by encoding
// packs of at most 8 into a single byte. However, in the case of the
// serialization of the `RawAutomaton` type, this would only save two bytes per
// serialized automaton, which is quite insignificant.
impl Serialize for bool {
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        if *self { 1u8 } else { 0u8 }.serialize(buf)
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        Ok(u8::deserialize(buf)? == 1)
    }
}

impl<T> Serialize for Option<T>
where
    T: Serialize,
{
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        match self {
            None => false.serialize(buf),
            Some(x) => {
                true.serialize(buf);
                x.serialize(buf);
            }
        }
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        if !bool::deserialize(buf)? {
            Ok(None)
        } else {
            Ok(Some(T::deserialize(buf)?))
        }
    }
}

impl<T, U> Serialize for (T, U)
where
    T: Serialize,
    U: Serialize,
{
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        self.0.serialize(buf);
        self.1.serialize(buf);
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        let x = T::deserialize(buf)?;
        let y = U::deserialize(buf)?;
        Ok((x, y))
    }
}

// A bit redundant with the implementation for binary tuples, but probably still
// tolerable. If Serialize has to be later implemented for even further tuple
// types, factor everything out with a macro.
impl<T, U, V> Serialize for (T, U, V)
where
    T: Serialize,
    U: Serialize,
    V: Serialize,
{
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        self.0.serialize(buf);
        self.1.serialize(buf);
        self.2.serialize(buf);
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        let x = T::deserialize(buf)?;
        let y = U::deserialize(buf)?;
        let z = V::deserialize(buf)?;
        Ok((x, y, z))
    }
}

impl<T> Serialize for Vec<T>
where
    T: Serialize,
{
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        // The length is serialized so to know when to stop during deserialization.
        self.len().serialize(buf);
        for x in self {
            x.serialize(buf)
        }
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        let len = usize::deserialize(buf)?;
        let mut res = Vec::with_capacity(len);
        for _ in 0..len {
            res.push(T::deserialize(buf)?);
        }
        Ok(res)
    }
}

impl<T> Serialize for FxHashSet<T>
where
    T: Serialize + Copy + Hash + Ord,
{
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        let mut v = Vec::from_iter(self.iter().copied());
        // Sorting is necessary to ensure the determinism of serialization.
        v.sort();
        v.serialize(buf)
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        let v = Vec::<T>::deserialize(buf)?;
        Ok(FxHashSet::from_iter(v))
    }
}

// This serialization of `HashMap` assumes that the deserializing the key type
// `K` can be unambiguously done even if the key's encoding is followed directly
// by the value's encoding. In practice, keys will always be types that have a
// fixed size anyway.
impl<K, T> Serialize for FxHashMap<K, T>
where
    K: Serialize + Copy + Hash + Ord,
    T: Serialize + Clone,
{
    #[cfg(test)]
    fn serialize(&self, buf: &mut Vec<u8>) {
        let mut v = Vec::from_iter(self.iter().map(|(k, v)| (*k, v.clone())));
        // Sorting is necessary to ensure the determinism of serialization.
        v.sort_by_key(|e| e.0);
        v.serialize(buf)
    }
    fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
        let v = Vec::<(K, T)>::deserialize(buf)?;
        Ok(FxHashMap::from_iter(v))
    }
}

/// A macro rule implementing `Serialize` for a `struct`, assuming all fields
/// already implement it. To call the macro, e.g., on a struct `S` with two
/// fields called `x` and `y`, one would write:
///
/// ```text
/// impl_serialize_for_struct(S { x, y })
/// ```
macro_rules! impl_serialize_for_struct {
    ($type:ident { $($field:ident),* }) => {
        impl Serialize for $type {
            #[cfg(test)]
            fn serialize(&self, buf: &mut Vec<u8>) {
                $( self.$field.serialize(buf); )*
            }

            fn deserialize(buf: &mut &[u8]) -> Result<Self, String> {
                $( let $field = Serialize::deserialize(buf)?; )*
                Ok(Self { $($field),* })
            }
        }
    };
}

impl_serialize_for_struct!(Automaton {
    nb_states,
    initial_state,
    final_states,
    transitions
});

#[cfg(test)]
mod tests {
    use std::fmt::Debug;

    use rustc_hash::{FxHashMap, FxHashSet};

    use super::Serialize;

    // Test of serialization functionalities.
    fn serialization_one_test<T>(x: T, type_name: &str)
    where
        T: Serialize + Debug + Eq,
    {
        println!(">> Testing the {} serialization: {:?}", type_name, x);
        let mut buf = Vec::new();
        x.serialize(&mut buf);
        let mut slice: &[u8] = &buf;
        let y = T::deserialize(&mut slice);
        let y = match y {
            Err(s) => panic!(
                "deserialization failed!\nBuffer: {:?}\nError message: {}",
                buf, s
            ),
            Ok(y) => y,
        };
        assert!(x == y, "incorrect serialization!\nBuffer: {:?}", buf);
        println!("serialization succeeded!\nBuffer: {:?}", buf);
    }

    #[test]
    fn serialization_test() {
        serialization_one_test(2134098563175846_usize, "usize");
        serialization_one_test(213409856315_u64, "u64");
        for i in 0..256 {
            serialization_one_test(i as u8, "u8");
        }
        serialization_one_test(true, "bool");
        serialization_one_test(false, "bool");
        let test_vector: Vec<usize> = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let test_vector_pairs: Vec<(usize, u8)> =
            vec![(82365, 0), (82365, 2), (825, 4), (82365, 6), (82365, 7)];
        serialization_one_test(test_vector.clone(), "Vec<usize>");
        serialization_one_test(Some(test_vector.clone()), "Option<Vec<usize>>");
        serialization_one_test(None::<u64>, "Option<Vec<usize>>");
        serialization_one_test(None::<bool>, "Option<Vec<usize>>");
        serialization_one_test(
            None::<(
                Vec<(bool, usize)>,
                FxHashMap<usize, u64>,
                FxHashSet<(u64, usize, bool)>,
            )>,
            "Option<Vec<usize>>",
        );
        serialization_one_test(test_vector_pairs.clone(), "Vec<(usize,u8)>");
        serialization_one_test(
            (test_vector_pairs.clone(), 84065_u64, true),
            "(Vec<(usize,u8)>, u64, bool)",
        );
        serialization_one_test(
            FxHashSet::from_iter(test_vector.clone()),
            "FxHashSet<usize>",
        );
        serialization_one_test(
            FxHashMap::from_iter(test_vector_pairs.clone()),
            "FxHashMap<usize,u8>",
        );
    }

    #[test]
    fn test_serialization_regex_instructions() {
        // Implement a test for the serialization of regexinstructions.
        // 1. fetch the result from all deserialization (force recompute if they
        //    don't exist)
        // 2. recompute all fetched instructions (skip if done at the previous
        //    step)
        // 3. compare the recomputed data with the fetched data for all of them
        // 4. All serialized instructions should be tested so that running this
        //    test ensures that all required instructions are serialized
        // 5. [TODO] the serialization should force the determinisation, to save
        //    computation. Probably done by modifying
        //    `to_raw_automaton_serialized`
    }
}

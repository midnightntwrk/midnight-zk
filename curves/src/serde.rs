use std::{convert::TryInto, fmt::Debug};

#[derive(Clone, Copy, Debug)]
pub struct Repr<const T: usize>([u8; T]);

impl<const T: usize> Repr<T> {
    pub fn inner(&self) -> &[u8; T] {
        &self.0
    }
}

impl<const T: usize> From<[u8; T]> for Repr<T> {
    fn from(bytes: [u8; T]) -> Self {
        Self(bytes)
    }
}

impl<const T: usize> From<&[u8]> for Repr<T> {
    fn from(bytes: &[u8]) -> Self {
        Self(bytes.try_into().unwrap())
    }
}

impl<const T: usize> From<Repr<T>> for [u8; T] {
    fn from(repr: Repr<T>) -> Self {
        repr.0
    }
}

impl<const T: usize> Default for Repr<T> {
    fn default() -> Self {
        Self([0u8; T])
    }
}

impl<const T: usize> AsMut<[u8]> for Repr<T> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl<const T: usize> AsRef<[u8]> for Repr<T> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const T: usize> std::ops::Index<std::ops::Range<usize>> for Repr<T> {
    type Output = [u8];

    fn index(&self, range: std::ops::Range<usize>) -> &Self::Output {
        &self.0[range]
    }
}

impl<const T: usize> std::ops::Index<usize> for Repr<T> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<const T: usize> std::ops::Index<std::ops::RangeTo<usize>> for Repr<T> {
    type Output = [u8];

    fn index(&self, range: std::ops::RangeTo<usize>) -> &Self::Output {
        &self.0[range]
    }
}

impl<const T: usize> std::ops::Index<std::ops::RangeFrom<usize>> for Repr<T> {
    type Output = [u8];

    fn index(&self, range: std::ops::RangeFrom<usize>) -> &Self::Output {
        &self.0[range]
    }
}

impl<const T: usize> std::ops::IndexMut<std::ops::Range<usize>> for Repr<T> {
    fn index_mut(&mut self, range: std::ops::Range<usize>) -> &mut Self::Output {
        &mut self.0[range]
    }
}

// Re-export SerdeObject from serde_traits to avoid duplication
pub use crate::serde_traits::SerdeObject;

pub mod endian {
    use std::convert::TryInto;

    pub trait EndianRepr: Sized {
        const ENDIAN: Endian;

        fn to_bytes(&self) -> Vec<u8>;

        fn from_bytes(x: &[u8]) -> subtle::CtOption<Self>;
    }

    pub enum Endian {
        LE,
        BE,
    }

    impl Endian {
        pub fn to_bytes(&self, res: &mut [u8], el: &[u64]) {
            match self {
                Endian::LE => {
                    el.iter().enumerate().for_each(|(i, limb)| {
                        let off = i * 8;
                        res[off..off + 8].copy_from_slice(&limb.to_le_bytes());
                    });
                }
                Endian::BE => {
                    el.iter().rev().enumerate().for_each(|(i, limb)| {
                        let off = i * 8;
                        res[off..off + 8].copy_from_slice(&limb.to_be_bytes());
                    });
                }
            }
        }

        pub fn from_bytes(&self, res: &[u8], el: &mut [u64]) {
            match self {
                Endian::LE => {
                    el.iter_mut().enumerate().for_each(|(i, limb)| {
                        let off = i * 8;
                        *limb = u64::from_le_bytes(res[off..off + 8].try_into().unwrap());
                    });
                }
                Endian::BE => {
                    el.iter_mut().rev().enumerate().for_each(|(i, limb)| {
                        let off = i * 8;
                        *limb = u64::from_be_bytes(res[off..off + 8].try_into().unwrap());
                    });
                }
            }
        }
    }
}

pub mod engine;
pub mod field;
pub mod field_halo2curves;

pub fn hex_to_bytes(hex: &str) -> Vec<u8> {
    hex::decode(hex).expect("Invalid hex string")
}

//! WASM bindings for Multi-Scalar Multiplication (MSM) operations on G1 points.

use js_sys::Uint8Array;
use wasm_bindgen::prelude::*;

use crate::g1::{G1Compressed, G1Uncompressed};
use crate::{Fq, G1Affine, G1Projective};
use group::{Group, GroupEncoding, UncompressedEncoding};

/// Compute MSM from JavaScript arrays of points and scalars.
#[wasm_bindgen]
pub fn msm_from_bytes(
    points: js_sys::Array,
    scalars: js_sys::Array,
) -> Result<G1Projective, JsValue> {
    if points.length() != scalars.length() {
        return Err(JsValue::from_str("Mismatched point/scalar count"));
    }

    let mut g1s: Vec<G1Projective> = Vec::with_capacity(points.length() as usize);
    let mut fqs = Vec::with_capacity(scalars.length() as usize);

    for i in 0..points.length() {
        let p_val = points.get(i);
        let s_val = scalars.get(i);

        let p_bytes = Uint8Array::new(&p_val).to_vec();
        let s_bytes = Uint8Array::new(&s_val).to_vec();

        if p_bytes.len() != 96 {
            return Err(JsValue::from_str("Point must be 96 bytes (uncompressed)"));
        }
        let mut uncompressed = G1Uncompressed::default();
        uncompressed.as_mut().copy_from_slice(&p_bytes);
        let point: G1Projective = G1Affine::from_uncompressed_unchecked(&uncompressed)
            .into_option()
            .ok_or_else(|| JsValue::from_str("Invalid G1Affine"))?
            .into();

        let mut buffer = [0u8; 32];
        buffer.copy_from_slice(&s_bytes);
        let scalar = Fq::from_bytes_le(&buffer)
            .into_option()
            .ok_or_else(|| JsValue::from_str("Invalid scalar"))?;

        g1s.push(point);
        fqs.push(scalar);
    }

    let result = G1Projective::multi_exp(&g1s, &fqs);
    Ok(result)
}

/// Compute MSM for a chunk of points and scalars.
/// Returns the compressed bytes of the resulting G1 point.
#[wasm_bindgen]
pub fn msm_chunk(points: js_sys::Array, scalars: js_sys::Array) -> Result<Vec<u8>, JsValue> {
    let result = msm_from_bytes(points, scalars)?;
    let compressed = result.to_bytes();
    Ok(compressed.as_ref().to_vec())
}

/// Sum multiple G1 points from compressed byte arrays.
#[wasm_bindgen]
pub fn sum_g1_points(compressed_points: js_sys::Array) -> Result<G1Projective, JsValue> {
    let mut result = G1Projective::identity();

    for i in 0..compressed_points.length() {
        let bytes_val = compressed_points.get(i);
        let bytes = Uint8Array::new(&bytes_val).to_vec();

        if bytes.len() != 48 {
            return Err(JsValue::from_str(
                "Invalid compressed point size (expected 48 bytes)",
            ));
        }

        let mut compressed = G1Compressed::default();
        compressed.as_mut().copy_from_slice(&bytes);

        let point = G1Projective::from_bytes(&compressed)
            .into_option()
            .ok_or_else(|| JsValue::from_str("Invalid compressed G1 point"))?;

        result += point;
    }

    Ok(result)
}

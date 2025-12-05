//! Type conversions between midnight-curves and ICICLE types
//!
//! ICICLE uses uncompressed point representations:
//! - ScalarField: 32 bytes (Fr field element)
//! - G1Affine: 96 bytes (x: 48 bytes Fq, y: 48 bytes Fq)
//! - G1Projective: 144 bytes (x, y, z: each 48 bytes Fq)
//!
//! Strategy: Direct field element conversion via bytes, avoiding point validation overhead

use midnight_curves::{Fq as Scalar, Fp, G1Affine, G1Projective};

#[cfg(feature = "gpu")]
use icicle_bls12_381::curve::{
    ScalarField as IcicleScalar,
    BaseField as IcicleBaseField,
    G1Affine as IcicleG1Affine,
    G1Projective as IcicleG1Projective,
};
#[cfg(feature = "gpu")]
use icicle_core::ecntt::Projective as IcicleProjective;
#[cfg(feature = "gpu")]
use icicle_core::bignum::BigNum;
#[cfg(feature = "gpu")]
use halo2curves::CurveAffine;
#[cfg(feature = "gpu")]
use ff::PrimeField;

/// Type converter for midnight-curves <-> ICICLE types
#[derive(Debug)]
pub struct TypeConverter;

#[cfg(feature = "gpu")]
impl TypeConverter {
    /// Convert midnight Scalar (Fr) to ICICLE ScalarField
    #[inline]
    pub fn scalar_to_icicle(scalar: &Scalar) -> IcicleScalar {
        let bytes = scalar.to_repr();
        IcicleScalar::from_bytes_le(bytes.as_ref())
    }
    
    /// Convert slice of scalars - batched for efficiency
    pub fn scalar_slice_to_icicle_vec(scalars: &[Scalar]) -> Vec<IcicleScalar> {
        scalars.iter().map(|s| {
            let bytes = s.to_repr();
            IcicleScalar::from_bytes_le(bytes.as_ref())
        }).collect()
    }
    
    /// Convert midnight Fp (base field) to ICICLE BaseField
    #[inline]
    fn fp_to_icicle_base(fp: &Fp) -> IcicleBaseField {
        let bytes = fp.to_repr();
        IcicleBaseField::from_bytes_le(bytes.as_ref())
    }
    
    /// Convert midnight G1Affine to ICICLE G1Affine
    /// Extracts x,y coordinates and converts each field element
    #[inline]
    pub fn g1_affine_to_icicle(point: &G1Affine) -> IcicleG1Affine {
        
        // Get coordinates as Fp elements
        let coords = point.coordinates().unwrap();
        let x = Self::fp_to_icicle_base(coords.x());
        let y = Self::fp_to_icicle_base(coords.y());
        
        IcicleG1Affine { x, y }
    }
    
    /// Convert slice of G1Affine points
    pub fn g1_affine_slice_to_icicle_vec(points: &[G1Affine]) -> Vec<IcicleG1Affine> {
        points.iter().map(Self::g1_affine_to_icicle).collect()
    }
    
    /// Convert ICICLE BaseField back to midnight Fp
    #[inline]
    fn icicle_base_to_fp(icicle: &IcicleBaseField) -> Option<Fp> {
        let bytes = icicle.to_bytes_le();
        let byte_array: [u8; 48] = bytes.as_slice().try_into().ok()?;
        Fp::from_bytes_le(&byte_array).into_option()
    }
    
    /// Convert ICICLE G1Projective back to midnight G1Projective
    /// Converts to affine first (ICICLE provides to_affine), then reconstructs point
    pub fn icicle_to_g1_projective(icicle: &IcicleG1Projective) -> G1Projective {
        // Convert to affine coordinates
        let affine = icicle.to_affine();
        
        // Extract x, y and convert to midnight Fp
        let x = Self::icicle_base_to_fp(&affine.x)
            .expect("Invalid x coordinate from ICICLE");
        let y = Self::icicle_base_to_fp(&affine.y)
            .expect("Invalid y coordinate from ICICLE");
        
        // Reconstruct midnight affine point (from_xy validates the point is on curve)
        let midnight_affine = G1Affine::from_xy(x, y)
            .into_option()
            .expect("Invalid point from ICICLE");
        
        // Convert to projective
        G1Projective::from(midnight_affine)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[cfg(feature = "gpu")]
    #[test]
    fn test_scalar_conversion() {
        use ff::Field;
        let scalar = Scalar::ONE;
        let icicle = TypeConverter::scalar_to_icicle(&scalar);
        // Can't easily test roundtrip without implementing reverse conversion
        let _ = icicle; // Just verify it compiles and runs
    }
    
    #[cfg(feature = "gpu")]
    #[test]
    fn test_point_conversion() {
        use group::Group;
        let point = G1Affine::generator();
        let icicle = TypeConverter::g1_affine_to_icicle(&point);
        let _ = icicle; // Just verify it compiles and runs
    }
}

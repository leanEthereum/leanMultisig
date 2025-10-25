//! Witness generation for VM execution traces

pub mod dot_product;
pub mod multilinear_eval;
pub mod poseidon16;
pub mod poseidon24;

pub use dot_product::*;
pub use multilinear_eval::*;
pub use poseidon16::*;
pub use poseidon24::*;

use crate::F;

pub trait PoseidonWitnessTrait<const WIDTH: usize> {
    fn inputs(&self) -> &[F; WIDTH];
}

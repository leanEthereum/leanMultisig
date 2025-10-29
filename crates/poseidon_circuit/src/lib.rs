#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use multilinear_toolkit::prelude::MultilinearPoint;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};

mod prove;
pub use prove::*;

mod verify;
pub use verify::*;

mod utils;
pub use utils::*;

mod witness_gen;
pub use witness_gen::*;

pub mod tests;

pub mod gkr_layers;
pub use gkr_layers::*;

pub(crate) type F = KoalaBear;
pub(crate) type EF = QuinticExtensionFieldKB;

#[derive(Debug, Clone)]
pub struct GKRPoseidonResult {
    pub output_values: Vec<EF>,                            // of length width
    pub input_statements: (MultilinearPoint<EF>, Vec<EF>), // of length width, remain to be proven
    pub cubes_statements: (MultilinearPoint<EF>, Vec<EF>), // of length n_committed_cubes, remain to be proven
}

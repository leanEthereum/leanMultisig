#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use multilinear_toolkit::prelude::MultilinearPoint;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};

mod prove;
pub use prove::*;

mod verify;
pub use verify::*;

mod witness_gen;
pub use witness_gen::*;

#[cfg(test)]
mod tests;

pub mod gkr_layers;
pub use gkr_layers::*;

pub(crate) type F = KoalaBear;
pub(crate) type EF = QuinticExtensionFieldKB;

#[derive(Debug, Clone)]
pub struct GKRPoseidonResult<const WIDTH: usize, const N_COMMITED_CUBES: usize> {
    pub output_values: [EF; WIDTH],
    pub input_statements: (MultilinearPoint<EF>, [EF; WIDTH]), // remain to be proven
    pub cubes_statements: (MultilinearPoint<EF>, [EF; N_COMMITED_CUBES]), // remain to be proven
}

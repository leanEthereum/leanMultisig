#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use backend::*;

mod prove;
pub use prove::*;

mod verify;
pub use verify::*;

mod utils;
pub use utils::*;

mod witness_gen;
pub use witness_gen::*;

pub mod gkr_layers;
pub use gkr_layers::*;

pub(crate) type F = KoalaBear;
pub(crate) type EF = QuinticExtensionFieldKB;

#[derive(Debug, Clone)]
pub struct GKRPoseidonResult {
    pub input_point: MultilinearPoint<EF>,
    pub input_evals: Vec<EF>,
}

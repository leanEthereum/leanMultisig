#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use multilinear_toolkit::prelude::{Evaluation, MultiEvaluation};
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

/// remain to be proven
#[derive(Debug, Clone)]
pub struct GKRPoseidonResult {
    pub output_statements: MultiEvaluation<EF>, // of length width
    pub input_statements: MultiEvaluation<EF>,  // of length width
    pub cubes_statements: MultiEvaluation<EF>,  // of length n_committed_cubes
    pub on_compression_selector: Option<Evaluation<EF>>, // univariate_skips = 1 here (TODO dont do this)
}

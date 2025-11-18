#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_air::Air;

mod prove;
mod table;
mod uni_skip_utils;
mod utils;
mod verify;

pub use prove::*;
pub use table::*;
pub use verify::*;

#[cfg(test)]
pub mod tests;

pub trait MyAir<EF: ExtensionField<PF<EF>>>: Air + SumcheckComputationForAir + Send + Sync {}

impl<EF, A> MyAir<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: Air + SumcheckComputationForAir + Send + Sync,
{
}

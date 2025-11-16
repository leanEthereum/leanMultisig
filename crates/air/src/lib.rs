#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use ::utils::ConstraintChecker;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_uni_stark::SymbolicAirBuilder;

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

pub trait MyAir<EF: ExtensionField<PF<EF>>>:
    Air<SymbolicAirBuilder<PF<EF>>>
    + for<'a> Air<ConstraintFolder<'a, PF<EF>, EF>>
    + for<'a> Air<ConstraintFolder<'a, EF, EF>>
    + for<'a> Air<ConstraintChecker<'a, PF<EF>, EF>>
    + for<'a> Air<ConstraintChecker<'a, EF, EF>>
    + for<'a> Air<ConstraintFolderPackedBase<'a, EF>>
    + for<'a> Air<ConstraintFolderPackedExtension<'a, EF>>
    + SumcheckComputationForAir
    + Send
    + Sync
{
}

impl<EF, A> MyAir<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: Air<SymbolicAirBuilder<PF<EF>>>
        + for<'a> Air<ConstraintFolder<'a, PF<EF>, EF>>
        + for<'a> Air<ConstraintFolder<'a, EF, EF>>
        + for<'a> Air<ConstraintChecker<'a, PF<EF>, EF>>
        + for<'a> Air<ConstraintChecker<'a, EF, EF>>
        + for<'a> Air<ConstraintFolderPackedBase<'a, EF>>
        + for<'a> Air<ConstraintFolderPackedExtension<'a, EF>>
        + SumcheckComputationForAir
        + Send
        + Sync,
{
}

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use ::utils::{
    ConstraintChecker, ConstraintFolder, ConstraintFolderPackedBase,
    ConstraintFolderPackedExtension, PF,
};
use p3_air::Air;
use p3_field::ExtensionField;
use p3_uni_stark::SymbolicAirBuilder;

mod prove;
pub mod table;
mod uni_skip_utils;
mod utils;
mod verify;

#[cfg(test)]
mod test;

pub trait NormalAir<EF: ExtensionField<PF<EF>>>:
    Air<SymbolicAirBuilder<PF<EF>>>
    + for<'a> Air<ConstraintFolder<'a, PF<EF>, EF>>
    + for<'a> Air<ConstraintFolder<'a, EF, EF>>
    + for<'a> Air<ConstraintChecker<'a, PF<EF>, EF>>
    + for<'a> Air<ConstraintChecker<'a, EF, EF>>
{
}

pub trait PackedAir<EF: ExtensionField<PF<EF>>>:
    for<'a> Air<ConstraintFolderPackedBase<'a, EF>>
    + for<'a> Air<ConstraintFolderPackedExtension<'a, EF>>
{
}

impl<EF, A> NormalAir<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: Air<SymbolicAirBuilder<PF<EF>>>
        + for<'a> Air<ConstraintFolder<'a, PF<EF>, EF>>
        + for<'a> Air<ConstraintFolder<'a, EF, EF>>
        + for<'a> Air<ConstraintChecker<'a, PF<EF>, EF>>
        + for<'a> Air<ConstraintChecker<'a, EF, EF>>,
{
}

impl<EF, A> PackedAir<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: for<'a> Air<ConstraintFolderPackedBase<'a, EF>>
        + for<'a> Air<ConstraintFolderPackedExtension<'a, EF>>,
{
}

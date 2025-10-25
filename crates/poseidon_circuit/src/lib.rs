#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};

mod prove;
pub use prove::*;

mod verify;
pub use verify::*;

mod witness_gen;
pub use witness_gen::*;

#[cfg(test)]
mod tests;

pub(crate) mod gkr_layers;

pub(crate) type F = KoalaBear;
pub(crate) type EF = QuinticExtensionFieldKB;


#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod prove;
mod uni_skip_utils;
mod utils;
mod validity_check;
mod verify;

use multilinear_toolkit::prelude::{Field, MultilinearPoint};
pub use prove::*;
pub use validity_check::*;
pub use verify::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AirClaims<EF: Field> {
    pub point: MultilinearPoint<EF>,
    pub evals_f: Vec<EF>,
    pub evals_ef: Vec<EF>,

    // only for columns with a "shift", in case univariate skip == 1
    pub down_point: Option<MultilinearPoint<EF>>,
    pub evals_f_on_down_columns: Vec<EF>,
    pub evals_ef_on_down_columns: Vec<EF>,
}

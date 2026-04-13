#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod prove;
mod verify;

use backend::{Field, MultilinearPoint};
pub use prove::*;
pub use verify::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AirClaims<EF: Field> {
    pub point: MultilinearPoint<EF>,
    pub evals: Vec<EF>,
    pub evals_down: Vec<EF>, // columns 'shifted down' by one row
}

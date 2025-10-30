/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

*/

mod quotient_gkr;

mod logup_star;
pub use logup_star::*;

mod product_gkr;
pub use product_gkr::*;

pub(crate) const MIN_VARS_FOR_PACKING: usize = 8;

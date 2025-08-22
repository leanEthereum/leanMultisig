use dot_product::WitnessDotProduct;
use multilinear_eval::WitnessMultilinearEval;
use poseidon::{WitnessPoseidon16, WitnessPoseidon24};

pub mod dot_product;
pub mod multilinear_eval;
pub mod poseidon;

/// An enum to encapsulate any possible precompile witness.
#[derive(Debug)]
pub enum Witness {
    Poseidon16(WitnessPoseidon16),
    Poseidon24(WitnessPoseidon24),
    DotProduct(WitnessDotProduct),
    MultilinearEval(WitnessMultilinearEval),
}

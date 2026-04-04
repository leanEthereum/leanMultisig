use backend::*;

pub use backend::ProofError;
pub use rec_aggregation::{AggregatedXMSS, AggregationTopology, xmss_aggregate, xmss_verify_aggregation};

pub type F = KoalaBear;

/// Call once before proving. Compiles the aggregation program and precomputes DFT twiddles.
pub fn setup_prover() {
    rec_aggregation::init_aggregation_bytecode();
    precompute_dft_twiddles::<F>(1 << 24);
}

/// Call once before verifying (not needed if `setup_prover` was already called).
pub fn setup_verifier() {
    rec_aggregation::init_aggregation_bytecode();
}

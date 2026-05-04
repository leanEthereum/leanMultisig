use backend::*;

pub use backend::ProofError;
pub use rec_aggregation::{
    AggregatedXMSS, AggregationTopology, TYPE2_MAX_COMPONENTS, TypeOneInfo, TypeOneMultiSignature,
    TypeTwoMultiSignature, aggregate_type_1, merge_many_type_1, message_bytes_to_field, split_type_2, verify_type1,
    verify_type2, xmss_aggregate, xmss_verify_aggregation,
};
pub use xmss::{MESSAGE_LEN_FE, XmssPublicKey, XmssSecretKey, XmssSignature, xmss_key_gen, xmss_sign, xmss_verify};

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

/// Bump-arena allocator.
///
/// **Optional.**
///
/// To enable, set it as the `#[global_allocator]` in your binary and call
/// [`init_allocator`] once at startup. Then bracket each proving call with
/// [`begin_phase`] / [`end_phase`] and **clone the outputs after
/// [`end_phase`]** so the cloned copy lands in the system allocator before the
/// next [`begin_phase`] resets the arena slabs.
///
/// See `tests/test_zk_alloc.rs` for a runnable end-to-end example.
pub use zk_alloc::{ZkAllocator, begin_phase, end_phase, init as init_allocator};

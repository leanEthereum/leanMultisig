#![cfg_attr(not(test), allow(unused_crate_dependencies))]
pub mod benchmark;
mod bytecode_claims;
mod compilation;
mod type_1_aggregation;
mod type_2_aggregation;

use backend::{Evaluation, Proof, ProofError, RawProof};
pub use compilation::{
    MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN,
    get_aggregation_bytecode, init_aggregation_bytecode,
};
use lean_prover::verify_execution::verify_execution;
use lean_vm::{DIGEST_LEN, EF, F};
pub use type_1_aggregation::{TypeOneInfo, TypeOneMultiSignature, aggregate_type_1, verify_type_1};
pub use type_2_aggregation::{
    TypeTwoMultiSignature, merge_many_type_1, split_type_2, split_type_2_by_msg, verify_type_2,
};
use utils::poseidon_compress_slice;

#[allow(missing_debug_implementations)]
pub struct InnerVerified {
    pub input_data: Vec<F>,
    pub input_data_hash: [F; DIGEST_LEN],
    pub bytecode_evaluation: Evaluation<EF>,
    pub raw_proof: RawProof<F>,
}

pub(crate) fn verify_inner(input_data: Vec<F>, proof: Proof<F>) -> Result<InnerVerified, ProofError> {
    let input_data_hash = poseidon_compress_slice(&input_data, true);
    let bytecode = get_aggregation_bytecode();
    let (verif, raw_proof) = verify_execution(bytecode, &input_data_hash, proof)?;
    Ok(InnerVerified {
        input_data,
        input_data_hash,
        bytecode_evaluation: verif.bytecode_evaluation,
        raw_proof,
    })
}

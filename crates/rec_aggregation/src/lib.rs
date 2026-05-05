#![cfg_attr(not(test), allow(unused_crate_dependencies))]
pub mod benchmark;
mod compilation;
mod type_1_aggregation;
mod type_2_aggregation;

pub use compilation::{
    MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN,
    get_aggregation_bytecode, init_aggregation_bytecode,
};
pub use type_1_aggregation::{AggregationProof, TypeOneInfo, TypeOneMultiSignature, aggregate_type_1, verify_type_1};
pub use type_2_aggregation::{TypeTwoMultiSignature, merge_many_type_1, split_type_2, verify_type_2};

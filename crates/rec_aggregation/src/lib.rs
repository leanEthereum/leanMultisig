#![cfg_attr(not(test), allow(unused_crate_dependencies))]

pub mod recursion;
pub mod xmss_aggregate;

pub use recursion::bench_recursion;
pub use xmss_aggregate::bench_xmss;

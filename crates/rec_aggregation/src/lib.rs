#![cfg_attr(not(test), allow(unused_crate_dependencies))]

mod wrappers;
pub mod xmss_aggregate;

/*
Testing PROD_CONFIG:
````
RUSTFLAGS='-C target-cpu=native' cargo test --release --package rec_aggregation --lib -- xmss_aggregate::test_xmss_aggregate --exact --nocapture
````

Testing TEST_CONFIG:
````
RUSTFLAGS='-C target-cpu=native' cargo test --release --package rec_aggregation --lib --features test_config -- xmss_aggregate::test_xmss_aggregate --exact --nocapture
````
*/

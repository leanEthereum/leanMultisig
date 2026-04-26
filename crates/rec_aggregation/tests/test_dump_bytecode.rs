//! Compile the recursive-aggregation main bytecode and write its
//! pretty-printed disassembly to disk.
//!
//! The test is `#[ignore]` because the self-referential compilation is slow.
//! Run it explicitly with:
//!
//! ```bash
//! cargo test -p rec_aggregation --release --test test_dump_bytecode -- --ignored --nocapture
//! ```
//!
//! Output path defaults to `target/aggregation_bytecode.txt` at the workspace
//! root. Override with the `BYTECODE_DUMP_PATH` environment variable.

use std::env;
use std::path::PathBuf;

use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode};

#[test]
#[ignore]
fn dump_aggregation_bytecode() {
    init_aggregation_bytecode();
    let bytecode = get_aggregation_bytecode();
    let pretty = bytecode.pretty_print();

    let output_path = match env::var("BYTECODE_DUMP_PATH") {
        Ok(p) => PathBuf::from(p),
        Err(_) => PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../target")
            .join("aggregation_bytecode.txt"),
    };

    if let Some(parent) = output_path.parent() {
        std::fs::create_dir_all(parent).unwrap();
    }
    std::fs::write(&output_path, &pretty).unwrap();

    println!(
        "wrote {} bytes ({} instructions) to {}",
        pretty.len(),
        bytecode.size(),
        output_path.display()
    );
}

//! Compile the recursive-aggregation main bytecode and write its
//! pretty-printed disassembly to the given output path.
//!
//! Usage: cargo run --release -p rec_aggregation --example dump_pretty -- <output_path>

use std::env;
use std::path::PathBuf;

use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode};

fn main() {
    let args: Vec<String> = env::args().collect();
    let output_path = PathBuf::from(args.get(1).expect("missing output path argument"));

    init_aggregation_bytecode();
    let bytecode = get_aggregation_bytecode();
    let pretty = bytecode.pretty_print();

    if let Some(parent) = output_path.parent()
        && !parent.as_os_str().is_empty()
    {
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

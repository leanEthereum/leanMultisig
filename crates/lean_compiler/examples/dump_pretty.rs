//! Dump the pretty-printed bytecode for a given .py file.
//!
//! Usage: cargo run --release -p lean_compiler --example dump_pretty -- <path>
//!
//! For files that contain placeholders (e.g. anything in
//! `crates/rec_aggregation/`), placeholders must be expanded first; this
//! example compiles a standalone file as-is.

use std::env;

use lean_compiler::{ProgramSource, compile_program};

fn main() {
    let args: Vec<String> = env::args().collect();
    let path = args.get(1).expect("missing path argument").clone();
    let bytecode = compile_program(&ProgramSource::Filepath(path));
    println!("{}", bytecode.pretty_print());
}

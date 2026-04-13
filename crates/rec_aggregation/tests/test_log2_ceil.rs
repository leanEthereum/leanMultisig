use std::collections::BTreeMap;

use backend::*;
use lean_compiler::*;
use lean_vm::*;
use rec_aggregation::{NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN};

#[test]
fn test_log2_ceil() {
    let path = format!("{}/tests/test_log2_ceil.py", env!("CARGO_MANIFEST_DIR"));
    let replacements = BTreeMap::from([
        ("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string()),
        (
            "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
            NUM_REPEATED_ONES.to_string(),
        ),
    ]);
    let bytecode = compile_program_with_flags(&ProgramSource::Filepath(path), CompilationFlags { replacements });
    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints: Default::default(),
    };
    let run = |n: usize| {
        let expected = log2_ceil_usize(n);
        let public_input = vec![F::from_usize(n), F::from_usize(expected)];
        execute_bytecode(&bytecode, &public_input, &witness, false);
    };

    // small values (n > 2)
    for n in 3..=10 {
        run(n);
    }
    // exact powers of 2
    for exp in 2..=20 {
        run(1 << exp);
    }
    // one above a power of 2
    for exp in 2..=20 {
        run((1 << exp) + 1);
    }
    // one below a power of 2
    for exp in 3..=20 {
        run((1 << exp) - 1);
    }
    // large values
    for exp in 24..=30 {
        run(1 << exp);
    }
    for exp in 24..=29 {
        run((1 << exp) + 1);
    }
    run((1 << 30) - 1);
}

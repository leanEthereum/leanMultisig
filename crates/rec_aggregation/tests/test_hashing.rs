use backend::PrimeCharacteristicRing;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::{NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN};
use std::collections::{BTreeMap, HashMap};
use utils::poseidon_compress_slice;

#[test]
fn test_slice_hashing() {
    let path = format!("{}/tests/test_hashing.py", env!("CARGO_MANIFEST_DIR"));
    let replacements = BTreeMap::from([
        ("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string()),
        (
            "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
            NUM_REPEATED_ONES.to_string(),
        ),
    ]);
    let bytecode = compile_program_with_flags(&ProgramSource::Filepath(path), CompilationFlags { replacements });

    for len in [1, 2, 6, 7, 8, 9, 15, 16, 17, 24, 100, 1000, 12345] {
        let mut rng = StdRng::seed_from_u64(0);
        let data: Vec<F> = (0..len).map(|_| rng.random()).collect();
        let public_input = poseidon_compress_slice(&data, true).to_vec();
        let hints = HashMap::from([
            ("input_size".to_string(), vec![vec![F::from_usize(len)]]),
            ("input".to_string(), vec![data]),
        ]);
        let witness = ExecutionWitness {
            preamble_memory_len: PREAMBLE_MEMORY_LEN,
            hints,
        };
        execute_bytecode(&bytecode, &public_input, &witness, false);
    }
}

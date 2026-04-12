use backend::PrimeCharacteristicRing;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::PREAMBLE_MEMORY_LEN;
use std::collections::HashMap;
use utils::poseidon_compress_slice;

#[test]
fn test_slice_hashing() {
    let path = format!("{}/tests/test_hashing.py", env!("CARGO_MANIFEST_DIR"));
    let bytecode = compile_program(&ProgramSource::Filepath(path));

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

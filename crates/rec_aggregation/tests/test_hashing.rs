use backend::PrimeCharacteristicRing;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::PREAMBLE_MEMORY_LEN;
use utils::poseidon_compress_slice;

#[test]
fn test_slice_hashing() {
    let path = format!("{}/tests/test_hashing.py", env!("CARGO_MANIFEST_DIR"));
    let bytecode = compile_program(&ProgramSource::Filepath(path));

    for len in [1, 2, 6, 7, 8, 9, 15, 16, 17, 24, 100, 1000, 12345] {
        let mut rng = StdRng::seed_from_u64(0);
        let data: Vec<F> = (0..len).map(|_| rng.random()).collect();
        let hash = poseidon_compress_slice(&data, true);
        let public_input: Vec<F> = hash.to_vec();
        let mut private_input: Vec<F> = vec![F::from_usize(len)];
        private_input.extend(&data);
        let witness = ExecutionWitness {
            private_input: &private_input,
            preamble_memory_len: PREAMBLE_MEMORY_LEN,
            ..Default::default()
        };
        execute_bytecode(&bytecode, &public_input, &witness, false);
    }
}

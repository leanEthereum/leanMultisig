use backend::PrimeCharacteristicRing;
use lean_compiler::*;
use lean_vm::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon_compress_slice;

#[test]
fn test_slice_hashing() {
    let path = format!("{}/tests/test_hashing.py", env!("CARGO_MANIFEST_DIR"));
    let bytecode = compile_program(&ProgramSource::Filepath(path));

    for len in [1, 2, 6, 7, 8, 9, 15, 16, 17, 24, 100, 1000, 12345] {
        let mut rng = StdRng::seed_from_u64(0);
        let data: Vec<F> = (0..len).map(|_| rng.random()).collect();
        let hash = poseidon_compress_slice(&data);
        let mut public_input = vec![F::from_usize(len)];
        public_input.extend(&data);
        public_input.extend(hash);
        execute_bytecode(&bytecode, (&public_input, &[]), false, &vec![]);
    }
}

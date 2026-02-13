use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::PrimeCharacteristicRing;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon_compress_slice;

fn test_hashing_with_len(len: usize) {
    let path = format!("{}/tests/test_hashing.py", env!("CARGO_MANIFEST_DIR"));
    let mut rng = StdRng::seed_from_u64(0);
    let data: Vec<F> = (0..len).map(|_| rng.random()).collect();
    let hash = poseidon_compress_slice(&data);
    let mut public_input = vec![F::from_usize(len)];
    public_input.extend(&data);
    public_input.extend(hash);
    compile_and_run(&ProgramSource::Filepath(path), (&public_input, &[]), false);
}

#[test]
fn test_slice_hashing() {
    for len in [1, 2, 6, 7, 8, 9, 15, 16, 17, 24, 100, 1000, 12345] {
        test_hashing_with_len(len);
    }
}

use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::PrimeCharacteristicRing;
use p3_util::log2_ceil_usize;

fn test_log2_ceil_with(n: usize) {
    let path = format!("{}/tests/test_log2_ceil.py", env!("CARGO_MANIFEST_DIR"));
    let expected = log2_ceil_usize(n);
    let public_input = vec![F::from_usize(n), F::from_usize(expected)];
    compile_and_run(&ProgramSource::Filepath(path), (&public_input, &[]), false);
}

#[test]
fn test_log2_ceil() {
    // small values (n > 2)
    for n in 3..=10 {
        test_log2_ceil_with(n);
    }
    // exact powers of 2
    for exp in 2..=20 {
        test_log2_ceil_with(1 << exp);
    }
    // one above a power of 2
    for exp in 2..=20 {
        test_log2_ceil_with((1 << exp) + 1);
    }
    // one below a power of 2
    for exp in 3..=20 {
        test_log2_ceil_with((1 << exp) - 1);
    }
    // large values
    for exp in 24..=28 {
        test_log2_ceil_with(1 << exp);
    }
    for exp in 24..=27 {
        test_log2_ceil_with((1 << exp) + 1);
    }
    test_log2_ceil_with((1 << 28) - 1);
}

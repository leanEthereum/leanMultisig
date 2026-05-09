//! Sanity test for the barycentric Reed-Solomon parity check implemented in
//! `zkdsl_implem/barycentric.py`. We feed a known-good codeword along with the
//! externally computed value `M * P(r)` as public input, then execute the
//! bytecode. If `barycentric_slices` is incorrect, at least one of the two
//! length-M dot products produces a value that disagrees with the public
//! `expected` and execution fails.

use std::collections::BTreeMap;

use backend::{BasedVectorSpace, PrimeCharacteristicRing, TwoAdicField};
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_vm::{EF, ExecutionWitness, F, execute_bytecode};
use rand::{RngExt, SeedableRng, rngs::StdRng};

const TEST_LOG_M: usize = 4;

fn ntt(a: &mut [F]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros() as usize;

    let shift = usize::BITS as usize - log_n;
    for i in 0..n {
        let j = i.reverse_bits() >> shift;
        if i < j {
            a.swap(i, j);
        }
    }

    let mut size = 2;
    while size <= n {
        let half = size / 2;
        let root = F::two_adic_generator(size.trailing_zeros() as usize);
        for chunk_start in (0..n).step_by(size) {
            let mut twiddle = F::ONE;
            for i in 0..half {
                let u = a[chunk_start + i];
                let v = a[chunk_start + i + half] * twiddle;
                a[chunk_start + i] = u + v;
                a[chunk_start + i + half] = u - v;
                twiddle *= root;
            }
        }
        size *= 2;
    }
}

fn rs_encode(message: &[F]) -> Vec<F> {
    let m = message.len();
    let mut codeword = vec![F::ZERO; 2 * m];
    codeword[..m].copy_from_slice(message);
    ntt(&mut codeword);
    codeword
}

fn build_public_input(seed: u64, log_m: usize) -> Vec<F> {
    let m = 1 << log_m;
    let mut rng = StdRng::seed_from_u64(seed);

    let poly: Vec<F> = (0..m).map(|_| rng.random()).collect();
    let codeword = rs_encode(&poly);
    let r: EF = rng.random();

    // Horner evaluation P(r), then scale by M to match the barycentric form
    // used by the zkDSL (which drops the 1/M factor on both sides).
    let p_r: EF = poly.iter().rev().fold(EF::ZERO, |acc, &c| acc * r + EF::from(c));
    let expected = p_r * EF::from(F::from_u64(m as u64));

    let mut input = Vec::with_capacity(2 * m + 2 * <EF as BasedVectorSpace<F>>::DIMENSION);
    input.extend((0..m).map(|j| codeword[2 * j]));
    input.extend((0..m).map(|j| codeword[2 * j + 1]));
    input.extend(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&r));
    input.extend(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&expected));
    input
}

fn build_corrupted_input(seed: u64, log_m: usize) -> Vec<F> {
    let mut input = build_public_input(seed, log_m);
    input[3] += F::ONE;
    input
}

#[test]
fn test_barycentric_zkdsl_accepts_valid_codeword() {
    let path = format!("{}/tests/test_barycentric.py", env!("CARGO_MANIFEST_DIR"));
    let replacements = BTreeMap::from([("LOG_M_PLACEHOLDER".to_string(), TEST_LOG_M.to_string())]);
    let bytecode = compile_program_with_flags(&ProgramSource::Filepath(path), CompilationFlags { replacements });
    let witness = ExecutionWitness::default();
    for seed in 0..5 {
        let public_input = build_public_input(seed, TEST_LOG_M);
        execute_bytecode(&bytecode, &public_input, &witness, false);
    }
}

#[test]
#[should_panic]
fn test_barycentric_zkdsl_rejects_corrupted_codeword() {
    // Sanity check that the parity check actually catches a malformed
    // codeword: corrupting a single field element must trigger a constraint
    // failure during execution.
    let path = format!("{}/tests/test_barycentric.py", env!("CARGO_MANIFEST_DIR"));
    let replacements = BTreeMap::from([("LOG_M_PLACEHOLDER".to_string(), TEST_LOG_M.to_string())]);
    let bytecode = compile_program_with_flags(&ProgramSource::Filepath(path), CompilationFlags { replacements });
    let witness = ExecutionWitness::default();
    let public_input = build_corrupted_input(0, TEST_LOG_M);
    execute_bytecode(&bytecode, &public_input, &witness, false);
}

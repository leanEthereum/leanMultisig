#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use std::collections::{BTreeMap, HashMap};

use backend::{PrimeCharacteristicRing, Proof, TwoAdicField};
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    default_whir_config,
    prove_execution::{ExecutionProof, prove_execution},
    verify_execution::verify_execution,
};
use lean_vm::{Bytecode, ExecutionWitness, F};
use rand::{RngExt, SeedableRng, rngs::StdRng};

static EMBEDDED_ZK_DSL: include_dir::Dir<'_> = include_dir::include_dir!("$CARGO_MANIFEST_DIR/zkdsl_implem");

const STARTING_LOG_INV_RATE: usize = 1;

pub const LOG_M: usize = 6;

pub fn compile_lean_da_bytecode() -> Bytecode {
    let mut replacements = BTreeMap::new();
    replacements.insert("LOG_M_PLACEHOLDER".to_string(), LOG_M.to_string());
    let source = ProgramSource::Embedded {
        entry: "lean_da.py".to_string(),
        dir: &EMBEDDED_ZK_DSL,
    };
    compile_program_with_flags(&source, CompilationFlags { replacements })
}

/// In-place radix-2 Cooley-Tukey NTT.
/// On input `a` of length `n = 2^k`, computes `A[j] = sum_i a[i] * w_n^{i*j}`
/// where `w_n` is the canonical 2^k-th root of unity.
fn ntt(a: &mut [F]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros() as usize;

    // Bit-reverse permutation.
    let shift = usize::BITS as usize - log_n;
    for i in 0..n {
        let j = i.reverse_bits() >> shift;
        if i < j {
            a.swap(i, j);
        }
    }

    // Butterfly layers.
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

/// Encode a length-`m` message into a length-`2m` Reed-Solomon codeword (rate 1/2):
/// the message coefficients define a degree-<m polynomial, evaluated at the 2m-th
/// roots of unity via a single length-2m NTT (the message is zero-padded to 2m).
fn rs_encode(message: &[F]) -> Vec<F> {
    let m = message.len();
    assert!(m.is_power_of_two());
    let mut codeword = vec![F::ZERO; 2 * m];
    codeword[..m].copy_from_slice(message);
    ntt(&mut codeword);
    codeword
}

fn build_witness() -> ExecutionWitness {
    let m = 1 << LOG_M;
    let mut rng = StdRng::seed_from_u64(0);
    let message: Vec<F> = (0..m).map(|_| rng.random()).collect();
    let codeword = rs_encode(&message);

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert("codeword".to_string(), vec![codeword]);
    ExecutionWitness {
        preamble_memory_len: 0,
        hints,
    }
}

pub fn prove_lean_da(bytecode: &Bytecode, public_input: &[F]) -> ExecutionProof {
    let witness = build_witness();
    prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(STARTING_LOG_INV_RATE),
        false,
    )
    .unwrap()
}

pub fn verify_lean_da(bytecode: &Bytecode, public_input: &[F], proof: Proof<F>) {
    verify_execution(bytecode, public_input, proof).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_prove_verify() {
        let bytecode = compile_lean_da_bytecode();
        let public_input: Vec<F> = vec![];
        let proof = prove_lean_da(&bytecode, &public_input);
        verify_lean_da(&bytecode, &public_input, proof.proof);
    }

    #[test]
    fn test_rs_encode_matches_naive() {
        let mut rng = StdRng::seed_from_u64(7);
        let m: usize = 1 << LOG_M;
        let message: Vec<F> = (0..m).map(|_| rng.random()).collect();
        let two_m = 2 * m;
        let w = F::two_adic_generator(two_m.trailing_zeros() as usize);
        let naive: Vec<F> = (0..two_m)
            .map(|j| {
                let wj = w.exp_u64(j as u64);
                message.iter().rev().fold(F::ZERO, |acc, &c| acc * wj + c)
            })
            .collect();
        assert_eq!(rs_encode(&message), naive);
    }
}

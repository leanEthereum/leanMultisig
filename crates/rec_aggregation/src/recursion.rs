use std::time::Instant;

use lean_compiler::{ProgramSource, compile_program};
use lean_prover::default_whir_config;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use multilinear_toolkit::prelude::*;

use crate::compilation::get_recursion_bytecode_helper;

pub fn run_recursion_benchmark(count: usize, log_inv_rate: usize, prox_gaps_conjecture: bool, tracing: bool) {
    let program_to_prove = r#"
DIM = 5
POSEIDON_OF_ZERO = POSEIDON_OF_ZERO_PLACEHOLDER
# Dot product precompile:
BE = 1  # base-extension
EE = 0  # extension-extension

def main():
    for i in range(0, 1000):
        null_ptr = ZERO_VEC_PTR  # pointer to zero vector
        poseidon_of_zero = POSEIDON_OF_ZERO
        poseidon16(null_ptr, null_ptr, poseidon_of_zero)
        a = Array(DIM)
        b = Array(DIM)
        after_null_ptr = 16
        dot_product(after_null_ptr, after_null_ptr, a, 3, BE)
        dot_product(after_null_ptr, after_null_ptr, b, 2, EE)
        x: Mut = 0
        n = 10
        for j in range(0, n):
            x += j
        assert x == n * (n - 1) / 2
    n = 100000
    x = 0
    sum: Mut = x[0]
    for i in unroll(0, n):
        sum += i
    assert sum == n * (n - 1) / 2
    return
"#
    .replace("POSEIDON_OF_ZERO_PLACEHOLDER", &POSEIDON_16_NULL_HASH_PTR.to_string());
    run_recursion_benchmark_with_program(count, log_inv_rate, prox_gaps_conjecture, tracing, &program_to_prove);
}

#[test]
fn test_end2end_recursion_poseidon_heavy() {
    // Poseidon table larger than dot_product table (reversed ordering)
    let program_to_prove = r#"
DIM = 5
POSEIDON_OF_ZERO = POSEIDON_OF_ZERO_PLACEHOLDER
BE = 1

def main():
    for i in range(0, 1000):
        null_ptr = ZERO_VEC_PTR
        poseidon_of_zero = POSEIDON_OF_ZERO
        poseidon16(null_ptr, null_ptr, poseidon_of_zero)
        poseidon16(null_ptr, null_ptr, poseidon_of_zero)
        poseidon16(null_ptr, null_ptr, poseidon_of_zero)
    dot_product(ZERO_VEC_PTR, ZERO_VEC_PTR, ZERO_VEC_PTR, 2, BE)
    return
"#
    .replace("POSEIDON_OF_ZERO_PLACEHOLDER", &POSEIDON_16_NULL_HASH_PTR.to_string());
    run_recursion_benchmark_with_program(1, 2, false, false, &program_to_prove);
}

fn run_recursion_benchmark_with_program(
    count: usize,
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
    tracing: bool,
    inner_program: &str,
) {
    let whir_config = default_whir_config(log_inv_rate, prox_gaps_conjecture);
    let inner_bytecode = compile_program(&ProgramSource::Raw(inner_program.to_string()));
    precompute_dft_twiddles::<F>(1 << 24);
    let inner_public_input = vec![];
    let inner_private_input = vec![];
    let proof_to_prove = prove_execution(
        &inner_bytecode,
        (&inner_public_input, &inner_private_input),
        &vec![],
        &whir_config,
        false,
    );
    let verif_details = verify_execution(
        &inner_bytecode,
        &inner_public_input,
        proof_to_prove.proof.clone(),
        whir_config.clone(),
    )
    .unwrap();

    let mut outer_public_input = vec![F::from_usize(verif_details.bytecode_evaluation.point.num_variables())];
    outer_public_input.extend(
        verif_details
            .bytecode_evaluation
            .point
            .0
            .iter()
            .flat_map(|c| c.as_basis_coefficients_slice()),
    );
    outer_public_input.extend(verif_details.bytecode_evaluation.value.as_basis_coefficients_slice());
    let inner_public_memory = build_public_memory(&inner_public_input);
    let mut outer_private_input = vec![
        F::from_usize(proof_to_prove.proof.len()),
        F::from_usize(log2_strict_usize(inner_public_memory.len())),
        F::from_usize(count),
    ];
    outer_private_input.extend(inner_public_memory);
    for _ in 0..count {
        outer_private_input.extend(proof_to_prove.proof.to_vec());
    }

    let recursion_bytecode = get_recursion_bytecode_helper(prox_gaps_conjecture, inner_bytecode.log_size());

    if tracing {
        utils::init_tracing();
    }
    let time = Instant::now();

    let recursion_proof = prove_execution(
        &recursion_bytecode,
        (&outer_public_input, &outer_private_input),
        &vec![], // TODO precompute poseidons
        &default_whir_config(log_inv_rate, prox_gaps_conjecture),
        false,
    );
    let proving_time = time.elapsed();
    verify_execution(
        &recursion_bytecode,
        &outer_public_input,
        recursion_proof.proof,
        default_whir_config(log_inv_rate, prox_gaps_conjecture),
    )
    .unwrap();
    println!(
        "(Outer proof: 2**{} memory, 2**{} cycles, 2**{} dot_product_rows, 2**{} poseidons)",
        verif_details.log_memory,
        verif_details.table_n_vars[&Table::execution()],
        verif_details.table_n_vars[&Table::dot_product()],
        verif_details.table_n_vars[&Table::poseidon16()],
    );
    println!("{}", recursion_proof.exec_summary);
    println!(
        "{}->1 recursion proving time: {} ms (1->1: {} ms), proof size: {} KiB",
        count,
        proving_time.as_millis(),
        proving_time.as_millis() / count as u128,
        recursion_proof.proof_size_fe * F::bits() / (8 * 1024)
    );
}

#[test]
fn test_end2end_recursion() {
    run_recursion_benchmark(1, 2, false, false);
}

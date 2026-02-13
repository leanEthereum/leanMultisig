use std::time::Instant;

use lean_compiler::{ProgramSource, compile_program};
use lean_prover::default_whir_config;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use utils::{build_prover_state, poseidon_compress_slice, poseidon16_compress_pair};

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

/// Extract bytecode claim (point, value) from a public input that starts with the claim.
fn extract_bytecode_claim_from_public_input(
    public_input: &[F],
    bytecode_point_n_vars: usize,
) -> (MultilinearPoint<EF>, EF) {
    let claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let packed = pack_scalars_to_extension(&public_input[..claim_size]);
    let point = MultilinearPoint(packed[..bytecode_point_n_vars].to_vec());
    let value = packed[bytecode_point_n_vars];
    (point, value)
}

/// Hash all bytecode claims into a single digest
fn hash_bytecode_claims(claims: &[(MultilinearPoint<EF>, EF)]) -> [F; DIGEST_LEN] {
    let mut running_hash = [F::ZERO; DIGEST_LEN];
    for (point, value) in claims {
        let mut ef_data: Vec<EF> = point.0.clone();
        ef_data.push(*value);
        let mut data = flatten_scalars_to_base::<F, EF>(&ef_data);
        data.resize(data.len().next_multiple_of(DIGEST_LEN), F::ZERO);

        let claim_hash = poseidon_compress_slice(&data);
        running_hash = poseidon16_compress_pair(running_hash, claim_hash);
    }
    running_hash
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

    let bytecode_point_n_vars = inner_bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    // Inner public input: bytecode claim = (zero_point, bytecode(0)), padded to multiple of DIGEST_LEN.
    let bytecode_claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);
    let mut inner_public_input = vec![F::ZERO; bytecode_claim_size_padded];
    inner_public_input[bytecode_point_n_vars * DIMENSION] = inner_bytecode.instructions_multilinear[0];

    let inner_private_input = vec![];
    let inner_proof = prove_execution(
        &inner_bytecode,
        (&inner_public_input, &inner_private_input),
        &vec![],
        &whir_config,
        false,
    );

    let verif_details = verify_execution(
        &inner_bytecode,
        &inner_public_input,
        inner_proof.proof.clone(),
        whir_config.clone(),
    )
    .unwrap();

    let recursion_bytecode = get_recursion_bytecode_helper(
        prox_gaps_conjecture,
        inner_bytecode.log_size(),
        inner_bytecode.instructions_multilinear[0],
    );

    if tracing {
        utils::init_tracing();
    }
    let time = Instant::now();

    // Collect 2*num_recursions bytecode claims
    let mut claims = vec![];
    for _ in 0..count {
        // from inner proof's public input
        let first_claim = extract_bytecode_claim_from_public_input(&inner_public_input, bytecode_point_n_vars);
        claims.push(first_claim);

        // from verify_execution
        let second = &verif_details.bytecode_evaluation;
        claims.push((second.point.clone(), second.value));
    }

    // Sumcheck reduction: 2n claims -> 1
    let (bytecode_claim_output, final_sumcheck_transcript) = if count > 0 {
        let claims_hash = hash_bytecode_claims(&claims);

        let mut reduction_prover = build_prover_state();
        reduction_prover.add_base_scalars(&claims_hash);
        let alpha: EF = reduction_prover.sample();

        let n_claims = claims.len();
        let alpha_powers: Vec<EF> = alpha.powers().take(n_claims).collect();

        // Build weights: w(x) = sum_i alpha^i * eq(x, point_i)
        let weights_packed = claims
            .par_iter()
            .zip(&alpha_powers)
            .map(|((point_i, _), &alpha_i)| eval_eq_packed_scaled(&point_i.0, alpha_i))
            .reduce_with(|mut acc, eq_i| {
                acc.par_iter_mut().zip(&eq_i).for_each(|(w, e)| *w += *e);
                acc
            })
            .unwrap();

        let claimed_sum: EF = dot_product(claims.iter().map(|(_, v)| *v), alpha_powers.iter().copied());

        let witness = MleGroupOwned::ExtensionPacked(vec![
            inner_bytecode.instructions_multilinear_packed.clone(),
            weights_packed,
        ]);

        let (challenges, final_evals, _) = sumcheck_prove::<EF, _, _>(
            1,
            witness,
            None,
            &ProductComputation {},
            &vec![],
            None,
            false,
            &mut reduction_prover,
            claimed_sum,
            false,
        );

        let reduced_point = challenges;
        let reduced_value = final_evals[0]; // bytecode polynomial evaluated at `reduced_point`

        let mut ef_claim: Vec<EF> = reduced_point.0;
        ef_claim.push(reduced_value);
        let claim_output = flatten_scalars_to_base::<F, EF>(&ef_claim);
        assert_eq!(claim_output.len(), bytecode_claim_size);

        (claim_output, reduction_prover.raw_proof())
    } else {
        // n_recursions=0: output ((0,0,...,0), bytecode((0,0,...,0)))
        let mut claim_output = vec![F::ZERO; bytecode_claim_size];
        claim_output[bytecode_point_n_vars * DIMENSION] = inner_bytecode.instructions_multilinear[0];
        (claim_output, vec![])
    };

    // Outer public input: the reduced bytecode claim
    let outer_public_input = bytecode_claim_output;

    // Outer private input
    let inner_public_memory = build_public_memory(&inner_public_input);
    let mut outer_private_input = vec![
        F::from_usize(log2_strict_usize(inner_public_memory.len())),
        F::from_usize(count),
    ];
    // For each recursion: proof_size + inner_public_memory + bytecode_value_hint (DIM) + proof transcript
    for _ in 0..count {
        outer_private_input.push(F::from_usize(inner_proof.proof.len()));
        outer_private_input.extend(&inner_public_memory);
        outer_private_input.extend(verif_details.bytecode_evaluation.value.as_basis_coefficients_slice());
        outer_private_input.extend(inner_proof.proof.to_vec());
    }
    // Sumcheck transcript for bytecode 2n->1 reduction
    outer_private_input.extend(&final_sumcheck_transcript);

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

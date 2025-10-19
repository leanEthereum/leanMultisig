use std::time::Instant;

use air::examples::prove_poseidon2::{Poseidon2Config, prove_poseidon2};
use lean_compiler::*;
use lean_prover::{
    prove_execution::prove_execution, verify_execution::verify_execution, whir_config_builder,
};
use lean_vm::{F, execute_bytecode};
use p3_field::PrimeCharacteristicRing;
use whir_p3::{FoldingFactor, SecurityAssumption};
use xmss::iterate_hash;

#[test]
fn benchmark_poseidon_chain() {
    let program_str = r#"
    
    const LOG_CHAIN_LENGTH = LOG_CHAIN_LENGTH_PLACEHOLDER;
    const CHAIN_LENGTH = 2 ** LOG_CHAIN_LENGTH;
    const COMPRESSION = 1;
    const UNROLLED_STEPS = 2**7;

    fn main() {

        // current implem panics if some precompiles are not used... (TODO)
        poseidon_24_null_hash_ptr = 5;
        zero = 0;
        for i in 0..2**9 {
            poseidon24(0, 0, poseidon_24_null_hash_ptr);
            dot_product(0, 0, zero, 1);
        }

        buff = malloc_vec(CHAIN_LENGTH + 1);
        poseidon16(0, 0, buff, COMPRESSION);
        
        for i in 0..CHAIN_LENGTH / UNROLLED_STEPS {
            offset = buff + i * UNROLLED_STEPS;
            for j in 0..UNROLLED_STEPS unroll {
                poseidon16(offset + j, 0, offset + (j + 1), COMPRESSION);
            }
        }

        buff_ptr = (buff + (CHAIN_LENGTH-1)) * 8;
        public_input = public_input_start;
        for i in 0..8 {
            assert buff_ptr[i] == public_input[i];
        }

        return;
    }
   "#
    .to_string();

    const LOG_CHAIN_LENGTH: usize = 17;
    const CHAIN_LENGTH: usize = 1 << LOG_CHAIN_LENGTH;

    let program_str = program_str.replace(
        "LOG_CHAIN_LENGTH_PLACEHOLDER",
        &LOG_CHAIN_LENGTH.to_string(),
    );

    let mut public_input = F::zero_vec(1 << 13);
    public_input[0..8].copy_from_slice(&iterate_hash(&Default::default(), CHAIN_LENGTH));

    let private_input = vec![];

    utils::init_tracing();
    let (bytecode, function_locations) = compile_program(&program_str);
    let no_vec_runtime_memory = execute_bytecode(
        &bytecode,
        &public_input,
        &private_input,
        &program_str,
        &function_locations,
        1 << (3 + LOG_CHAIN_LENGTH),
        (false, true),
    )
    .no_vec_runtime_memory;

    let time = Instant::now();
    let proof_data = prove_execution(
        &bytecode,
        &program_str,
        &function_locations,
        (&public_input, &private_input),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
    )
    .0;
    let vm_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();

    let raw_proof = prove_poseidon2(&Poseidon2Config {
        log_n_poseidons_16: LOG_CHAIN_LENGTH,
        log_n_poseidons_24: 10, // (almost invisible cost)
        univariate_skips: 4,
        folding_factor: FoldingFactor::new(7, 4),
        log_inv_rate: 1,
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        security_level: 128,
        rs_domain_initial_reduction_factor: 5,
        max_num_variables_to_send_coeffs: 7,
        display_logs: true,
    });

    println!("VM proof time: {:?}", vm_time);
    println!("Raw Poseidon proof time: {:?}", raw_proof.prover_time);

    println!(
        "VM overhead: {:.2}x",
        vm_time.as_secs_f64() / raw_proof.prover_time.as_secs_f64()
    );
}

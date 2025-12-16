use std::path::Path;
use std::time::Instant;

use lean_compiler::compile_program;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{FIBONNACI_PROGRAM, SnarkParams, whir_config_builder};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use whir_p3::{WhirConfig, precompute_dft_twiddles};

const FIBONACCI_N: usize = 10_000;

pub fn run_end2end_recursion_benchmark() {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("full_recursion.snark");
    let mut program_str = std::fs::read_to_string(src_file).unwrap();
    let snark_params = SnarkParams {
        first_whir: whir_config_builder(1, 3, 1),
        second_whir: whir_config_builder(3, 4, 1),
    };

    let bytecode_to_prove = compile_program(FIBONNACI_PROGRAM.replace("FIB_N_PLACEHOLDER", &FIBONACCI_N.to_string()));
    precompute_dft_twiddles::<F>(1 << 24);
    let proof_to_prove = prove_execution(&bytecode_to_prove, (&[], &[]), &vec![], &snark_params, false);
    verify_execution(&bytecode_to_prove, &[], proof_to_prove.proof.clone(), &snark_params).unwrap();

    let first_whir_config = WhirConfig::<F>::new(&snark_params.first_whir, proof_to_prove.first_whir_n_vars);

    program_str = program_str.replace(
        &format!("NUM_OOD_COMMIT_PLACEHOLDER"),
        &first_whir_config.committment_ood_samples.to_string(),
    );
    for (i, round) in first_whir_config.round_parameters.iter().enumerate() {
        program_str = program_str
            .replace(&format!("NUM_QUERIES_{i}_PLACEHOLDER"), &round.num_queries.to_string())
            .replace(&format!("NUM_OOD_{}_PLACEHOLDER", i), &round.ood_samples.to_string())
            .replace(&format!("GRINDING_BITS_{i}_PLACEHOLDER"), &round.pow_bits.to_string());
    }
    program_str = program_str
        .replace(
            &format!("NUM_QUERIES_{}_PLACEHOLDER", first_whir_config.n_rounds()),
            &first_whir_config.final_queries.to_string(),
        )
        .replace(
            &format!("GRINDING_BITS_{}_PLACEHOLDER", first_whir_config.n_rounds()),
            &first_whir_config.final_pow_bits.to_string(),
        )
        .replace("N_VARS_PLACEHOLDER", &first_whir_config.num_variables.to_string())
        .replace(
            "LOG_INV_RATE_PLACEHOLDER",
            &snark_params.first_whir.starting_log_inv_rate.to_string(),
        );
    assert_eq!(first_whir_config.n_rounds(), 3); // this is hardcoded in the program above
    for round in 0..=first_whir_config.n_rounds() {
        program_str = program_str.replace(
            &format!("FOLDING_FACTOR_{round}_PLACEHOLDER"),
            &snark_params.first_whir.folding_factor.at_round(round).to_string(),
        );
    }
    program_str = program_str.replace(
        "RS_REDUCTION_FACTOR_0_PLACEHOLDER",
        &snark_params.first_whir.rs_domain_initial_reduction_factor.to_string(),
    );

    let public_input = proof_to_prove.proof;

    let recursion_bytecode = compile_program(program_str);

    let time = Instant::now();

    let recursion_proof = prove_execution(
        &recursion_bytecode,
        (&public_input, &[]),
        &vec![], // TODO precompute poseidons
        &Default::default(),
        false,
    );
    let proving_time = time.elapsed();
    verify_execution(
        &recursion_bytecode,
        &public_input,
        recursion_proof.proof,
        &Default::default(),
    )
    .unwrap();

    println!("{}", recursion_proof.exec_summary);
    println!(
        "Recursion proving time: {} ms, proof size: {} KiB (not optimized)",
        proving_time.as_millis(),
        recursion_proof.proof_size_fe * F::bits() / (8 * 1024)
    );
}

#[test]
fn test_end2end_recursion() {
    run_end2end_recursion_benchmark();
}

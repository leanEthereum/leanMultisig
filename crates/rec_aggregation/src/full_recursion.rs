use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{FIBONNACI_PROGRAM, SnarkParams, whir_config_builder};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use whir_p3::{WhirConfig, precompute_dft_twiddles};

const FIBONACCI_N: usize = 10_000;

pub fn run_end2end_recursion_benchmark() {
    let filepath = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("full_recursion.snark")
        .to_str()
        .unwrap()
        .to_string();

    let snark_params = SnarkParams {
        first_whir: whir_config_builder(1, 3, 1),
        second_whir: whir_config_builder(3, 4, 1),
    };
    let bytecode_to_prove = compile_program_with_flags(
        &ProgramSource::Raw(FIBONNACI_PROGRAM.to_string()),
        CompilationFlags {
            replacements: vec![("FIB_N_PLACEHOLDER".to_string(), FIBONACCI_N.to_string())]
                .into_iter()
                .collect(),
        },
    );
    precompute_dft_twiddles::<F>(1 << 24);
    let proof_to_prove = prove_execution(&bytecode_to_prove, (&[], &[]), &vec![], &snark_params, false);
    let verif_details = verify_execution(&bytecode_to_prove, &[], proof_to_prove.proof.clone(), &snark_params).unwrap();

    let first_whir_config = WhirConfig::<EF>::new(&snark_params.first_whir, proof_to_prove.first_whir_n_vars);

    let mut replacements = BTreeMap::new();
    replacements.insert(
        "NUM_OOD_COMMIT_PLACEHOLDER".to_string(),
        first_whir_config.committment_ood_samples.to_string(),
    );
    for (i, round) in first_whir_config.round_parameters.iter().enumerate() {
        replacements.insert(
            format!("NUM_QUERIES_{i}_PLACEHOLDER", i = i),
            round.num_queries.to_string(),
        );
        replacements.insert(format!("NUM_OOD_{}_PLACEHOLDER", i), round.ood_samples.to_string());
        replacements.insert(
            format!("GRINDING_BITS_{i}_PLACEHOLDER", i = i),
            round.pow_bits.to_string(),
        );
    }
    replacements.insert(
        format!("NUM_QUERIES_{}_PLACEHOLDER", first_whir_config.n_rounds()),
        first_whir_config.final_queries.to_string(),
    );
    replacements.insert(
        format!("GRINDING_BITS_{}_PLACEHOLDER", first_whir_config.n_rounds()),
        first_whir_config.final_pow_bits.to_string(),
    );
    replacements.insert(
        "N_VARS_PLACEHOLDER".to_string(),
        first_whir_config.num_variables.to_string(),
    );
    replacements.insert(
        "LOG_INV_RATE_PLACEHOLDER".to_string(),
        snark_params.first_whir.starting_log_inv_rate.to_string(),
    );
    for round in 0..=first_whir_config.n_rounds() {
        replacements.insert(
            format!("FOLDING_FACTOR_{round}_PLACEHOLDER"),
            first_whir_config.folding_factor.at_round(round).to_string(),
        );
    }
    replacements.insert(
        "RS_REDUCTION_FACTOR_0_PLACEHOLDER".to_string(),
        snark_params.first_whir.rs_domain_initial_reduction_factor.to_string(),
    );

    assert!(
        verif_details.log_memory >= verif_details.table_log_n_vars[&Table::execution()]
            && verif_details
                .table_log_n_vars
                .values()
                .collect::<Vec<_>>()
                .windows(2)
                .all(|w| w[0] >= w[1]),
        "TODO a more general recursion program",
    );
    assert_eq!(
        verif_details.table_log_n_vars.keys().copied().collect::<Vec<_>>(),
        vec![Table::execution(), Table::dot_product(), Table::poseidon16()]
    );

    // VM recursion parameters (different from WHIR)
    replacements.insert(
        "N_VARS_FIRST_GKR_PLACEHOLDER".to_string(),
        verif_details.first_quotient_gkr_n_vars.to_string(),
    );
    replacements.insert("N_TABLES_PLACEHOLDER".to_string(), N_TABLES.to_string());
    replacements.insert(
        "MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        MIN_LOG_N_ROWS_PER_TABLE.to_string(),
    );
    replacements.insert(
        "MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        MAX_LOG_N_ROWS_PER_TABLE.to_string(),
    );
    replacements.insert(
        "MIN_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MIN_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MAX_LOG_MEMORY_SIZE.to_string(),
    );

    let public_input = vec![];
    let private_input = proof_to_prove.proof;

    let recursion_bytecode =
        compile_program_with_flags(&ProgramSource::Filepath(filepath), CompilationFlags { replacements });

    let time = Instant::now();

    let recursion_proof = prove_execution(
        &recursion_bytecode,
        (&public_input, &private_input),
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

use std::path::Path;
use std::time::Instant;

use lean_compiler::{CompilationFlags, ProgramSource, compile_program, compile_program_with_flags};
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{STARTING_LOG_INV_RATE_BASE, STARTING_LOG_INV_RATE_EXTENSION, SnarkParams, whir_config_builder};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use utils::MEMORY_TABLE_INDEX;
use whir_p3::{WhirConfig, precompute_dft_twiddles};

use crate::whir_recursion::whir_recursion_placeholder_replacements;

pub fn run_end2end_recursion_benchmark() {
    let filepath = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("full_recursion.snark")
        .to_str()
        .unwrap()
        .to_string();

    let snark_params = SnarkParams {
        first_whir: whir_config_builder(STARTING_LOG_INV_RATE_BASE, 3, 1),
        second_whir: whir_config_builder(STARTING_LOG_INV_RATE_EXTENSION, 4, 1),
    };
    let program_to_prove = r#"
    const DIM = 5;
    const COMPRESSION = 1;
    const PERMUTATION = 0;
    const POSEIDON_OF_ZERO = POSEIDON_OF_ZERO_PLACEHOLDER;    
    // Dot product precompile:
    const BE = 1; // base-extension
    const EE = 0; // extension-extension

    fn main() {
        for i in 0..1 {
            null_ptr = pointer_to_zero_vector; // pointer to zero vector
            poseidon_of_zero = POSEIDON_OF_ZERO;
            poseidon16(null_ptr, null_ptr, poseidon_of_zero, PERMUTATION);
            poseidon16(null_ptr, null_ptr, poseidon_of_zero, COMPRESSION);
            dot_product(null_ptr, null_ptr, null_ptr, 2, BE);
            dot_product(null_ptr, null_ptr, null_ptr, 2, EE);
        }
        return;
    }
   "#
    .replace("POSEIDON_OF_ZERO_PLACEHOLDER", &POSEIDON_16_NULL_HASH_PTR.to_string());
    let bytecode_to_prove = compile_program(&ProgramSource::Raw(program_to_prove.to_string()));
    precompute_dft_twiddles::<F>(1 << 24);
    let proof_to_prove = prove_execution(&bytecode_to_prove, (&[], &[]), &vec![], &snark_params, false);
    let verif_details = verify_execution(&bytecode_to_prove, &[], proof_to_prove.proof.clone(), &snark_params).unwrap();

    let first_whir_config = WhirConfig::<EF>::new(&snark_params.first_whir, proof_to_prove.first_whir_n_vars);

    let mut replacements = whir_recursion_placeholder_replacements(&first_whir_config);

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
    replacements.insert("MAX_BUS_WIDTH_PLACEHOLDER".to_string(), max_bus_width().to_string());
    replacements.insert(
        "MEMORY_TABLE_INDEX_PLACEHOLDER".to_string(),
        MEMORY_TABLE_INDEX.to_string(),
    );
    replacements.insert("UNIVARIATE_SKIPS_PLACEHOLDER".to_string(), UNIVARIATE_SKIPS.to_string());
    let mut lookup_f_indexes_str = vec![];
    let mut lookup_f_values_str = vec![];
    for table in ALL_TABLES {
        let indexes_str = table
            .lookups_f()
            .iter()
            .map(|lookup_f| lookup_f.index.to_string())
            .collect::<Vec<_>>();
        lookup_f_indexes_str.push(format!("[{}]", indexes_str.join(", ")));
        let values_str = table
            .lookups_f()
            .iter()
            .map(|lookup_f| {
                format!(
                    "[{}]",
                    lookup_f
                        .values
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect::<Vec<_>>();
        lookup_f_values_str.push(format!("[{}]", values_str.join(", ")));
    }
    replacements.insert(
        "LOOKUPS_F_INDEXES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_f_indexes_str.join(", ")),
    );
    replacements.insert(
        "LOOKUPS_F_VALUES_PLACEHOLDER".to_string(),
        dbg!(format!("[{}]", lookup_f_values_str.join(", "))),
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

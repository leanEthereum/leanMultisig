use backend::*;
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    GRINDING_BITS, MAX_NUM_VARIABLES_TO_SEND_COEFFS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, WHIR_INITIAL_FOLDING_FACTOR,
    WHIR_SUBSEQUENT_FOLDING_FACTOR, default_whir_config,
};
use lean_vm::*;
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::OnceLock;
use sub_protocols::{min_stacked_n_vars, total_whir_statements};
use tracing::instrument;
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, RANDOMNESS_LEN_FE, TARGET_SUM, V, V_GRINDING, W};

use crate::{MERKLE_LEVELS_PER_CHUNK_FOR_SLOT, N_MERKLE_CHUNKS_FOR_SLOT};

static BYTECODE: OnceLock<Bytecode> = OnceLock::new();

pub fn get_aggregation_bytecode() -> &'static Bytecode {
    BYTECODE
        .get()
        .unwrap_or_else(|| panic!("call init_aggregation_bytecode() first"))
}

pub fn init_aggregation_bytecode() {
    BYTECODE.get_or_init(compile_main_program_self_referential);
}

fn compile_main_program(inner_program_log_size: usize, bytecode_zero_eval: F) -> Bytecode {
    let bytecode_point_n_vars = inner_program_log_size + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let claim_data_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let claim_data_size_padded = claim_data_size.next_multiple_of(DIGEST_LEN);
    // pub_input layout: n_sigs(1) + slice_hash(8) + slot_low(1) + slot_high(1)
    //                   + message + merkle_chunks_for_slot + bytecode_claim_padded + bytecode_hash(8)
    let pub_input_size =
        1 + DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + claim_data_size_padded + DIGEST_LEN;
    let inner_public_memory_log_size = log2_ceil_usize(NONRESERVED_PROGRAM_INPUT_START + pub_input_size);
    let replacements = build_replacements(
        inner_program_log_size,
        inner_public_memory_log_size,
        bytecode_zero_eval,
        pub_input_size,
    );

    let filepath = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("main.py")
        .to_str()
        .unwrap()
        .to_string();
    compile_program_with_flags(&ProgramSource::Filepath(filepath), CompilationFlags { replacements })
}

#[instrument(skip_all)]
fn compile_main_program_self_referential() -> Bytecode {
    let mut log_size_guess = 18;
    let bytecode_zero_eval = F::ONE;
    loop {
        let bytecode = compile_main_program(log_size_guess, bytecode_zero_eval);
        assert_eq!(bytecode_zero_eval, bytecode.instructions_multilinear[0]);
        let actual_log_size = bytecode.log_size();
        if actual_log_size == log_size_guess {
            return bytecode;
        } else {
            println!(
                "Wrong guess at `compile_main_program_self_referential`, should be {} instead of {}, recompiling...",
                actual_log_size, log_size_guess
            );
        }
        log_size_guess = actual_log_size;
    }
}

fn build_replacements(
    inner_program_log_size: usize,
    inner_public_memory_log_size: usize,
    bytecode_zero_eval: F,
    pub_input_size: usize,
) -> BTreeMap<String, String> {
    let mut replacements = BTreeMap::new();

    let log_inner_bytecode = inner_program_log_size;
    let min_stacked = min_stacked_n_vars(log_inner_bytecode);

    let mut all_potential_num_queries = vec![];
    let mut all_potential_query_grinding = vec![];
    let mut all_potential_num_oods = vec![];
    let mut all_potential_folding_grinding = vec![];
    let mut too_much_grinding = false;
    for log_inv_rate in MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE {
        let max_n_vars = F::TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate;
        let whir_config_builder = default_whir_config(log_inv_rate);

        let mut queries_for_rate = vec![];
        let mut query_grinding_for_rate = vec![];
        let mut oods_for_rate = vec![];
        let mut folding_grinding_for_rate = vec![];
        for n_vars in min_stacked..=max_n_vars {
            let cfg = WhirConfig::<EF>::new(&whir_config_builder, n_vars);
            if cfg.max_folding_pow_bits() > GRINDING_BITS {
                too_much_grinding = true;
            }

            let mut num_queries = vec![];
            let mut query_grinding_bits = vec![];
            let mut oods = vec![cfg.commitment_ood_samples];
            let mut folding_grinding = vec![cfg.starting_folding_pow_bits];
            for round in &cfg.round_parameters {
                num_queries.push(round.num_queries);
                query_grinding_bits.push(round.query_pow_bits);
                oods.push(round.ood_samples);
                folding_grinding.push(round.folding_pow_bits);
            }
            num_queries.push(cfg.final_queries);
            query_grinding_bits.push(cfg.final_query_pow_bits);

            queries_for_rate.push(format!(
                "[{}]",
                num_queries.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(", ")
            ));
            query_grinding_for_rate.push(format!(
                "[{}]",
                query_grinding_bits
                    .iter()
                    .map(|q| q.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
            oods_for_rate.push(format!(
                "[{}]",
                oods.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", ")
            ));
            folding_grinding_for_rate.push(format!(
                "[{}]",
                folding_grinding
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        all_potential_num_queries.push(format!("[{}]", queries_for_rate.join(", ")));
        all_potential_query_grinding.push(format!("[{}]", query_grinding_for_rate.join(", ")));
        all_potential_num_oods.push(format!("[{}]", oods_for_rate.join(", ")));
        all_potential_folding_grinding.push(format!("[{}]", folding_grinding_for_rate.join(", ")));
    }
    if too_much_grinding {
        tracing::warn!("Too much grinding for WHIR folding",);
    }
    replacements.insert(
        "WHIR_FIRST_RS_REDUCTION_FACTOR_PLACEHOLDER".to_string(),
        RS_DOMAIN_INITIAL_REDUCTION_FACTOR.to_string(),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_QUERIES_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_queries.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_QUERY_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_query_grinding.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_OODS_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_oods.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_FOLDING_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_folding_grinding.join(", ")),
    );
    replacements.insert("MIN_STACKED_N_VARS_PLACEHOLDER".to_string(), min_stacked.to_string());

    // VM recursion parameters (different from WHIR)
    replacements.insert("N_TABLES_PLACEHOLDER".to_string(), N_TABLES.to_string());
    replacements.insert(
        "MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        MIN_LOG_N_ROWS_PER_TABLE.to_string(),
    );
    let mut max_log_n_rows_per_table = MAX_LOG_N_ROWS_PER_TABLE.to_vec();
    max_log_n_rows_per_table.sort_by_key(|(table, _)| table.index());
    max_log_n_rows_per_table.dedup();
    assert_eq!(max_log_n_rows_per_table.len(), N_TABLES);
    replacements.insert(
        "MIN_WHIR_LOG_INV_RATE_PLACEHOLDER".to_string(),
        MIN_WHIR_LOG_INV_RATE.to_string(),
    );
    replacements.insert(
        "MAX_WHIR_LOG_INV_RATE_PLACEHOLDER".to_string(),
        MAX_WHIR_LOG_INV_RATE.to_string(),
    );
    replacements.insert(
        "MAX_NUM_VARIABLES_TO_SEND_COEFFS_PLACEHOLDER".to_string(),
        MAX_NUM_VARIABLES_TO_SEND_COEFFS.to_string(),
    );
    replacements.insert(
        "WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER".to_string(),
        WHIR_INITIAL_FOLDING_FACTOR.to_string(),
    );
    replacements.insert(
        "WHIR_SUBSEQUENT_FOLDING_FACTOR_PLACEHOLDER".to_string(),
        WHIR_SUBSEQUENT_FOLDING_FACTOR.to_string(),
    );
    replacements.insert(
        "MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        format!(
            "[{}]",
            max_log_n_rows_per_table
                .iter()
                .map(|(_, v)| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    );
    replacements.insert(
        "MIN_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MIN_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MAX_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_BUS_WIDTH_PLACEHOLDER".to_string(),
        max_bus_width_including_domainsep().to_string(),
    );
    replacements.insert(
        "LOGUP_MEMORY_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_MEMORY_DOMAINSEP.to_string(),
    );
    replacements.insert(
        "LOGUP_PRECOMPILE_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_PRECOMPILE_DOMAINSEP.to_string(),
    );
    replacements.insert(
        "LOGUP_BYTECODE_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_BYTECODE_DOMAINSEP.to_string(),
    );
    replacements.insert(
        "LOG_GUEST_BYTECODE_LEN_PLACEHOLDER".to_string(),
        log_inner_bytecode.to_string(),
    );
    replacements.insert("COL_PC_PLACEHOLDER".to_string(), COL_PC.to_string());
    replacements.insert(
        "NONRESERVED_PROGRAM_INPUT_START_PLACEHOLDER".to_string(),
        NONRESERVED_PROGRAM_INPUT_START.to_string(),
    );
    replacements.insert(
        "INNER_PUBLIC_MEMORY_LOG_SIZE_PLACEHOLDER".to_string(),
        inner_public_memory_log_size.to_string(),
    );
    replacements.insert("PUB_INPUT_SIZE_PLACEHOLDER".to_string(), pub_input_size.to_string());

    let mut lookup_indexes_str = vec![];
    let mut lookup_values_str = vec![];
    let mut num_cols_air = vec![];
    let mut air_degrees = vec![];
    let mut n_air_columns = vec![];
    let mut air_down_columns = vec![];
    for table in ALL_TABLES {
        let this_look_f_indexes_str = table
            .lookups()
            .iter()
            .map(|lookup_f| lookup_f.index.to_string())
            .collect::<Vec<_>>();
        lookup_indexes_str.push(format!("[{}]", this_look_f_indexes_str.join(", ")));
        num_cols_air.push(table.n_columns().to_string());
        let this_lookup_f_values_str = table
            .lookups()
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
        lookup_values_str.push(format!("[{}]", this_lookup_f_values_str.join(", ")));
        air_degrees.push(table.degree_air().to_string());
        n_air_columns.push(table.n_columns().to_string());
        air_down_columns.push(format!(
            "[{}]",
            table
                .down_column_indexes()
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    replacements.insert(
        "LOOKUPS_INDEXES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_indexes_str.join(", ")),
    );
    replacements.insert(
        "LOOKUPS_VALUES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_values_str.join(", ")),
    );
    replacements.insert(
        "NUM_COLS_AIR_PLACEHOLDER".to_string(),
        format!("[{}]", num_cols_air.join(", ")),
    );
    replacements.insert(
        "EXECUTION_TABLE_INDEX_PLACEHOLDER".to_string(),
        Table::execution().index().to_string(),
    );
    replacements.insert(
        "MAX_NUM_AIR_CONSTRAINTS_PLACEHOLDER".to_string(),
        max_air_constraints().to_string(),
    );
    replacements.insert(
        "AIR_DEGREES_PLACEHOLDER".to_string(),
        format!("[{}]", air_degrees.join(", ")),
    );
    replacements.insert(
        "N_AIR_COLUMNS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_columns.join(", ")),
    );
    replacements.insert(
        "AIR_DOWN_COLUMNS_PLACEHOLDER".to_string(),
        format!("[{}]", air_down_columns.join(", ")),
    );
    replacements.insert(
        "EVALUATE_AIR_FUNCTIONS_PLACEHOLDER".to_string(),
        all_air_evals_in_zk_dsl(),
    );
    replacements.insert(
        "N_INSTRUCTION_COLUMNS_PLACEHOLDER".to_string(),
        N_INSTRUCTION_COLUMNS.to_string(),
    );
    replacements.insert(
        "N_COMMITTED_EXEC_COLUMNS_PLACEHOLDER".to_string(),
        N_RUNTIME_COLUMNS.to_string(),
    );
    replacements.insert(
        "TOTAL_WHIR_STATEMENTS_PLACEHOLDER".to_string(),
        total_whir_statements().to_string(),
    );
    replacements.insert("STARTING_PC_PLACEHOLDER".to_string(), STARTING_PC.to_string());
    replacements.insert("ENDING_PC_PLACEHOLDER".to_string(), ENDING_PC.to_string());

    // XMSS-specific replacements
    replacements.insert("V_PLACEHOLDER".to_string(), V.to_string());
    replacements.insert("V_GRINDING_PLACEHOLDER".to_string(), V_GRINDING.to_string());
    replacements.insert("W_PLACEHOLDER".to_string(), W.to_string());
    replacements.insert("TARGET_SUM_PLACEHOLDER".to_string(), TARGET_SUM.to_string());
    replacements.insert("LOG_LIFETIME_PLACEHOLDER".to_string(), LOG_LIFETIME.to_string());
    replacements.insert("MESSAGE_LEN_PLACEHOLDER".to_string(), MESSAGE_LEN_FE.to_string());
    replacements.insert("RANDOMNESS_LEN_PLACEHOLDER".to_string(), RANDOMNESS_LEN_FE.to_string());
    replacements.insert(
        "MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER".to_string(),
        MERKLE_LEVELS_PER_CHUNK_FOR_SLOT.to_string(),
    );

    // Bytecode zero eval
    replacements.insert(
        "BYTECODE_ZERO_EVAL_PLACEHOLDER".to_string(),
        bytecode_zero_eval.as_canonical_u64().to_string(),
    );

    replacements
}

fn all_air_evals_in_zk_dsl() -> String {
    use crate::air_constraints_optimizer::{expr_graph_from_symbolic, rate_solution, solution_to_zkdsl, solve_trivial};

    fn gen_table<T: TableT>(table: T, idx: usize) -> String
    where
        T::ExtraData: Default,
    {
        let graph = expr_graph_from_symbolic(&table);
        let solution = solve_trivial(&graph);
        let cost = rate_solution(&solution);
        tracing::info!(
            "Table {} AIR codegen: {} instructions, {} exec rows, {} ext op rows",
            idx,
            solution.instructions.len(),
            cost.exec_rows,
            cost.ext_op_rows
        );
        solution_to_zkdsl(&solution, &graph, idx)
    }

    let mut res = String::new();
    res += &gen_table(ExecutionTable::<false> {}, 0);
    res += &gen_table(ExtensionOpPrecompile::<false> {}, 1);
    res += &gen_table(Poseidon16Precompile::<false> {}, 2);
    res
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

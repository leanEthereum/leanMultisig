use backend::*;
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    GRINDING_BITS, MAX_NUM_VARIABLES_TO_SEND_COEFFS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, WHIR_INITIAL_FOLDING_FACTOR,
    WHIR_SUBSEQUENT_FOLDING_FACTOR, default_whir_config,
};
use lean_vm::*;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::rc::Rc;
use std::sync::OnceLock;
use sub_protocols::{min_stacked_n_vars, total_whir_statements};
use tracing::instrument;
use utils::Counter;
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, RANDOMNESS_LEN_FE, TARGET_SUM, V, V_GRINDING, W};

use crate::{MERKLE_LEVELS_PER_CHUNK_FOR_SLOT, N_MERKLE_CHUNKS_FOR_SLOT};

static BYTECODE: OnceLock<Bytecode> = OnceLock::new();

pub(crate) fn get_aggregation_bytecode() -> &'static Bytecode {
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
    // pub_input layout: n_sigs(1) + slice_hash(8) + slot_low(1) + slot_high(1)
    //                   + message + merkle_chunks_for_slot + bytecode_claim
    let pub_input_size = 1 + DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + claim_data_size;
    let inner_public_memory_log_size = log2_ceil_usize(NONRESERVED_PROGRAM_INPUT_START + pub_input_size);
    let replacements = build_replacements(inner_program_log_size, inner_public_memory_log_size, bytecode_zero_eval);

    let filepath = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("main.py")
        .to_str()
        .unwrap()
        .to_string();
    compile_program_with_flags(&ProgramSource::Filepath(filepath), CompilationFlags { replacements })
}

#[instrument(skip_all)]
fn compile_main_program_self_referential() -> Bytecode {
    let mut log_size_guess = 19;
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
    let mut res = String::new();
    res += &air_eval_in_zk_dsl(ExecutionTable::<false> {});
    res += &air_eval_in_zk_dsl(ExtensionOpPrecompile::<false> {});
    res += &air_eval_in_zk_dsl(Poseidon16Precompile::<false> {});
    res
}

const AIR_INNER_VALUES_VAR: &str = "inner_evals";

fn air_eval_in_zk_dsl<T: TableT>(table: T) -> String
where
    T::ExtraData: Default,
{
    let (constraints, bus_flag, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
    let mut vars_counter = Counter::new();
    let mut cache: HashMap<*const (), String> = HashMap::new();

    let mut res = format!(
        "def evaluate_air_constraints_table_{}({}, air_alpha_powers, bus_beta, logup_alphas_eq_poly):\n",
        table.table().index(),
        AIR_INNER_VALUES_VAR
    );

    let n_constraints = constraints.len();
    res += &format!("\n    constraints_buf = Array(DIM * {})", n_constraints);
    for (index, constraint) in constraints.iter().enumerate() {
        let dest = format!("constraints_buf + {} * DIM", index);
        eval_air_constraint(constraint, Some(&dest), &mut cache, &mut res, &mut vars_counter);
    }

    // first: bus data
    let flag = eval_air_constraint(&bus_flag, None, &mut cache, &mut res, &mut vars_counter);
    res += &format!("\n    buff = Array(DIM * {})", bus_data.len());
    for (i, data) in bus_data.iter().enumerate() {
        let data_str = eval_air_constraint(data, None, &mut cache, &mut res, &mut vars_counter);
        res += &format!("\n    copy_5({}, buff + DIM * {})", data_str, i);
    }
    // dot product: bus_res = sum(buff[i] * logup_alphas_eq_poly[i]) for i in 0..bus_data.len()
    res += "\n    bus_res_init = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee(buff, logup_alphas_eq_poly, bus_res_init, {})",
        bus_data.len()
    );
    res += &format!(
        "\n    bus_res: Mut = add_extension_ret(mul_base_extension_ret(LOGUP_PRECOMPILE_DOMAINSEP, logup_alphas_eq_poly + {} * DIM), bus_res_init)",
        max_bus_width_including_domainsep().next_power_of_two() - 1
    );
    res += "\n    bus_res = mul_extension_ret(bus_res, bus_beta)";
    res += &format!("\n    sum: Mut = add_extension_ret(bus_res, {})", flag);

    // Batch constraint weighting: single dot_product_ee(alpha_powers, constraints_buf, result, n_constraints)
    res += "\n    weighted_constraints = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee(air_alpha_powers + DIM, constraints_buf, weighted_constraints, {})",
        n_constraints
    );
    res += "\n    sum = add_extension_ret(sum, weighted_constraints)";

    res += "\n    return sum";
    res += "\n";
    res
}

/// Evaluate a symbolic AIR constraint expression, emitting zkDSL code into `res`.
/// If `dest` is Some, writes the result directly there (avoids a copy_5).
/// If `dest` is None, allocates an aux var. Returns the var/pointer where the result lives.
fn eval_air_constraint(
    expr: &SymbolicExpression<F>,
    dest: Option<&str>,
    cache: &mut HashMap<*const (), String>,
    res: &mut String,
    ctr: &mut Counter,
) -> String {
    match expr {
        SymbolicExpression::Constant(c) => {
            let v = format!("aux_{}", ctr.get_next());
            res.push_str(&format!("\n    {} = embed_in_ef({})", v, c.as_canonical_u32()));
            v
        }
        SymbolicExpression::Variable(v) => format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, v.index),
        SymbolicExpression::Operation(operation) => {
            let key = Rc::as_ptr(operation) as *const ();
            if let Some(v) = cache.get(&key) {
                if let Some(d) = dest {
                    res.push_str(&format!("\n    copy_5({}, {})", v, d));
                }
                return v.clone();
            }
            let (op, args) = &**operation;
            let v = match *op {
                SymbolicOperation::Neg => {
                    assert_eq!(args.len(), 1);
                    let a = eval_air_constraint(&args[0], None, cache, res, ctr);
                    let v = format!("aux_{}", ctr.get_next());
                    res.push_str(&format!("\n    {} = opposite_extension_ret({})", v, a));
                    v
                }
                _ => {
                    assert_eq!(args.len(), 2);
                    eval_air_binop(*op, args, dest, cache, res, ctr)
                }
            };
            // If dest was requested but the result landed elsewhere, copy it
            if let Some(d) = dest
                && v != d
            {
                res.push_str(&format!("\n    copy_5({}, {})", v, d));
            }
            cache.insert(key, v.clone());
            v
        }
    }
}

/// Evaluate a binary operation (Add/Sub/Mul). When `dest` is Some and the operation
/// supports it, writes directly to dest and returns dest; otherwise allocates an aux var.
fn eval_air_binop(
    op: SymbolicOperation,
    args: &[SymbolicExpression<F>],
    dest: Option<&str>,
    cache: &mut HashMap<*const (), String>,
    res: &mut String,
    ctr: &mut Counter,
) -> String {
    let c0 = match &args[0] {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };
    let c1 = match &args[1] {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };

    match (c0, c1) {
        // Both extension
        (None, None) => {
            let a = eval_air_constraint(&args[0], None, cache, res, ctr);
            let b = eval_air_constraint(&args[1], None, cache, res, ctr);
            if let Some(d) = dest {
                let f = match op {
                    SymbolicOperation::Mul => "mul_extension",
                    SymbolicOperation::Add => "add_ee",
                    SymbolicOperation::Sub => "sub_extension",
                    _ => unreachable!(),
                };
                res.push_str(&format!("\n    {}({}, {}, {})", f, a, b, d));
                d.to_string()
            } else {
                let f = match op {
                    SymbolicOperation::Mul => "mul_extension_ret",
                    SymbolicOperation::Add => "add_extension_ret",
                    SymbolicOperation::Sub => "sub_extension_ret",
                    _ => unreachable!(),
                };
                let v = format!("aux_{}", ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, a, b));
                v
            }
        }
        // Mul/Add with a constant (commutative for base-ext)
        _ if matches!(op, SymbolicOperation::Mul | SymbolicOperation::Add) => {
            let (c, ext_idx) = match (c0, c1) {
                (Some(c), _) => (c, 1),
                (_, Some(c)) => (c, 0),
                _ => unreachable!(),
            };
            let ext = eval_air_constraint(&args[ext_idx], None, cache, res, ctr);
            if let Some(d) = dest {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "dot_product_be"
                } else {
                    "add_be"
                };
                emit_base_precompile(res, ctr, f, c, &ext, d);
                d.to_string()
            } else {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "mul_base_extension_ret"
                } else {
                    "add_base_extension_ret"
                };
                let v = format!("aux_{}", ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, c, ext));
                v
            }
        }
        // Sub: base - ext
        (Some(c), _) => {
            let ext = eval_air_constraint(&args[1], None, cache, res, ctr);
            let v = format!("aux_{}", ctr.get_next());
            res.push_str(&format!("\n    {} = sub_base_extension_ret({}, {})", v, c, ext));
            v
        }
        // Sub: ext - base
        (_, Some(c)) => {
            let ext = eval_air_constraint(&args[0], None, cache, res, ctr);
            if let Some(d) = dest {
                // add_be(tmp, dest, ext) asserts ext = tmp + dest, i.e. dest = ext - tmp
                emit_base_precompile(res, ctr, "add_be", c, d, &ext);
                d.to_string()
            } else {
                let v = format!("aux_{}", ctr.get_next());
                res.push_str(&format!("\n    {} = sub_extension_base_ret({}, {})", v, ext, c));
                v
            }
        }
    }
}

/// Emit: `tmp = Array(1); tmp[0] = c; func(tmp, arg2, arg3)`
fn emit_base_precompile(res: &mut String, ctr: &mut Counter, func: &str, c: u32, arg2: &str, arg3: &str) {
    let tmp = format!("aux_{}", ctr.get_next());
    res.push_str(&format!(
        "\n    {} = Array(1)\n    {}[0] = {}\n    {}({}, {}, {})",
        tmp, tmp, c, func, tmp, arg2, arg3
    ));
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

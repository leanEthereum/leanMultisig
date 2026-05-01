use backend::*;
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    GRINDING_BITS, MAX_NUM_VARIABLES_TO_SEND_COEFFS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, WHIR_INITIAL_FOLDING_FACTOR,
    WHIR_SUBSEQUENT_FOLDING_FACTOR, default_whir_config,
};
use lean_vm::*;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::OnceLock;
use sub_protocols::{N_VARS_TO_SEND_GKR_COEFFS, min_stacked_n_vars, total_whir_statements};
use tracing::instrument;
use utils::Counter;
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, PUBLIC_PARAM_LEN_FE, RANDOMNESS_LEN_FE, TARGET_SUM, V, W, XMSS_DIGEST_LEN};

use crate::{MERKLE_LEVELS_PER_CHUNK_FOR_SLOT, N_MERKLE_CHUNKS_FOR_SLOT, NUM_REPEATED_ONES, ZERO_VEC_LEN};

static BYTECODE: OnceLock<Bytecode> = OnceLock::new();

pub fn get_aggregation_bytecode() -> &'static Bytecode {
    BYTECODE
        .get()
        .unwrap_or_else(|| panic!("call init_aggregation_bytecode() first"))
}

pub fn init_aggregation_bytecode() {
    BYTECODE.get_or_init(compile_main_program_self_referential);
}

fn compile_main_program(program_log_size: usize, bytecode_zero_eval: F) -> Bytecode {
    let bytecode_point_n_vars = program_log_size + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let claim_data_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let claim_data_size_padded = claim_data_size.next_multiple_of(DIGEST_LEN);
    // input_data_buf layout (part of the witness, "hinted" then hashed to a single digest that should match public input):
    //   n_sigs(1) + pubkeys_hash(8) + message + merkle_chunks_for_slot
    //   + tweaks_hash(8) + bytecode_claim_padded + bytecode_hash_domsep(8)
    let input_data_size =
        1 + DIGEST_LEN + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + DIGEST_LEN + claim_data_size_padded + DIGEST_LEN;
    let input_data_size_padded = input_data_size.next_multiple_of(DIGEST_LEN);
    let replacements = build_replacements(program_log_size, bytecode_zero_eval, input_data_size_padded);

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
    bytecode_zero_eval: F,
    input_data_size_padded: usize,
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
        tracing::info!("Warning: Too much grinding for WHIR folding"); // TODO
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
        "LOGUP_GKR_N_VARS_TO_SEND_COEFFS_PLACEHOLDER".to_string(),
        N_VARS_TO_SEND_GKR_COEFFS.to_string(),
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
        "INPUT_DATA_SIZE_PADDED_PLACEHOLDER".to_string(),
        input_data_size_padded.to_string(),
    );
    let bytecode_point_n_vars = log_inner_bytecode + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    replacements.insert(
        "BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER".to_string(),
        bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars).to_string(),
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
        "MAX_AIR_FULL_DEGREE_PLACEHOLDER".to_string(),
        (ALL_TABLES.iter().map(|t| t.degree_air()).max().unwrap() + 1).to_string(),
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
    replacements.insert("W_PLACEHOLDER".to_string(), W.to_string());
    replacements.insert("TARGET_SUM_PLACEHOLDER".to_string(), TARGET_SUM.to_string());
    replacements.insert("LOG_LIFETIME_PLACEHOLDER".to_string(), LOG_LIFETIME.to_string());
    replacements.insert("MESSAGE_LEN_PLACEHOLDER".to_string(), MESSAGE_LEN_FE.to_string());
    replacements.insert("RANDOMNESS_LEN_PLACEHOLDER".to_string(), RANDOMNESS_LEN_FE.to_string());
    replacements.insert(
        "PUBLIC_PARAM_LEN_FE_PLACEHOLDER".to_string(),
        PUBLIC_PARAM_LEN_FE.to_string(),
    );
    replacements.insert(
        "MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER".to_string(),
        MERKLE_LEVELS_PER_CHUNK_FOR_SLOT.to_string(),
    );
    replacements.insert("XMSS_DIGEST_LEN_PLACEHOLDER".to_string(), XMSS_DIGEST_LEN.to_string());

    // Bytecode zero eval
    replacements.insert(
        "BYTECODE_ZERO_EVAL_PLACEHOLDER".to_string(),
        bytecode_zero_eval.as_canonical_u64().to_string(),
    );
    replacements.insert("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string());
    replacements.insert(
        "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
        NUM_REPEATED_ONES.to_string(),
    );

    replacements
}

pub(crate) fn bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars: usize) -> usize {
    let per_round = (3 * DIMENSION).next_multiple_of(DIGEST_LEN);
    DIGEST_LEN + bytecode_point_n_vars * per_round
}

fn all_air_evals_in_zk_dsl() -> String {
    let mut res = String::new();
    res += &air_eval_in_zk_dsl(ExecutionTable::<false> {});
    res += &air_eval_in_zk_dsl(ExtensionOpPrecompile::<false> {});
    res += &air_eval_in_zk_dsl(Poseidon16Precompile::<false> {});
    res
}

const AIR_INNER_VALUES_VAR: &str = "inner_evals";

struct AirCodegenCtx {
    expr_cache: HashMap<u32, String>,
    consts_cache: HashMap<Vec<u32>, String>,
    ef_const_cache: HashMap<u32, String>,
    ctr: Counter,
}

impl AirCodegenCtx {
    fn new() -> Self {
        Self {
            expr_cache: HashMap::new(),
            consts_cache: HashMap::new(),
            ef_const_cache: HashMap::new(),
            ctr: Counter::new(),
        }
    }

    fn write_base_constants(&mut self, values: &[u32], res: &mut String) -> String {
        if let Some(name) = self.consts_cache.get(values) {
            return name.clone();
        }
        let name = format!("bc_{}", self.ctr.get_next());
        res.push_str(&format!("\n    {} = Array({})", name, values.len()));
        for (i, &c) in values.iter().enumerate() {
            res.push_str(&format!("\n    {}[{}] = {}", name, i, c));
        }
        self.consts_cache.insert(values.to_vec(), name.clone());
        name
    }

    fn write_embedded_constant(&mut self, c: u32, res: &mut String) -> String {
        if let Some(name) = self.ef_const_cache.get(&c) {
            return name.clone();
        }
        let name = format!("aux_{}", self.ctr.get_next());
        res.push_str(&format!("\n    {} = embed_in_ef({})", name, c));
        self.ef_const_cache.insert(c, name.clone());
        name
    }
}

fn air_eval_in_zk_dsl<T: TableT>(table: T) -> String
where
    T::ExtraData: Default,
{
    let (constraints, bus_flag, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
    let mut ctx = AirCodegenCtx::new();

    let mut res = format!(
        "def evaluate_air_constraints_table_{}({}, air_alpha_powers, bus_beta, logup_alphas_eq_poly):\n",
        table.table().index(),
        AIR_INNER_VALUES_VAR
    );

    let n_constraints = constraints.len();
    res += &format!("\n    constraints_buf = Array(DIM * {})", n_constraints);
    for (index, constraint) in constraints.iter().enumerate() {
        let dest = format!("constraints_buf + {} * DIM", index);
        eval_air_constraint(*constraint, Some(&dest), &mut ctx, &mut res);
    }

    // first: bus data
    let flag = eval_air_constraint(bus_flag, None, &mut ctx, &mut res);
    res += &format!("\n    buff = Array(DIM * {})", bus_data.len());
    for (i, data) in bus_data.iter().enumerate() {
        let data_str = eval_air_constraint(*data, None, &mut ctx, &mut res);
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

fn eval_air_constraint(
    expr: SymbolicExpression<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> String {
    let v = match expr {
        SymbolicExpression::Constant(c) => ctx.write_embedded_constant(c.as_canonical_u32(), res),
        SymbolicExpression::Variable(v) => format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, v.index),
        SymbolicExpression::Operation(idx) => {
            if let Some(v) = ctx.expr_cache.get(&idx) {
                v.clone()
            } else if let Some(v) = try_emit_dot_product_be(idx, dest, ctx, res) {
                ctx.expr_cache.insert(idx, v.clone());
                return v;
            } else {
                let node = get_node::<F>(idx);
                let v = match node.op {
                    SymbolicOperation::Neg => {
                        let a = eval_air_constraint(node.lhs, None, ctx, res);
                        let v = format!("aux_{}", ctx.ctr.get_next());
                        res.push_str(&format!("\n    {} = opposite_extension_ret({})", v, a));
                        v
                    }
                    _ => eval_air_binary_op(node.op, node.lhs, node.rhs, dest, ctx, res),
                };
                ctx.expr_cache.insert(idx, v.clone());
                v
            }
        }
    };
    if let Some(d) = dest
        && v != d
    {
        res.push_str(&format!("\n    copy_5({}, {})", v, d));
    }
    v
}

/// Detect `0 + c0*x0 + c1*x1 + ... + cn*xn` in the expression tree and emit
/// a single `dot_product_be` precompile call. Returns None if the pattern doesn't match.
fn try_emit_dot_product_be(idx: u32, dest: Option<&str>, ctx: &mut AirCodegenCtx, res: &mut String) -> Option<String> {
    // Walk the left-spine of Add(_, Mul(Const, _)) nodes down to Constant(ZERO).
    let mut constants = Vec::new();
    let mut operands = Vec::new();
    let mut current = SymbolicExpression::<F>::Operation(idx);
    loop {
        match current {
            SymbolicExpression::Constant(c) if c == F::ZERO && constants.len() >= 2 => break,
            SymbolicExpression::Operation(op_idx) => {
                if op_idx != idx && ctx.expr_cache.contains_key(&op_idx) {
                    return None;
                }
                let node = get_node::<F>(op_idx);
                if node.op != SymbolicOperation::Add {
                    return None;
                }
                let mul_idx = match node.rhs {
                    SymbolicExpression::Operation(i) => i,
                    _ => return None,
                };
                let mul = get_node::<F>(mul_idx);
                if mul.op != SymbolicOperation::Mul {
                    return None;
                }
                let (c, expr) = match (mul.lhs, mul.rhs) {
                    (SymbolicExpression::Constant(c), o) | (o, SymbolicExpression::Constant(c)) => {
                        (c.as_canonical_u32(), o)
                    }
                    _ => return None,
                };
                constants.push(c);
                operands.push(expr);
                current = node.lhs;
            }
            _ => return None,
        }
    }
    constants.reverse();
    operands.reverse();
    let n = constants.len();

    let consts = ctx.write_base_constants(&constants, res);

    // Reuse an existing contiguous buffer if possible.
    let vals = try_find_contiguous_buffer(&operands, ctx).unwrap_or_else(|| {
        let buf = format!("dp_v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = Array(DIM * {})", buf, n));
        for (i, ext) in operands.iter().enumerate() {
            eval_air_constraint(*ext, Some(&format!("{} + DIM * {}", buf, i)), ctx, res);
        }
        buf
    });

    let dp_dest = dest.map_or_else(
        || {
            let v = format!("aux_{}", ctx.ctr.get_next());
            res.push_str(&format!("\n    {} = Array(DIM)", v));
            v
        },
        |d| d.to_string(),
    );
    res.push_str(&format!(
        "\n    dot_product_be({}, {}, {}, {})",
        consts, vals, dp_dest, n
    ));
    Some(dp_dest)
}

/// Check whether every operand is already cached as consecutive slots in the
/// same buffer (`buf + DIM * 0`, `buf + DIM * 1`, …).
fn try_find_contiguous_buffer(operands: &[SymbolicExpression<F>], ctx: &AirCodegenCtx) -> Option<String> {
    let mut base: Option<&str> = None;
    for (i, op) in operands.iter().enumerate() {
        let idx = match op {
            SymbolicExpression::Operation(idx) => *idx,
            _ => return None,
        };
        let suffix = format!(" + DIM * {}", i);
        let this_base = ctx.expr_cache.get(&idx)?.strip_suffix(&suffix)?;
        match base {
            None => base = Some(this_base),
            Some(b) if b == this_base => {}
            _ => return None,
        }
    }
    base.map(|s| s.to_string())
}

fn eval_air_binary_op(
    op: SymbolicOperation,
    lhs: SymbolicExpression<F>,
    rhs: SymbolicExpression<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> String {
    let c0 = match lhs {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };
    let c1 = match rhs {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };

    match (c0, c1) {
        // Both extension
        (None, None) => {
            let a = eval_air_constraint(lhs, None, ctx, res);
            let b = eval_air_constraint(rhs, None, ctx, res);
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
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, a, b));
                v
            }
        }
        // Mul/Add with a base-field constant
        _ if matches!(op, SymbolicOperation::Mul | SymbolicOperation::Add) => {
            let (c, ext_expr) = match (c0, c1) {
                (Some(c), _) => (c, rhs),
                (_, Some(c)) => (c, lhs),
                _ => unreachable!(),
            };
            let ext = eval_air_constraint(ext_expr, None, ctx, res);
            if let Some(d) = dest {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "dot_product_be"
                } else {
                    "add_be"
                };
                let scalar = ctx.write_base_constants(&[c], res);
                res.push_str(&format!("\n    {}({}, {}, {})", f, scalar, ext, d));
                d.to_string()
            } else {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "mul_base_extension_ret"
                } else {
                    "add_base_extension_ret"
                };
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, c, ext));
                v
            }
        }
        // Sub: base - ext
        (Some(c), _) => {
            let ext = eval_air_constraint(rhs, None, ctx, res);
            let v = format!("aux_{}", ctx.ctr.get_next());
            res.push_str(&format!("\n    {} = sub_base_extension_ret({}, {})", v, c, ext));
            v
        }
        // Sub: ext - base
        (_, Some(c)) => {
            let ext = eval_air_constraint(lhs, None, ctx, res);
            if let Some(d) = dest {
                let scalar = ctx.write_base_constants(&[c], res);
                res.push_str(&format!("\n    add_be({}, {}, {})", scalar, d, ext));
                d.to_string()
            } else {
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = sub_extension_base_ret({}, {})", v, ext, c));
                v
            }
        }
    }
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

#[test]
fn display_poseidon_air_in_zk_dsl() {
    println!("{}", air_eval_in_zk_dsl(Poseidon16Precompile::<false> {}));
}

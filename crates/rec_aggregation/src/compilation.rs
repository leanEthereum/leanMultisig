use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    MAX_NUM_VARIABLES_TO_SEND_COEFFS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, WHIR_INITIAL_FOLDING_FACTOR,
    WHIR_SUBSEQUENT_FOLDING_FACTOR, default_whir_config,
};
use lean_vm::*;
use multilinear_toolkit::prelude::symbolic::{
    SymbolicExpression, SymbolicOperation, get_symbolic_constraints_and_bus_data_values,
};
use multilinear_toolkit::prelude::*;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::rc::Rc;
use sub_protocols::{min_stacked_n_vars, total_whir_statements};
use utils::{BYTECODE_TABLE_INDEX, Counter, MEMORY_TABLE_INDEX};

pub(crate) fn get_recursion_bytecode_helper(
    prox_gaps_conjecture: bool,
    inner_program_log_size: usize,
    bytecode_zero_eval: F,
) -> Bytecode {
    let mut replacements = BTreeMap::new();
    replacements.insert(
        "BYTECODE_ZERO_EVAL_PLACEHOLDER".to_string(),
        bytecode_zero_eval.as_canonical_u64().to_string(),
    );

    let log_inner_bytecode = inner_program_log_size;
    let min_stacked = min_stacked_n_vars(log_inner_bytecode);

    let mut all_potential_num_queries = vec![];
    let mut all_potential_grinding = vec![];
    let mut all_potential_num_oods = vec![];
    for log_inv_rate in MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE {
        let max_n_vars = F::TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate;
        let whir_config_builder = default_whir_config(log_inv_rate, prox_gaps_conjecture);
        let whir_config = WhirConfig::<EF>::new(&whir_config_builder, max_n_vars);
        let mut num_queries = vec![];
        let mut grinding_bits = vec![];
        for round in &whir_config.round_parameters {
            num_queries.push(round.num_queries);
            grinding_bits.push(round.pow_bits);
        }
        num_queries.push(whir_config.final_queries);
        grinding_bits.push(whir_config.final_pow_bits);
        all_potential_num_queries.push(format!(
            "[{}]",
            num_queries.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(", ")
        ));
        all_potential_grinding.push(format!(
            "[{}]",
            grinding_bits
                .iter()
                .map(|q| q.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));

        // OOD samples for each possible stacked_n_vars
        let mut oods_for_rate = vec![];
        for n_vars in min_stacked..=max_n_vars {
            let cfg = WhirConfig::<EF>::new(&whir_config_builder, n_vars);
            let mut oods = vec![cfg.committment_ood_samples];
            for round in &cfg.round_parameters {
                oods.push(round.ood_samples);
            }
            oods_for_rate.push(format!(
                "[{}]",
                oods.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", ")
            ));
        }
        all_potential_num_oods.push(format!("[{}]", oods_for_rate.join(", ")));
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
        "WHIR_ALL_POTENTIAL_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_grinding.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_OODS_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_oods.join(", ")),
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
    replacements.insert("MAX_BUS_WIDTH_PLACEHOLDER".to_string(), max_bus_width().to_string());
    replacements.insert(
        "MEMORY_TABLE_INDEX_PLACEHOLDER".to_string(),
        MEMORY_TABLE_INDEX.to_string(),
    );
    replacements.insert(
        "BYTECODE_TABLE_INDEX_PLACEHOLDER".to_string(),
        BYTECODE_TABLE_INDEX.to_string(),
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

    let mut lookup_f_indexes_str = vec![];
    let mut lookup_f_values_str = vec![];
    let mut lookup_ef_indexes_str = vec![];
    let mut lookup_ef_values_str = vec![];
    let mut num_cols_f_air = vec![];
    let mut num_cols_ef_air = vec![];
    let mut num_cols_f_committed = vec![];
    let mut air_degrees = vec![];
    let mut n_air_columns_f = vec![];
    let mut n_air_columns_ef = vec![];
    let mut air_down_columns_f = vec![];
    let mut air_down_columns_ef = vec![];
    for table in ALL_TABLES {
        let this_look_f_indexes_str = table
            .lookups_f()
            .iter()
            .map(|lookup_f| lookup_f.index.to_string())
            .collect::<Vec<_>>();
        let this_look_ef_indexes_str = table
            .lookups_ef()
            .iter()
            .map(|lookup_ef| lookup_ef.index.to_string())
            .collect::<Vec<_>>();
        lookup_f_indexes_str.push(format!("[{}]", this_look_f_indexes_str.join(", ")));
        lookup_ef_indexes_str.push(format!("[{}]", this_look_ef_indexes_str.join(", ")));
        num_cols_f_air.push(table.n_columns_f_air().to_string());
        num_cols_ef_air.push(table.n_columns_ef_air().to_string());
        num_cols_f_committed.push(table.n_columns_f_air().to_string());
        let this_lookup_f_values_str = table
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
        let this_lookup_ef_values_str = table
            .lookups_ef()
            .iter()
            .map(|lookup_ef| lookup_ef.values.to_string())
            .collect::<Vec<_>>();
        lookup_f_values_str.push(format!("[{}]", this_lookup_f_values_str.join(", ")));
        lookup_ef_values_str.push(format!("[{}]", this_lookup_ef_values_str.join(", ")));
        air_degrees.push(table.degree_air().to_string());
        n_air_columns_f.push(table.n_columns_f_air().to_string());
        n_air_columns_ef.push(table.n_columns_ef_air().to_string());
        air_down_columns_f.push(format!(
            "[{}]",
            table
                .down_column_indexes_f()
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));
        air_down_columns_ef.push(format!(
            "[{}]",
            table
                .down_column_indexes_ef()
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    replacements.insert(
        "LOOKUPS_F_INDEXES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_f_indexes_str.join(", ")),
    );
    replacements.insert(
        "LOOKUPS_F_VALUES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_f_values_str.join(", ")),
    );
    replacements.insert(
        "NUM_COLS_F_AIR_PLACEHOLDER".to_string(),
        format!("[{}]", num_cols_f_air.join(", ")),
    );
    replacements.insert(
        "NUM_COLS_EF_AIR_PLACEHOLDER".to_string(),
        format!("[{}]", num_cols_ef_air.join(", ")),
    );
    replacements.insert(
        "NUM_COLS_F_COMMITTED_PLACEHOLDER".to_string(),
        format!("[{}]", num_cols_f_committed.join(", ")),
    );
    replacements.insert(
        "LOOKUPS_EF_INDEXES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_ef_indexes_str.join(", ")),
    );
    replacements.insert(
        "LOOKUPS_EF_VALUES_PLACEHOLDER".to_string(),
        format!("[{}]", lookup_ef_values_str.join(", ")),
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
        "N_AIR_COLUMNS_F_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_columns_f.join(", ")),
    );
    replacements.insert(
        "N_AIR_COLUMNS_EF_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_columns_ef.join(", ")),
    );
    replacements.insert(
        "AIR_DOWN_COLUMNS_F_PLACEHOLDER".to_string(),
        format!("[{}]", air_down_columns_f.join(", ")),
    );
    replacements.insert(
        "AIR_DOWN_COLUMNS_EF_PLACEHOLDER".to_string(),
        format!("[{}]", air_down_columns_ef.join(", ")),
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

    let filepath = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("recursion.py")
        .to_str()
        .unwrap()
        .to_string();

    compile_program_with_flags(&ProgramSource::Filepath(filepath), CompilationFlags { replacements })
}

fn all_air_evals_in_zk_dsl() -> String {
    let mut res = String::new();
    res += &air_eval_in_zk_dsl(ExecutionTable::<false> {});
    res += &air_eval_in_zk_dsl(DotProductPrecompile::<false> {});
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

    let mut constraints_evals = vec![];
    for constraint in &constraints {
        constraints_evals.push(write_down_air_constraint_eval(
            constraint,
            &mut cache,
            &mut res,
            &mut vars_counter,
        ));
    }

    // first: bus data
    let table_index = match table.bus().table {
        BusTable::Constant(c) => format!("embed_in_ef({})", c.index()),
        BusTable::Variable(col) => format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, col),
    };
    let flag = write_down_air_constraint_eval(&bus_flag, &mut cache, &mut res, &mut vars_counter);
    res += &format!("\n    buff = Array(DIM * {})", bus_data.len());
    for (i, data) in bus_data.iter().enumerate() {
        let data_str = write_down_air_constraint_eval(data, &mut cache, &mut res, &mut vars_counter);
        res += &format!("\n    copy_5({}, buff + DIM * {})", data_str, i);
    }
    res += &format!(
        "\n    bus_res: Mut = dot_product_ret(buff, logup_alphas_eq_poly, {}, EE)",
        bus_data.len()
    );
    res += &format!(
        "\n    bus_res = add_extension_ret(mul_extension_ret({}, logup_alphas_eq_poly + {} * DIM), bus_res)",
        table_index,
        max_bus_width().next_power_of_two() - 1
    );
    res += "\n    bus_res = mul_extension_ret(bus_res, bus_beta)";
    res += &format!("\n    sum: Mut = add_extension_ret(bus_res, {})", flag);

    for (index, constraint_eval) in constraints_evals.iter().enumerate() {
        res += format!(
            "\n    sum = add_extension_ret(sum, mul_extension_ret(air_alpha_powers + {} * DIM, {}))",
            index + 1,
            constraint_eval
        )
        .as_str();
    }

    res += "\n    return sum";
    res += "\n";
    res
}

fn write_down_air_constraint_eval(
    constraint: &SymbolicExpression<F>,
    cache: &mut HashMap<*const (), String>,
    res: &mut String,
    vars_counter: &mut Counter,
) -> String {
    match constraint {
        SymbolicExpression::Constant(_) => {
            unreachable!()
        }
        SymbolicExpression::Variable(v) => {
            format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, v.index)
        }
        SymbolicExpression::Operation(operation) => {
            let key = Rc::as_ptr(operation) as *const ();
            if let Some(var_name) = cache.get(&key) {
                return var_name.clone();
            }
            let (op, args) = &**operation;

            let new_var = match *op {
                SymbolicOperation::Neg => {
                    assert_eq!(args.len(), 1);
                    let arg_str = write_down_air_constraint_eval(&args[0], cache, res, vars_counter);
                    let aux_var = format!("aux_{}", vars_counter.get_next());
                    res.push_str(&format!("\n    {} = opposite_extension_ret({})", aux_var, arg_str));
                    return aux_var;
                }
                SymbolicOperation::Add => handle_operation_on_two(
                    args,
                    cache,
                    res,
                    vars_counter,
                    ("add_base_extension_ret", "add_base_extension_ret", "add_extension_ret"),
                    true,
                ),
                SymbolicOperation::Sub => handle_operation_on_two(
                    args,
                    cache,
                    res,
                    vars_counter,
                    ("sub_base_extension_ret", "sub_extension_base_ret", "sub_extension_ret"),
                    false,
                ),
                SymbolicOperation::Mul => handle_operation_on_two(
                    args,
                    cache,
                    res,
                    vars_counter,
                    ("mul_base_extension_ret", "mul_base_extension_ret", "mul_extension_ret"),
                    true,
                ),
            };
            assert!(!cache.contains_key(&key));
            cache.insert(key, new_var.clone());
            new_var
        }
    }
}

fn handle_operation_on_two(
    args: &[SymbolicExpression<F>],
    cache: &mut HashMap<*const (), String>,
    res: &mut String,
    vars_counter: &mut Counter,
    (be_func, eb_func, ee_func): (&str, &str, &str),
    switch_args: bool,
) -> String {
    assert_eq!(args.len(), 2);
    if let SymbolicExpression::Constant(c1) = args[0] {
        let arg2_str = write_down_air_constraint_eval(&args[1], cache, res, vars_counter);
        let aux_var = format!("aux_{}", vars_counter.get_next());
        res.push_str(&format!("\n    {} = {}({}, {})", aux_var, be_func, c1, arg2_str));
        return aux_var;
    }
    if let SymbolicExpression::Constant(c2) = args[1] {
        let arg1_str = write_down_air_constraint_eval(&args[0], cache, res, vars_counter);
        let aux_var = format!("aux_{}", vars_counter.get_next());
        let (term0, term1) = if switch_args {
            (c2.to_string(), arg1_str)
        } else {
            (arg1_str, c2.to_string())
        };
        res.push_str(&format!("\n    {} = {}({}, {})", aux_var, eb_func, term0, term1));
        return aux_var;
    }
    let arg1_str = write_down_air_constraint_eval(&args[0], cache, res, vars_counter);
    let arg2_str = write_down_air_constraint_eval(&args[1], cache, res, vars_counter);
    let aux_var = format!("aux_{}", vars_counter.get_next());
    res.push_str(&format!("\n    {} = {}({}, {})", aux_var, ee_func, arg1_str, arg2_str));
    aux_var
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

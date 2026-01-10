use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::rc::Rc;
use std::time::Instant;

use lean_compiler::{CompilationFlags, ProgramSource, compile_program, compile_program_with_flags};
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{STARTING_LOG_INV_RATE_BASE, STARTING_LOG_INV_RATE_EXTENSION, SnarkParams, whir_config_builder};
use lean_vm::*;
use multilinear_toolkit::prelude::symbolic::{
    SymbolicExpression, SymbolicOperation, get_symbolic_constraints_and_bus_data_values,
};
use multilinear_toolkit::prelude::*;
use utils::{Counter, MEMORY_TABLE_INDEX};
use whir_p3::{WhirConfig, precompute_dft_twiddles};

pub fn run_recursion_benchmark(tracing: bool) {
    if tracing {
        utils::init_tracing();
    }
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
    let outer_public_input = vec![];
    let outer_private_input = vec![];
    let proof_to_prove = prove_execution(
        &bytecode_to_prove,
        (&outer_public_input, &outer_private_input),
        &vec![],
        &snark_params,
        false,
    );
    let verif_details = verify_execution(&bytecode_to_prove, &[], proof_to_prove.proof.clone(), &snark_params).unwrap();

    let base_whir = WhirConfig::<EF>::new(&snark_params.first_whir, proof_to_prove.first_whir_n_vars);
    let ext_whir = WhirConfig::<EF>::new(&snark_params.second_whir, log2_ceil_usize(program_to_prove.len()));

    let mut replacements = whir_recursion_placeholder_replacements(&base_whir, true);
    replacements.extend(whir_recursion_placeholder_replacements(&ext_whir, false));

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
    replacements.insert(
        "GUEST_BYTECODE_LEN_PLACEHOLDER".to_string(),
        bytecode_to_prove.instructions.len().to_string(),
    );
    replacements.insert("COL_INDEX_PC_PLACEHOLDER".to_string(), COL_INDEX_PC.to_string());
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
        num_cols_f_committed.push(table.n_commited_columns_f().to_string());
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
        "NUM_COLS_F_COMMITED_PLACEHOLDER".to_string(),
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
        "NUM_BYTECODE_INSTRUCTIONS_PLACEHOLDER".to_string(),
        N_INSTRUCTION_COLUMNS.to_string(),
    );
    replacements.insert(
        "N_COMMITTED_EXEC_COLUMNS_PLACEHOLDER".to_string(),
        N_COMMITTED_EXEC_COLUMNS.to_string(),
    );

    let inner_public_input = vec![];
    let outer_public_memory = build_public_memory(&outer_public_input);
    let mut inner_private_input = vec![
        F::from_usize(proof_to_prove.proof.len()),
        F::from_usize(log2_strict_usize(outer_public_memory.len())),
    ];
    inner_private_input.extend(proof_to_prove.proof.to_vec());
    inner_private_input.extend(outer_public_memory);

    let recursion_bytecode =
        compile_program_with_flags(&ProgramSource::Filepath(filepath), CompilationFlags { replacements });

    let time = Instant::now();

    let recursion_proof = prove_execution(
        &recursion_bytecode,
        (&inner_public_input, &inner_private_input),
        &vec![], // TODO precompute poseidons
        &Default::default(),
        false,
    );
    let proving_time = time.elapsed();
    verify_execution(
        &recursion_bytecode,
        &inner_public_input,
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

pub(crate) fn whir_recursion_placeholder_replacements(
    whir_config: &WhirConfig<EF>,
    base: bool,
) -> BTreeMap<String, String> {
    let mut num_queries = vec![];
    let mut ood_samples = vec![];
    let mut grinding_bits = vec![];
    let merkle_heights = (0..=whir_config.n_rounds())
        .map(|r| whir_config.merkle_tree_height(r).to_string())
        .collect::<Vec<_>>();
    let mut folding_factors = vec![];
    for round in &whir_config.round_parameters {
        num_queries.push(round.num_queries.to_string());
        ood_samples.push(round.ood_samples.to_string());
        grinding_bits.push(round.pow_bits.to_string());
        folding_factors.push(round.folding_factor.to_string());
    }
    folding_factors.push(whir_config.final_round_config().folding_factor.to_string());
    grinding_bits.push(whir_config.final_pow_bits.to_string());
    num_queries.push(whir_config.final_queries.to_string());

    let end = if base { "_BASE_PLACEHOLDER" } else { "_EXT_PLACEHOLDER" };
    let mut replacements = BTreeMap::new();
    replacements.insert(
        format!("MERKLE_HEIGHTS{}", end),
        format!("[{}]", merkle_heights.join(", ")),
    );
    replacements.insert(format!("NUM_QUERIES{}", end), format!("[{}]", num_queries.join(", ")));
    replacements.insert(
        format!("NUM_OOD_COMMIT{}", end),
        whir_config.committment_ood_samples.to_string(),
    );
    replacements.insert(format!("NUM_OODS{}", end), format!("[{}]", ood_samples.join(", ")));
    replacements.insert(
        format!("GRINDING_BITS{}", end),
        format!("[{}]", grinding_bits.join(", ")),
    );
    replacements.insert(
        format!("FOLDING_FACTORS{}", end),
        format!("[{}]", folding_factors.join(", ")),
    );
    replacements.insert(format!("N_VARS{}", end), whir_config.num_variables.to_string());
    replacements.insert(
        format!("LOG_INV_RATE{}", end),
        whir_config.starting_log_inv_rate.to_string(),
    );
    replacements.insert(
        format!("FINAL_VARS{}", end),
        whir_config.n_vars_of_final_polynomial().to_string(),
    );
    replacements.insert(
        format!("FIRST_RS_REDUCTION_FACTOR{}", end),
        whir_config.rs_domain_initial_reduction_factor.to_string(),
    );
    replacements
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
    let (constraints, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
    let mut vars_counter = Counter::new();
    let mut cache: HashMap<*const (), String> = HashMap::new();

    let mut res = format!(
        "fn evaluate_air_constraints_table_{}({}, air_alpha_powers, bus_beta, bus_alpha_powers) -> 1 {{\n",
        table.table().index() - 1,
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
        BusTable::Constant(c) => format!("embedd_in_ef({})", c.index()),
        BusTable::Variable(col) => format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, col),
    };
    let flag = format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, table.bus().selector);
    res += &format!("\n\tbuff = malloc(DIM * {});", bus_data.len());
    for (i, data) in bus_data.iter().enumerate() {
        let data_str = write_down_air_constraint_eval(data, &mut cache, &mut res, &mut vars_counter);
        res += &format!("\n\tcopy_5({}, buff + DIM * {});", data_str, i);
    }
    res += &format!(
        "\n\tmut bus_res = dot_product_ret(buff, bus_alpha_powers + DIM, {}, EE);",
        bus_data.len()
    );
    res += &format!("\n\tbus_res = add_extension_ret({}, bus_res);", table_index);
    res += "\n\tbus_res = mul_extension_ret(bus_res, bus_beta);";
    res += &format!("\n\tmut sum = add_extension_ret(bus_res, {});", flag);

    for (index, constraint_eval) in constraints_evals.iter().enumerate() {
        res += format!(
            "\n\tsum = add_extension_ret(sum, mul_extension_ret(air_alpha_powers + {} * DIM, {}));",
            index + 1,
            constraint_eval
        )
        .as_str();
    }

    res += "\n\treturn sum;";
    res += "\n}\n";
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
                    res.push_str(&format!("\t{} = opposite_extension_ret({});\n", aux_var, arg_str));
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
        res.push_str(&format!("\t{} = {}({}, {});\n", aux_var, be_func, c1, arg2_str));
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
        res.push_str(&format!("\t{} = {}({}, {});\n", aux_var, eb_func, term0, term1));
        return aux_var;
    }
    let arg1_str = write_down_air_constraint_eval(&args[0], cache, res, vars_counter);
    let arg2_str = write_down_air_constraint_eval(&args[1], cache, res, vars_counter);
    let aux_var = format!("aux_{}", vars_counter.get_next());
    res.push_str(&format!("\t{} = {}({}, {});\n", aux_var, ee_func, arg1_str, arg2_str));
    aux_var
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

#[test]
fn test_end2end_recursion() {
    run_recursion_benchmark(false);
}

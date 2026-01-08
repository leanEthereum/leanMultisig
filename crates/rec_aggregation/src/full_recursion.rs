use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;
use std::time::Instant;

use lean_compiler::{CompilationFlags, ProgramSource, compile_program, compile_program_with_flags};
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{STARTING_LOG_INV_RATE_BASE, STARTING_LOG_INV_RATE_EXTENSION, SnarkParams, whir_config_builder};
use lean_vm::*;
use multilinear_toolkit::prelude::symbolic::{SymbolicExpression, SymbolicOperation, get_symbolic_constraints};
use multilinear_toolkit::prelude::*;
use utils::{Counter, MEMORY_TABLE_INDEX};
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

fn all_air_evals_in_zk_dsl() -> String {
    let mut res = r#"fn evaluate_air_constraints(table_index, inner_evals, alpha_powers) -> 1 {
    var res;
    debug_assert table_index < 3;
    match table_index {
        0 => { res = evaluate_air_constraints_table_0(inner_evals, alpha_powers); }
        1 => { res = evaluate_air_constraints_table_1(inner_evals, alpha_powers); }
        2 => { res = evaluate_air_constraints_table_2(inner_evals, alpha_powers); }
    }  
    return res;
}
"#
    .to_string();
    res += &air_eval_in_zk_dsl(ExecutionTable::<false> {}, 0);
    res += &air_eval_in_zk_dsl(DotProductPrecompile::<false> {}, 1);
    res += &air_eval_in_zk_dsl(Poseidon16Precompile::<false> {}, 2);
    res
}

fn air_eval_in_zk_dsl<A: Air>(air: A, table_index: usize) -> String
where
    A::ExtraData: Default,
{
    let constraints = get_symbolic_constraints::<F, _>(&air);
    let mut vars_counter = Counter::new();
    let mut cache: HashMap<*const (), String> = HashMap::new();

    let mut res = format!(
        "fn evaluate_air_constraints_table_{}(inner_evals, alpha_powers) -> 1 {{\n",
        table_index
    );
    res += "\tmut sum = pointer_to_zero_vector;\n";

    for (index, constraint) in constraints.iter().enumerate() {
        res += "\n";
        let constraint_eval = write_down_air_constraint_eval(&constraint, &mut cache, &mut res, &mut vars_counter);
        res += format!(
            "\tsum = add_extension_ret(sum, mul_extension_ret(alpha_powers + {} * DIM, {}));\n",
            index + 1,
            constraint_eval
        )
        .as_str();
    }
    res += "\treturn sum;\n";
    res += "}\n";
    res
}

const AIR_INNER_VALUES_VAR: &str = "inner_evals";

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
                    let aux_var = format!("aux_{}", vars_counter.next());
                    res.push_str(&format!("\t{} = opposite_extension_ret({});\n", aux_var, arg_str));
                    return aux_var;
                }
                SymbolicOperation::Add => handle_operation_on_two(
                    args,
                    cache,
                    res,
                    vars_counter,
                    "add_base_extension_ret",
                    "add_base_extension_ret",
                    "add_extension_ret",
                    true
                ),
                SymbolicOperation::Sub => handle_operation_on_two(
                    args,
                    cache,
                    res,
                    vars_counter,
                    "sub_base_extension_ret",
                    "sub_extension_base_ret",
                    "sub_extension_ret",
                    false
                ),
                SymbolicOperation::Mul => handle_operation_on_two(
                    args,
                    cache,
                    res,
                    vars_counter,
                    "mul_base_extension_ret",
                    "mul_base_extension_ret",
                    "mul_extension_ret",
                    true
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
    be_func: &str,
    eb_func: &str,
    ee_func: &str,
    switch_args: bool,
) -> String {
    assert_eq!(args.len(), 2);
    if let SymbolicExpression::Constant(c1) = args[0] {
        let arg2_str = write_down_air_constraint_eval(&args[1], cache, res, vars_counter);
        let aux_var = format!("aux_{}", vars_counter.next());
        res.push_str(&format!("\t{} = {}({}, {});\n", aux_var, be_func, c1, arg2_str));
        return aux_var;
    }
    if let SymbolicExpression::Constant(c2) = args[1] {
        let arg1_str = write_down_air_constraint_eval(&args[0], cache, res, vars_counter);
        let aux_var = format!("aux_{}", vars_counter.next());
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
    let aux_var = format!("aux_{}", vars_counter.next());
    res.push_str(&format!("\t{} = {}({}, {});\n", aux_var, ee_func, arg1_str, arg2_str));
    return aux_var;
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

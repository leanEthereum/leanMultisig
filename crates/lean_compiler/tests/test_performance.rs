use lean_compiler::*;
use lean_vm::*;

fn test_data_dir() -> String {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    format!("{manifest_dir}/tests/test_data")
}

/// Helper to get the number of cycles for a program file
fn get_cycle_count(path: &str) -> usize {
    let bytecode = compile_program(&ProgramSource::Filepath(path.to_string()));
    let result = try_execute_bytecode(&bytecode, &[], &ExecutionWitness::empty(), false).unwrap();
    result.pcs.len()
}

#[test]
fn test_constant_if_else_optimization() {
    let path_with_conditions = format!("{}/perf_constant_if_with_conditions.py", test_data_dir());
    let path_baseline = format!("{}/perf_constant_if_baseline.py", test_data_dir());

    let cycles_with_conditions = get_cycle_count(&path_with_conditions);
    let cycles_baseline = get_cycle_count(&path_baseline);

    assert_eq!(
        cycles_with_conditions, cycles_baseline,
        "Constant if/else conditions should be eliminated at compile time.\n\
         Program with conditions: {} cycles\n\
         Baseline (no conditions): {} cycles\n\
         Expected equal cycle counts.",
        cycles_with_conditions, cycles_baseline
    );
}

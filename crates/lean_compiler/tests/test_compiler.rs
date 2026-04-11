use std::time::Instant;

use backend::BasedVectorSpace;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use utils::poseidon16_compress;

#[test]
fn test_poseidon() {
    let program = r#"
def main():
    a = 0
    b = a + 8
    c = Array(8)
    poseidon16_compress(a, b, c)

    for i in range(0, 8):
        cc = c[i]
        print(cc)
    return
   "#;
    let public_input: [F; 16] = (0..16).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&public_input, &[]), false);

    let _ = dbg!(poseidon16_compress(public_input));
}

#[test]
fn test_div_extension_field() {
    let program = r#"
DIM = 5

def main():
    n = 0
    d = n + DIM
    q = n + 2 * DIM
    computed_q_1 = div_ext_1(n, d)
    computed_q_2 = div_ext_2(n, d)
    assert_eq_ext(computed_q_2, q)
    assert_eq_ext(computed_q_1, q)
    return

def assert_eq_ext(x, y):
    for i in unroll(0, DIM):
        assert x[i] == y[i]
    return

def div_ext_1(n, d):
    quotient = Array(DIM)
    dot_product_ee(d, quotient, n)
    return quotient

def div_ext_2(n, d):
    quotient = Array(DIM)
    dot_product_ee(quotient, d, n)
    return quotient
    "#;

    let mut rng = StdRng::seed_from_u64(0);
    let n: EF = rng.random();
    let d: EF = rng.random();
    let q = n / d;
    let mut public_input = vec![];
    public_input.extend(n.as_basis_coefficients_slice());
    public_input.extend(d.as_basis_coefficients_slice());
    public_input.extend(q.as_basis_coefficients_slice());
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&public_input, &[]), false);
}

fn test_data_dir() -> String {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    format!("{manifest_dir}/tests/test_data")
}

fn find_files(dir: &str, prefix: &str, suffix: &str) -> Vec<String> {
    let mut paths: Vec<String> = std::fs::read_dir(dir)
        .expect("Failed to read test data directory")
        .filter_map(|entry| entry.ok())
        .filter_map(|entry| {
            let path = entry.path();
            let filename = path.file_name()?.to_str()?;
            if filename.starts_with(prefix) && filename.ends_with(suffix) {
                Some(path.to_string_lossy().to_string())
            } else {
                None
            }
        })
        .collect();
    paths.sort();
    paths
}

#[test]
fn test_num_files() {
    let expected_num_files = 3; // program_2.py imports foo.py and bar.py
    let path = format!("{}/program_2.py", test_data_dir());
    let bytecode = compile_program(&ProgramSource::Filepath(path));
    assert_eq!(bytecode.filepaths.len(), expected_num_files);
    assert_eq!(bytecode.source_code.len(), expected_num_files);
}

#[test]
fn test_all_errors() {
    let test_dir = test_data_dir();
    let paths = find_files(&test_dir, "error_", ".py");

    assert!(!paths.is_empty(), "No error_*.py files found");
    println!("Found {} test error programs", paths.len());

    for path in paths {
        let result = try_compile_and_run(&ProgramSource::Filepath(path.clone()), (&[], &[]), false);
        assert!(result.is_err(), "Expected error for {}, but it succeeded", path);
    }
}

#[test]
fn test_all_programs() {
    let test_dir = test_data_dir();
    let paths = find_files(&test_dir, "program_", ".py");

    assert!(!paths.is_empty(), "No program_*.py files found");
    println!("Found {} test programs", paths.len());

    // Reserve a 5-cell preamble for the programs that materialize a local
    // ONE_EF_PTR (program_15, program_166, program_179).
    let witness = ExecutionWitness {
        preamble_memory_len: 5,
        ..ExecutionWitness::default()
    };
    for path in paths {
        let bytecode = match try_compile_program(&ProgramSource::Filepath(path.clone())) {
            Ok(b) => b,
            Err(err) => panic!("Program {} failed to compile: {:?}", path, err),
        };
        if let Err(err) = try_execute_bytecode(&bytecode, &[], &witness, false) {
            panic!("Program {} failed with error: {:?}", path, err);
        }
    }
}

#[test]
fn test_reserved_function_names() {
    for name in RESERVED_FUNCTION_NAMES {
        let program = format!("def main():\n    return\ndef {name}():\n    return");
        assert!(
            try_compile_and_run(&ProgramSource::Raw(program), (&[], &[]), false).is_err(),
            "Expected error when defining function with reserved name '{name}', but it succeeded"
        );
    }
}

#[test]
fn test_dynamic_unroll_cycles() {
    // Verify that dynamic_unroll costs ~2 cycles per iteration
    for start in [0u32, 5, 50] {
        let program = format!(
            r#"
def main():
    a = 0
    end = a[0]
    expected = a[1]
    acc: Mut = 0
    for i in dynamic_unroll({start}, end, 13):
        acc = acc + i
    assert acc == expected
    return
"#
        );
        let bytecode = compile_program(&ProgramSource::Raw(program));

        let run = |end_val: u32| -> usize {
            let expected_sum = (start..end_val).map(|i| i as u64).sum::<u64>() as u32;
            let public_input = [F::new(end_val), F::new(expected_sum)];
            let result = try_execute_bytecode(&bytecode, &public_input, &ExecutionWitness::default(), false).unwrap();
            result.pcs.len()
        };

        let n_iters_a = 2000u32;
        let n_iters_b = 4000u32;
        let cycles_a = run(start + n_iters_a);
        let cycles_b = run(start + n_iters_b);
        let delta = cycles_b - cycles_a;
        let extra_iters = n_iters_b - n_iters_a;
        let expected_delta = 2 * extra_iters as usize;
        // Allow 5% tolerance for fixed overhead per activated bit
        let lo = expected_delta * 95 / 100;
        let hi = expected_delta * 105 / 100;
        assert!(delta >= lo && delta <= hi,);
    }
}

#[test]
fn debug_file_program() {
    let index = 167;
    let path = format!("{}/program_{}.py", test_data_dir(), index);
    compile_and_run(&ProgramSource::Filepath(path), (&[], &[]), false);
}

#[test]
fn test_fp_negative_offset() {
    let program = r#"
def main():
    a = Array(16)
    for i in unroll(0, 8):
        a[i] = i
    b = a - 1000
    for i in unroll(0, 1000):
        func(a, b + 1008)
    return

@inline
def func(a, b):
    poseidon16_compress(a, a, b)
    return
   "#;
    let bytecode = compile_program(&ProgramSource::Raw(program.to_string()));
    let n_cycles = execute_bytecode(&bytecode, &[], &ExecutionWitness::default(), false).n_cycles();
    assert!(n_cycles < 1100);
}

#[test]
fn test_parallel_loop() {
    let program = r#"
def main():
    n = 16
    res = Array(n)
    for i in loop(0, n):
        res[i] = factorial(10000)
    sum: Mut = 0
    for i in range(0, n):
        sum = sum + res[i]
    print(sum)
    return

def factorial(n):
    if n == 0:
        return 1
    else:
        return n * factorial(n - 1)
   "#;

    let compiled_sequencial = compile_program(&ProgramSource::Raw(program.replace("loop", "range")));
    let compiled_parallel = compile_program(&ProgramSource::Raw(program.replace("loop", "parallel_range")));

    let time_sequential = Instant::now();
    let exec_seq = execute_bytecode(&compiled_sequencial, &[], &ExecutionWitness::default(), false);
    let duration_sequential = time_sequential.elapsed();
    let time_parallel = Instant::now();
    let exec_par = execute_bytecode(&compiled_parallel, &[], &ExecutionWitness::default(), false);
    let duration_parallel = time_parallel.elapsed();

    assert_eq!(exec_seq.metadata.stdout, exec_par.metadata.stdout);
    assert_eq!(exec_seq.n_cycles(), exec_par.n_cycles());
    assert_eq!(exec_seq.runtime_memory_size, exec_par.runtime_memory_size);

    println!("Sequential duration: {:.4}s", duration_sequential.as_secs_f64());
    println!("Parallel duration: {:.4}s", duration_parallel.as_secs_f64());
    println!(
        "Speedup: {:.2}x",
        duration_sequential.as_secs_f64() / duration_parallel.as_secs_f64()
    );
}

#[test]
fn debug_str_program() {
    let program = r#"
def main():
    a = 2
    b = 3
    for i in unroll(0, a * b):
        print(i)
    return
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

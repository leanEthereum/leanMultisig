use backend::BasedVectorSpace;
use lean_compiler::*;
use lean_vm::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon16_compress;

#[test]
fn test_poseidon() {
    let program = r#"
def main():
    a = NONRESERVED_PROGRAM_INPUT_START
    b = a + 8
    c = Array(8)
    poseidon16(a, b, c)

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
    n = NONRESERVED_PROGRAM_INPUT_START
    d = NONRESERVED_PROGRAM_INPUT_START + DIM
    q = NONRESERVED_PROGRAM_INPUT_START + 2 * DIM
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

    for path in paths {
        if let Err(err) = try_compile_and_run(&ProgramSource::Filepath(path.clone()), (&[], &[]), false) {
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
    a = NONRESERVED_PROGRAM_INPUT_START
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
            let result = try_execute_bytecode(&bytecode, &public_input, &ExecutionWitness::empty(), false).unwrap();
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
    poseidon16(a, a, b)
    return
   "#;
    let bytecode = compile_program(&ProgramSource::Raw(program.to_string()));
    let n_cycles = execute_bytecode(&bytecode, &[], &ExecutionWitness::empty(), false).n_cycles();
    assert!(n_cycles < 1100);
}

#[test]
fn debug_str_program_good() {
    let program = r#"
def main():
    n = 10000
    array = Array(n * 8)
    for i in range(0, 16):
        array[i] = 0
    for i in unroll(2, n):
        poseidon16(array + (i - 2) * 8, array + (i - 1) * 8, array + i * 8)
    print(array + (n - 1) * 8)
    return
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

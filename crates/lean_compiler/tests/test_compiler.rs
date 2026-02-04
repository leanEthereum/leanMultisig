use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::BasedVectorSpace;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon16_permute;

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

    let _ = dbg!(poseidon16_permute(public_input));
}

#[test]
fn test_div_extension_field() {
    let program = r#"
# Dot product precompile:
BE = 1  # base-extension
EE = 0  # extension-extension
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
    dot_product(d, quotient, n, 1, EE)
    return quotient

def div_ext_2(n, d):
    quotient = Array(DIM)
    dot_product(quotient, d, n, 1, EE)
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
fn debug_file_program() {
    let index = 167;
    let path = format!("{}/program_{}.py", test_data_dir(), index);
    compile_and_run(&ProgramSource::Filepath(path), (&[], &[]), false);
}

#[test]
fn debug_str_program() {
    let program = r#"
def main():
    return
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn bug() {
    let program = r#"
def main():
    three = double(1) + 1
    assert three == 3
    return

def double(a: Const):
    return a + a
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

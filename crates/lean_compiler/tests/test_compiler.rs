use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::BasedVectorSpace;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon16_permute;

#[test]
fn test_poseidon() {
    let program = r#"
    fn main() {
        a = public_input_start;
        b = a + 8;
        c = malloc(2*8);
        poseidon16(a, b, c, 0);

        for i in 0..8 {
            cc = c[i];
            print(cc);
        }
        for i in 0..8 {
            dd = c[i+8];
            print(dd);
        }
        return;
    }
   "#;
    let public_input: [F; 16] = (0..16).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&public_input, &[]), false);

    let _ = dbg!(poseidon16_permute(public_input));
}

#[test]
fn test_div_extension_field() {
    let program = r#"
        // Dot product precompile:
        const BE = 1; // base-extension
        const EE = 0; // extension-extension

        const DIM = 5;
        fn main() {
            n = public_input_start;
            d = public_input_start + DIM;
            q = public_input_start + 2 * DIM;
            computed_q_1 = div_ext_1(n, d);
            computed_q_2 = div_ext_2(n, d);
            assert_eq_ext(computed_q_2, q);
            assert_eq_ext(computed_q_1, q);
            return;
        }

        fn assert_eq_ext(x, y) {
            for i in 0..DIM unroll {
                assert x[i] == y[i];
            }
            return;
        }

        fn div_ext_1(n, d) -> 1 {
            quotient = malloc(DIM);
            dot_product(d, quotient, n, 1, EE);
            return quotient;
        }

        fn div_ext_2(n, d) -> 1 {
            quotient = malloc(DIM);
            dot_product(quotient, d, n, 1, EE);
            return quotient;
        }
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
    let expected_num_files = 3; // program_2.snark imports foo.snark and bar.snark
    let path = format!("{}/program_2.snark", test_data_dir());
    let bytecode = compile_program(&ProgramSource::Filepath(path));
    assert_eq!(bytecode.filepaths.len(), expected_num_files);
    assert_eq!(bytecode.source_code.len(), expected_num_files);
}

#[test]
fn test_all_errors() {
    let test_dir = test_data_dir();
    let paths = find_files(&test_dir, "error_", ".snark");

    assert!(!paths.is_empty(), "No error_*.snark files found");
    println!("Found {} test error programs", paths.len());

    for path in paths {
        let result = try_compile_and_run(&ProgramSource::Filepath(path.clone()), (&[], &[]), false);
        assert!(result.is_err(), "Expected error for {}, but it succeeded", path);
    }
}

#[test]
fn test_all_programs() {
    let test_dir = test_data_dir();
    let paths = find_files(&test_dir, "program_", ".snark");

    assert!(!paths.is_empty(), "No program_*.snark files found");
    println!("Found {} test programs", paths.len());

    for path in paths {
        if let Err(err) = try_compile_and_run(&ProgramSource::Filepath(path.clone()), (&[], &[]), false) {
            panic!("Program {} failed with error: {:?}", path, err);
        }
    }
}

// #[test]
// fn test_given_program() {
//     let index = 1;
//     let path = format!("{}/program_{}.snark", test_data_dir(), index);
//     compile_and_run(&ProgramSource::Filepath(path), (&[], &[]), false);
// }

#[test]
fn debug() {
    let program = r#"
    fn main() {
        mut s = malloc(1);
        s[0] = 10;
        b = malloc(1);
        b[0] = 20;
        s = add_refs(s, b);
        assert s[0] == 30;
        return;
    }

    fn add_refs(a, b) -> 1 {
        c = malloc(1);
        c[0] = a[0] + b[0];
        return c;
    }
        
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

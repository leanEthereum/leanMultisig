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

#[test]
fn test_reserved_function_names() {
    #[rustfmt::skip]
    let reserved_names = ["print", "malloc", "private_input_start", "panic", "len", "log2_ceil", "next_multiple_of", "saturating_sub", "hint_decompose_bits_xmss", "hint_decompose_bits", "poseidon16", "dot_product"];

    for name in reserved_names {
        let program = format!("fn main() {{ return; }} fn {name}() {{ return; }}");
        assert!(
            try_compile_and_run(&ProgramSource::Raw(program), (&[], &[]), false).is_err(),
            "Expected error when defining function with reserved name '{name}', but it succeeded"
        );
    }
}

#[test]
fn debug_file_program() {
    let index = 1;
    let path = format!("{}/program_{}.snark", test_data_dir(), index);
    compile_and_run(&ProgramSource::Filepath(path), (&[], &[]), false);
}

#[test]
fn debug_pass() {
    let program = r#"
    fn main() {
        var mut two;
        if 1 == 1 {
            two = 2;
        } else {
            two = 3;
        }
        print(two);
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}


#[test]
fn test_panics() {
    let program = r#"
    fn main() {
        var mut two;
        if 1 == 1 {
            two = 2;
        } else {
            panic();
        }
        print(two);
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

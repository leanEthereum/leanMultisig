use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{init_tracing, poseidon16_compress};

#[test]
fn test_zk_vm_all_precompiles() {
    test_zk_vm_all_precompiles_helper(false);
}

#[test]
#[ignore] // slow test
fn test_zk_vm_fuzzing() {
    test_zk_vm_all_precompiles_helper(true);
}

fn test_zk_vm_all_precompiles_helper(fuzzing: bool) {
    let program_str = r#"
DIM = 5
N = 11
DIGEST_LEN = 8

# Dot product precompile:
BE = 1  # base-extension
EE = 0  # extension-extension

def main():
    pub_start = NONRESERVED_PROGRAM_INPUT_START
    poseidon16(pub_start + 4 * DIGEST_LEN, pub_start + 5 * DIGEST_LEN, pub_start + 6 * DIGEST_LEN)
    dot_product(pub_start + 88, pub_start + 88 + N, pub_start + 1000, N, BE)
    dot_product(pub_start + 88 + N, pub_start + 88 + N * (DIM + 1), pub_start + 1000 + DIM, N, EE)
    c: Mut = 0
    for i in range(0,100):
        c += 1
    assert c == 100

    return
"#;

    const N: usize = 11;

    let mut rng = StdRng::seed_from_u64(0);
    let mut public_input = F::zero_vec(1 << 13);

    let poseidon_16_compress_input: [F; 16] = rng.random();
    public_input[32..48].copy_from_slice(&poseidon_16_compress_input);
    public_input[48..56].copy_from_slice(&poseidon16_compress(poseidon_16_compress_input)[..8]);

    let poseidon_24_input: [F; 24] = rng.random();
    public_input[56..80].copy_from_slice(&poseidon_24_input);

    let dot_product_slice_base: [F; N] = rng.random();
    let dot_product_slice_ext_a: [EF; N] = rng.random();
    let dot_product_slice_ext_b: [EF; N] = rng.random();

    public_input[88..][..N].copy_from_slice(&dot_product_slice_base);
    public_input[88 + N..][..N * DIMENSION].copy_from_slice(
        &dot_product_slice_ext_a
            .iter()
            .flat_map(|&x| x.as_basis_coefficients_slice().to_vec())
            .collect::<Vec<F>>(),
    );
    public_input[88 + N + N * DIMENSION..][..N * DIMENSION].copy_from_slice(
        &dot_product_slice_ext_b
            .iter()
            .flat_map(|&x| x.as_basis_coefficients_slice().to_vec())
            .collect::<Vec<F>>(),
    );
    let dot_product_base_ext: EF = dot_product(dot_product_slice_ext_a.into_iter(), dot_product_slice_base.into_iter());
    let dot_product_ext_ext: EF = dot_product(dot_product_slice_ext_a.into_iter(), dot_product_slice_ext_b.into_iter());

    public_input[1000..][..DIMENSION].copy_from_slice(dot_product_base_ext.as_basis_coefficients_slice());
    public_input[1000 + DIMENSION..][..DIMENSION].copy_from_slice(dot_product_ext_ext.as_basis_coefficients_slice());

    let slice_a: [F; 3] = rng.random();
    let slice_b: [EF; 3] = rng.random();
    let poly_eq = MultilinearPoint(slice_b.to_vec())
        .eq_poly_outside(&MultilinearPoint(slice_a.iter().map(|&x| EF::from(x)).collect()));
    public_input[1100..][..3].copy_from_slice(&slice_a);
    public_input[1100 + 3..][..3 * DIMENSION].copy_from_slice(
        slice_b
            .iter()
            .flat_map(|&x| x.as_basis_coefficients_slice().to_vec())
            .collect::<Vec<F>>()
            .as_slice(),
    );
    public_input[1100 + 3 + 3 * DIMENSION..][..DIMENSION].copy_from_slice(poly_eq.as_basis_coefficients_slice());

    test_zk_vm_helper(program_str, (&public_input, &[]), fuzzing);
}

#[test]
fn test_small_memory() {
    let program_str = r#"
def main():
    a = Array(1)
    for i in unroll(0, 2**17):
        a[0] = 1 * 2
    return
"#;

    test_zk_vm_helper(program_str, (&[], &[]), false);
}

#[test]
fn test_prove_fibonacci() {
    if std::env::var("FIB_TRACING") == Ok("true".to_string()) {
        init_tracing();
    }
    let n = std::env::var("FIB_N")
        .unwrap_or("10000".to_string())
        .parse::<usize>()
        .unwrap();
    let program_str = r#"
N = FIB_N_PLACEHOLDER
STEPS = 10000  # N should be a multiple of STEPS
N_STEPS = N / STEPS

def main():
    x, y = fibonacci_step(0, 1, N_STEPS)
    print(x)
    return

def fibonacci_step(a, b, steps_remaining):
    if steps_remaining == 0:
        return a, b
    new_a, new_b = fibonacci_const(a, b, STEPS)
    res_a, res_b = fibonacci_step(new_a, new_b, steps_remaining - 1)
    return res_a, res_b

def fibonacci_const(a, b, n: Const):
    buff = Array(n + 2)
    buff[0] = a
    buff[1] = b
    for j in unroll(2, n + 2):
        buff[j] = buff[j - 1] + buff[j - 2]
    return buff[n], buff[n + 1]
"#;
    let program_str = program_str.replace("FIB_N_PLACEHOLDER", &n.to_string());

    test_zk_vm_helper(&program_str, (&[F::ZERO; 1 << 14], &[]), false);
}

fn test_zk_vm_helper(program_str: &str, (public_input, private_input): (&[F], &[F]), fuzzing: bool) {
    if !fuzzing {
        utils::init_tracing();
    }
    let bytecode = compile_program(&ProgramSource::Raw(program_str.to_string()));
    let time = std::time::Instant::now();
    let starting_log_inv_rate = 1;
    let proof = prove_execution(
        &bytecode,
        (public_input, private_input),
        &vec![],
        &default_whir_config(starting_log_inv_rate),
        false,
    );
    let proof_time = time.elapsed();
    verify_execution(
        &bytecode,
        public_input,
        proof.proof.clone(),
        &default_whir_config(starting_log_inv_rate),
    )
    .unwrap();
    println!("{}", proof.exec_summary);
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());

    if fuzzing {
        println!("Starting fuzzing...");
        let mut percent = 0;
        for i in 0..proof.proof.len() {
            let new_percent = i * 100 / proof.proof.len();
            if new_percent != percent {
                percent = new_percent;
                println!("{}%", percent);
            }
            let mut fuzzed_proof = proof.proof.clone();
            fuzzed_proof[i] += F::ONE;
            let verify_result = verify_execution(
                &bytecode,
                public_input,
                fuzzed_proof,
                &default_whir_config(starting_log_inv_rate),
            );
            assert!(verify_result.is_err(), "Fuzzing failed at index {}", i);
        }
    }
}

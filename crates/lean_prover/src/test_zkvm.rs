use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use backend::*;
use lean_compiler::*;
use lean_vm::*;
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

def main():
    pub_start = NONRESERVED_PROGRAM_INPUT_START
    poseidon16(pub_start + 4 * DIGEST_LEN, pub_start + 5 * DIGEST_LEN, pub_start + 6 * DIGEST_LEN)

    # Base-extension dot product: sum_i base[i] * ext_a[i] -> result
    base_ptr = pub_start + 88
    ext_a_ptr = pub_start + 88 + N
    res_be = pub_start + 1000
    acc_be: Mut = Array(DIM)
    mul_be(base_ptr, ext_a_ptr, acc_be)
    for i in unroll(1, N - 1):
        tmp = Array(DIM)
        mul_be(base_ptr + i, ext_a_ptr + i * DIM, tmp)
        new_acc_be = Array(DIM)
        add_ee(acc_be, tmp, new_acc_be)
        acc_be = new_acc_be
    last_be = Array(DIM)
    mul_be(base_ptr + N - 1, ext_a_ptr + (N - 1) * DIM, last_be)
    add_ee(acc_be, last_be, res_be)

    # Extension-extension dot product: sum_i ext_a[i] * ext_b[i] -> result
    ext_b_ptr = pub_start + 88 + N * (DIM + 1)
    res_ee = pub_start + 1000 + DIM
    acc_ee: Mut = Array(DIM)
    mul_ee(ext_a_ptr, ext_b_ptr, acc_ee)
    for i in unroll(1, N - 1):
        tmp2 = Array(DIM)
        mul_ee(ext_a_ptr + i * DIM, ext_b_ptr + i * DIM, tmp2)
        new_acc_ee = Array(DIM)
        add_ee(acc_ee, tmp2, new_acc_ee)
        acc_ee = new_acc_ee
    last_ee = Array(DIM)
    mul_ee(ext_a_ptr + (N - 1) * DIM, ext_b_ptr + (N - 1) * DIM, last_ee)
    add_ee(acc_ee, last_ee, res_ee)

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
    verify_execution(&bytecode, public_input, proof.raw_proof().unwrap()).unwrap();
    println!("{}", proof.metadata.display());
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());

    if fuzzing {
        println!("Starting fuzzing...");
        let mut percent = 0;
        let raw_proof = proof.raw_proof().unwrap();
        for i in 0..raw_proof.len() {
            let new_percent = i * 100 / raw_proof.len();
            if new_percent != percent {
                percent = new_percent;
                println!("{}%", percent);
            }
            let mut fuzzed_proof = raw_proof.clone();
            fuzzed_proof[i] += F::ONE;
            let verify_result = verify_execution(&bytecode, public_input, fuzzed_proof);
            assert!(verify_result.is_err(), "Fuzzing failed at index {}", i);
        }
    }
}

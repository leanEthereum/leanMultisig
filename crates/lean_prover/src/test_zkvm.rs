use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use backend::*;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use utils::{init_tracing, poseidon16_compress};

#[test]
#[ignore = "benchmark; run with `cargo test --release -p lean_prover bench_poseidon -- --ignored --nocapture`"]
fn bench_poseidon() {
    utils::init_tracing();
    let n_poseidon_calls = std::env::var("POSEIDON_BENCH_CALLS")
        .ok()
        .map(|raw| raw.parse::<usize>().expect("POSEIDON_BENCH_CALLS must be a usize"))
        .unwrap_or(1);
    let program_str = format!(
        r#"
N_POSEIDON_CALLS = {n_poseidon_calls}
DIGEST_LEN = 8

def main():
    input_left = 0
    input_right = DIGEST_LEN
    outputs = Array(N_POSEIDON_CALLS * DIGEST_LEN)
    for i in dynamic_unroll(0, N_POSEIDON_CALLS, 20):
        out = outputs + i * DIGEST_LEN
        poseidon16_compress(input_left, input_right, out)
    return
"#
    );

    let public_input: Vec<F> = (0..16).map(F::new).collect();
    let bytecode = compile_program(&ProgramSource::Raw(program_str));
    let witness = ExecutionWitness::default();
    let starting_log_inv_rate = 1;

    let time = std::time::Instant::now();
    let proof = prove_execution(
        &bytecode,
        &public_input,
        &witness,
        &default_whir_config(starting_log_inv_rate),
        false,
    );
    let proof_time = time.elapsed();
    let proof_size_kib = proof.proof.proof_size_fe() * F::bits() / (8 * 1024);

    println!("{}", proof.metadata.display());
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
    println!("Proof size: {proof_size_kib} KiB");

    verify_execution(&bytecode, &public_input, proof.proof).unwrap();
}

#[test]
#[ignore = "benchmark; run with `cargo test --release -p lean_prover bench_sha256_compress -- --ignored --nocapture`"]
fn bench_sha256_compress() {
    utils::init_tracing();
    let n_sha_calls = std::env::var("SHA256_BENCH_CALLS")
        .ok()
        .map(|raw| raw.parse::<usize>().expect("SHA256_BENCH_CALLS must be a usize"))
        .unwrap_or(1);
    const SHA_FIXTURE_STRIDE: usize = SHA256_STATE_LIMBS + SHA256_BLOCK_LIMBS + SHA256_STATE_LIMBS;
    let program_str = format!(
        r#"
N_SHA_CALLS = {n_sha_calls}
SHA_FIXTURE_STRIDE = 64

def main():
    for j in unroll(0, N_SHA_CALLS):
        base = j * SHA_FIXTURE_STRIDE
        state = base
        block = base + 16
        expected = base + 48
        out = Array(16)
        sha256_compress(state, block, out)

        for i in unroll(0, 16):
            assert out[i] == expected[i]
    return
"#
    );

    let mut public_input = vec![F::ZERO; n_sha_calls * SHA_FIXTURE_STRIDE];
    let expected = words_to_field_limbs_le(sha256_compress_words(SHA256_IV, SHA256_ABC_BLOCK));
    for j in 0..n_sha_calls {
        let base = j * SHA_FIXTURE_STRIDE;
        public_input[base..base + SHA256_STATE_LIMBS].copy_from_slice(&words_to_field_limbs_le(SHA256_IV));
        public_input[base + 16..base + 16 + SHA256_BLOCK_LIMBS]
            .copy_from_slice(&words_to_field_limbs_le(SHA256_ABC_BLOCK));
        public_input[base + 48..base + 48 + SHA256_STATE_LIMBS].copy_from_slice(&expected);
    }

    let bytecode = compile_program(&ProgramSource::Raw(program_str));
    let witness = ExecutionWitness::default();
    let starting_log_inv_rate = 1;

    let time = std::time::Instant::now();
    let proof = prove_execution(
        &bytecode,
        &public_input,
        &witness,
        &default_whir_config(starting_log_inv_rate),
        false,
    );
    let proof_time = time.elapsed();
    let proof_size_kib = proof.proof.proof_size_fe() * F::bits() / (8 * 1024);

    println!("{}", proof.metadata.display());
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
    println!("Proof size: {proof_size_kib} KiB");

    verify_execution(&bytecode, &public_input, proof.proof).unwrap();
}

#[test]
fn test_zk_vm_all_precompiles() {
    let program_str = r#"
DIM = 5
N = 11
M = 3
DIGEST_LEN = 8

def main():
    pub_start = 0
    poseidon16_compress(pub_start + 4 * DIGEST_LEN, pub_start + 5 * DIGEST_LEN, pub_start + 6 * DIGEST_LEN)

    # Keep the SHA fixture away from the extension-op fixture ranges below.
    sha_state = pub_start + 1400
    sha_block = sha_state + 16
    sha_expected = sha_block + 32
    sha_out = Array(16)
    sha256_compress(sha_state, sha_block, sha_out)
    for i in unroll(0, 16):
        assert sha_out[i] == sha_expected[i]

    base_ptr = pub_start + 88
    ext_a_ptr = pub_start + 88 + N
    ext_b_ptr = pub_start + 88 + N * (DIM + 1)

    # dot_product_be: sum_i base[i] * ext_a[i]
    dot_product_be(base_ptr, ext_a_ptr, pub_start + 1000, N)

    # dot_product_ee: sum_i ext_a[i] * ext_b[i]
    dot_product_ee(ext_a_ptr, ext_b_ptr, pub_start + 1000 + DIM, N)

    # add_be: sum_i (base[i] + ext_a[i])
    add_be(base_ptr, ext_a_ptr, pub_start + 1200, N)

    # add_ee: sum_i (ext_a[i] + ext_b[i])
    add_ee(ext_a_ptr, ext_b_ptr, pub_start + 1200 + DIM, N)

    # poly_eq_be: prod_i (a[i]*b[i] + (1-a[i])*(1-b[i])) with base a, ext b
    slice_a_ptr = pub_start + 1100
    slice_b_ptr = pub_start + 1100 + M
    poly_eq_be(slice_a_ptr, slice_b_ptr, pub_start + 1100 + M + M * DIM, M)

    # poly_eq_ee: prod_i (a[i]*b[i] + (1-a[i])*(1-b[i])) with ext a, ext b
    poly_eq_ee(ext_a_ptr, ext_b_ptr, pub_start + 1300, N)

    c: Mut = 0
    for i in range(0,100):
        c += 1
    assert c == 100

    return
"#;

    const N: usize = 11;
    const M: usize = 3;

    let mut rng = StdRng::seed_from_u64(0);
    let mut public_input = F::zero_vec(1 << 13);

    // Poseidon test data
    let poseidon_16_compress_input: [F; 16] = rng.random();
    public_input[32..48].copy_from_slice(&poseidon_16_compress_input);
    public_input[48..56].copy_from_slice(&poseidon16_compress(poseidon_16_compress_input)[..8]);
    let poseidon_24_input: [F; 24] = rng.random();
    public_input[56..80].copy_from_slice(&poseidon_24_input);

    // SHA256 compression test data: IV + padded "abc" block.
    // This mirrors the program's pub_start + 1400 offset; public_input is 2^13 cells,
    // so the state, block, and expected digest all fit in the public memory prefix.
    let sha_state_ptr = 1400;
    let sha_block_ptr = sha_state_ptr + SHA256_STATE_LIMBS;
    let sha_expected_ptr = sha_block_ptr + SHA256_BLOCK_LIMBS;
    public_input[sha_state_ptr..sha_state_ptr + SHA256_STATE_LIMBS]
        .copy_from_slice(&words_to_field_limbs_le(SHA256_IV));
    public_input[sha_block_ptr..sha_block_ptr + SHA256_BLOCK_LIMBS]
        .copy_from_slice(&words_to_field_limbs_le(SHA256_ABC_BLOCK));
    let sha_expected = words_to_field_limbs_le(sha256_compress_words(SHA256_IV, SHA256_ABC_BLOCK));
    public_input[sha_expected_ptr..sha_expected_ptr + SHA256_STATE_LIMBS].copy_from_slice(&sha_expected);

    // Extension op operands: base[N], ext_a[N], ext_b[N]
    let base_slice: [F; N] = rng.random();
    let ext_a_slice: [EF; N] = rng.random();
    let ext_b_slice: [EF; N] = rng.random();

    let ef_to_f = |slice: &[EF]| -> Vec<F> {
        slice
            .iter()
            .flat_map(|x| x.as_basis_coefficients_slice().to_vec())
            .collect()
    };

    public_input[88..][..N].copy_from_slice(&base_slice);
    public_input[88 + N..][..N * DIMENSION].copy_from_slice(&ef_to_f(&ext_a_slice));
    public_input[88 + N + N * DIMENSION..][..N * DIMENSION].copy_from_slice(&ef_to_f(&ext_b_slice));

    // dot_product_be result at 1000
    let dot_product_be_result: EF = dot_product(ext_a_slice.into_iter(), base_slice.into_iter());
    public_input[1000..][..DIMENSION].copy_from_slice(dot_product_be_result.as_basis_coefficients_slice());

    // dot_product_ee result at 1005
    let dot_product_ee_result: EF = dot_product(ext_a_slice.into_iter(), ext_b_slice.into_iter());
    public_input[1000 + DIMENSION..][..DIMENSION].copy_from_slice(dot_product_ee_result.as_basis_coefficients_slice());

    // add_be result at 1200: sum_i (EF::from(base[i]) + ext_a[i])
    let add_be_result: EF = (0..N)
        .map(|i| EF::from(base_slice[i]) + ext_a_slice[i])
        .fold(EF::ZERO, |a, b| a + b);
    public_input[1200..][..DIMENSION].copy_from_slice(add_be_result.as_basis_coefficients_slice());

    // add_ee result at 1205: sum_i (ext_a[i] + ext_b[i])
    let add_ee_result: EF = (0..N)
        .map(|i| ext_a_slice[i] + ext_b_slice[i])
        .fold(EF::ZERO, |a, b| a + b);
    public_input[1200 + DIMENSION..][..DIMENSION].copy_from_slice(add_ee_result.as_basis_coefficients_slice());

    // poly_eq_be operands: slice_a[M] (base), slice_b[M] (ext) at 1100
    let slice_a: [F; M] = rng.random();
    let slice_b: [EF; M] = rng.random();
    public_input[1100..][..M].copy_from_slice(&slice_a);
    public_input[1100 + M..][..M * DIMENSION].copy_from_slice(&ef_to_f(&slice_b));

    // poly_eq_be result at 1100 + M + M*DIM = 1118
    let poly_eq_be_result = MultilinearPoint(slice_b.to_vec())
        .eq_poly_outside(&MultilinearPoint(slice_a.iter().map(|&x| EF::from(x)).collect()));
    public_input[1100 + M + M * DIMENSION..][..DIMENSION]
        .copy_from_slice(poly_eq_be_result.as_basis_coefficients_slice());

    // poly_eq_ee result at 1300: prod_i (ext_a[i]*ext_b[i] + (1-ext_a[i])*(1-ext_b[i]))
    let poly_eq_ee_result: EF = (0..N)
        .map(|i| ext_a_slice[i] * ext_b_slice[i] + (EF::ONE - ext_a_slice[i]) * (EF::ONE - ext_b_slice[i]))
        .fold(EF::ONE, |acc, x| acc * x);
    public_input[1300..][..DIMENSION].copy_from_slice(poly_eq_ee_result.as_basis_coefficients_slice());

    test_zk_vm_helper(program_str, &public_input);
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

    test_zk_vm_helper(program_str, &[]);
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

    test_zk_vm_helper(&program_str, &[F::ZERO; 1 << 14]);
}

fn test_zk_vm_helper(program_str: &str, public_input: &[F]) {
    utils::init_tracing();
    let bytecode = compile_program(&ProgramSource::Raw(program_str.to_string()));
    let time = std::time::Instant::now();
    let starting_log_inv_rate = 1;
    let witness = ExecutionWitness::default();
    let proof = prove_execution(
        &bytecode,
        public_input,
        &witness,
        &default_whir_config(starting_log_inv_rate),
        false,
    );
    let proof_time = time.elapsed();
    verify_execution(&bytecode, public_input, proof.proof).unwrap();
    println!("{}", proof.metadata.display());
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
}

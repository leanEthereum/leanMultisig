use lean_compiler::*;
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution, whir_config_builder};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{poseidon16_permute, poseidon24_permute};

#[test]
fn test_zk_vm_all_precompiles() {
    let program_str = r#"
    const DIM = 5;
    const COMPRESSION = 1;
    const PERMUTATION = 0;
    const N = 11;
    fn main() {
        pub_start = public_input_start;
        pub_start_vec = pub_start / 8;

        poseidon16(pub_start_vec, pub_start_vec + 1, pub_start_vec + 2, PERMUTATION);
        poseidon16(pub_start_vec + 4, pub_start_vec + 5, pub_start_vec + 6, COMPRESSION);
        poseidon24(pub_start_vec + 7, pub_start_vec + 9, pub_start_vec + 10);
        dot_product_be(pub_start + 88, pub_start + 88 + N, pub_start + 1000, N);
        dot_product_ee(pub_start + 88 + N, pub_start + 88 + N * (DIM + 1), pub_start + 1000 + DIM, N);
        
        return;
    }
   "#;

    const N: usize = 11;

    let mut rng = StdRng::seed_from_u64(0);
    let mut public_input = F::zero_vec(1 << 13);

    let poseidon_16_perm_input: [F; 16] = rng.random();
    public_input[..16].copy_from_slice(&poseidon_16_perm_input);
    public_input[16..32].copy_from_slice(&poseidon16_permute(poseidon_16_perm_input));

    let poseidon_16_compress_input: [F; 16] = rng.random();
    public_input[32..48].copy_from_slice(&poseidon_16_compress_input);
    public_input[48..56].copy_from_slice(&poseidon16_permute(poseidon_16_compress_input)[..8]);

    let poseidon_24_input: [F; 24] = rng.random();
    public_input[56..80].copy_from_slice(&poseidon_24_input);
    public_input[80..88].copy_from_slice(&poseidon24_permute(poseidon_24_input)[16..]);

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

    test_zk_vm_helper(program_str, (&public_input, &[]), 0);
}

#[test]
fn test_prove_fibonacci() {
    let program_str = r#"
    const N = FIB_N_PLACEHOLDER;
    const STEPS = 10000; // N should be a multiple of STEPS
    const N_STEPS = N / STEPS;

    fn main() {
        x, y = fibonacci_step(0, 1, N_STEPS);
        print(x);
        return;
    }

    fn fibonacci_step(a, b, steps_remaining) -> 2 {
        if steps_remaining == 0 {
            return a, b;
        }
        new_a, new_b = fibonacci_const(a, b, STEPS);
        res_a, res_b = fibonacci_step(new_a, new_b, steps_remaining - 1);
        return res_a, res_b;
    }

    fn fibonacci_const(a, b, const n) -> 2 {
        buff = malloc(n + 2);
        buff[0] = a;
        buff[1] = b;
        for j in 2..n + 2 unroll {
            buff[j] = buff[j - 1] + buff[j - 2];
        }
        return buff[n], buff[n + 1];
    }
   "#;

    let n = std::env::var("FIB_N")
        .unwrap_or("100000".to_string())
        .parse::<usize>()
        .unwrap();
    let program_str = program_str.replace("FIB_N_PLACEHOLDER", &n.to_string());

    test_zk_vm_helper(&program_str, (&[F::ZERO; 1 << 14], &[]), 0);
}

fn test_zk_vm_helper(program_str: &str, (public_input, private_input): (&[F], &[F]), no_vec_runtime_memory: usize) {
    utils::init_tracing();
    let bytecode = compile_program(program_str.to_string());
    let time = std::time::Instant::now();
    let (proof_data, _, summary) = prove_execution(
        &bytecode,
        (public_input, private_input),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
        (&vec![], &vec![]),
    );
    let proof_time = time.elapsed();
    verify_execution(&bytecode, public_input, proof_data, whir_config_builder()).unwrap();
    println!("{summary}");
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
}

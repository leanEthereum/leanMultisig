static FIBONNACI_PROGRAM: &str = r#"
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

use crate::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon16_permute;

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
    const DIM = 5;
    const COMPRESSION = 1;
    const PERMUTATION = 0;
    const N = 11;
    const MERKLE_HEIGHT_1 = 10;
    const LEAF_POS_1 = 781;
    const MERKLE_HEIGHT_2 = 15;
    const LEAF_POS_2 = 178;
    const VECTOR_LEN = 8;
    fn main() {
        pub_start = public_input_start;
        poseidon16(pub_start, pub_start + VECTOR_LEN, pub_start + 2 * VECTOR_LEN, PERMUTATION);
        poseidon16(pub_start + 4 * VECTOR_LEN, pub_start + 5 * VECTOR_LEN, pub_start + 6 * VECTOR_LEN, COMPRESSION);
        dot_product_be(pub_start + 88, pub_start + 88 + N, pub_start + 1000, N);
        dot_product_ee(pub_start + 88 + N, pub_start + 88 + N * (DIM + 1), pub_start + 1000 + DIM, N);
        fourty = 40;
        poseidon24(0, 0, fourty);
        poseidon24(0, 0, fourty);
        
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
    let mut poseidon16_compressed_output = poseidon16_permute(poseidon_16_compress_input)[..8].to_vec();
    for i in 0..8 {
        poseidon16_compressed_output[i] += poseidon_16_compress_input[i];
    }
    public_input[48..56].copy_from_slice(&poseidon16_compressed_output);

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
fn test_prove_fibonacci() {
    let n = std::env::var("FIB_N")
        .unwrap_or("10000".to_string())
        .parse::<usize>()
        .unwrap();
    let program_str = FIBONNACI_PROGRAM.replace("FIB_N_PLACEHOLDER", &n.to_string());

    test_zk_vm_helper(&program_str, (&[F::ZERO; 1 << 14], &[]), false);
}

fn test_zk_vm_helper(program_str: &str, (public_input, private_input): (&[F], &[F]), fuzzing: bool) {
    if !fuzzing {
        utils::init_tracing();
    }
    let bytecode = compile_program(program_str.to_string());
    let (proof, _) = prove_execution(&bytecode, (public_input, private_input), false, &vec![], &vec![]);
    verify_execution(&bytecode, public_input, proof.clone()).unwrap();

    if fuzzing {
        println!("Starting fuzzing...");
        let mut percent = 0;
        for i in 0..proof.proof_data.len() {
            let new_percent = i * 100 / proof.proof_data.len();
            if new_percent != percent {
                percent = new_percent;
                println!("{}%", percent);
            }
            let mut fuzzed_proof = proof.clone();
            fuzzed_proof.proof_data[i] += F::ONE;
            let verify_result = verify_execution(&bytecode, public_input, fuzzed_proof);
            assert!(verify_result.is_err(), "Fuzzing failed at index {}", i);
        }
    }
}

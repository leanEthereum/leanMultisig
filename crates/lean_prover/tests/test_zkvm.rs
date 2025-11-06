use lean_compiler::*;
use lean_prover::{
    prove_execution::prove_execution, verify_execution::verify_execution, whir_config_builder,
};
use lean_vm::*;
use p3_field::PrimeCharacteristicRing;

#[test]
fn test_zk_vm_all_precompiles() {
    let program_str = r#"
    const DIM = 5;
    const SECOND_POINT = 2;
    const SECOND_N_VARS = 7;
    const COMPRESSION = 1;
    const PERMUTATION = 0;
    
    fn main() {
        for i in 0..1000 {  if 1 == 0 { } }

        for i in 10..500 {
            x = malloc_vec(6);
            poseidon16(i + 3, i, x, PERMUTATION);
            poseidon24(i + 3, i, x + 2);
            dot_product(i*2, i, (x + 3) * 8, 1);
            dot_product(i*3, i + 7, (x + 4) * 8, 2);
        }
        
        point_1 = malloc_vec(1, log2_ceil(10 * DIM));
        point_1_ptr = point_1 * (2 ** log2_ceil(10 * DIM));
        for i in 0..10 {
            point_1_ptr[i*5 + 0] = 785 + i;
            point_1_ptr[i*5 + 1] = 4152 - i;
            point_1_ptr[i*5 + 2] = 471*82 + i*i;
            point_1_ptr[i*5 + 3] = 7577 + i;
            point_1_ptr[i*5 + 4] = 676 - i;
        }

        res1 = malloc_vec(1);
        multilinear_eval(2**3, point_1, res1, 10);

        res2 = malloc_vec(1);
        multilinear_eval(10, SECOND_POINT, res2, SECOND_N_VARS);

        res3 = malloc_vec(1);
        multilinear_eval(11, SECOND_POINT, res3, SECOND_N_VARS);

        res2_ptr = res2 * 8;
        res3_ptr = res3 * 8;

        print(res3_ptr[0], res2_ptr[0]);

        assert res3_ptr[0] == res2_ptr[0] + 2**SECOND_N_VARS;

        for i in 0..1000 {
            assert i != 1000;
        }

        return;
    }
   "#;

    const SECOND_POINT: usize = 2;
    const SECOND_N_VARS: usize = 7;

    let mut public_input = (0..(1 << 13) - NONRESERVED_PROGRAM_INPUT_START)
        .map(F::from_usize)
        .collect::<Vec<_>>();

    public_input[SECOND_POINT * (SECOND_N_VARS * DIMENSION).next_power_of_two()
        + SECOND_N_VARS * DIMENSION
        - NONRESERVED_PROGRAM_INPUT_START
        ..(SECOND_POINT + 1) * (SECOND_N_VARS * DIMENSION).next_power_of_two()
            - NONRESERVED_PROGRAM_INPUT_START]
        .iter_mut()
        .for_each(|x| *x = F::ZERO);

    let private_input = (0..1 << 13)
        .map(|i| F::from_usize(i).square())
        .collect::<Vec<_>>();

    test_zk_vm_helper(program_str, (&public_input, &private_input), 1 << 20);
}

#[test]
fn test_prove_fibonacci() {
    let program_str = r#"
    const N = 2000000;
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

    test_zk_vm_helper(program_str, (&[F::ZERO; 1 << 14], &[]), 0);
}

fn test_zk_vm_helper(
    program_str: &str,
    (public_input, private_input): (&[F], &[F]),
    no_vec_runtime_memory: usize,
) {
    utils::init_tracing();
    let bytecode = compile_program(program_str.to_string());
    let time = std::time::Instant::now();
    let (proof_data, _, summary) = prove_execution(
        &bytecode,
        (&public_input, &private_input),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
        (&vec![], &vec![]),
    );
    let proof_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();
    println!("{}", summary);
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
}

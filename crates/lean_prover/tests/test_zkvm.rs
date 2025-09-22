use lean_compiler::*;
use lean_prover::{
    prove_execution::prove_execution, verify_execution::verify_execution, whir_config_builder,
};
use lean_vm::*;
use p3_field::PrimeCharacteristicRing;

#[test]
fn test_zk_vm() {
    let program_str = r#"
    const DIM = 5;
    const SECOND_POINT = 2;
    const SECOND_N_VARS = 7;
    
    fn main() {
        for i in 0..1000 unroll {  if 1 == 0 {  return; } } // increase bytecode size artificially

        for i in 0..500 {
            x = malloc_vec(6);
            poseidon16(i + 3, i, x);
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
   "#
    .to_string();

    const SECOND_POINT: usize = 2;
    const SECOND_N_VARS: usize = 7;

    let mut public_input = (0..(1 << 13) - PUBLIC_INPUT_START)
        .map(F::from_usize)
        .collect::<Vec<_>>();

    public_input[SECOND_POINT * (SECOND_N_VARS * DIMENSION).next_power_of_two()
        + SECOND_N_VARS * DIMENSION
        - PUBLIC_INPUT_START
        ..(SECOND_POINT + 1) * (SECOND_N_VARS * DIMENSION).next_power_of_two()
            - PUBLIC_INPUT_START]
        .iter_mut()
        .for_each(|x| *x = F::ZERO);

    let private_input = (0..1 << 13)
        .map(|i| F::from_usize(i).square())
        .collect::<Vec<_>>();

    // utils::init_tracing();
    let (bytecode, function_locations) = compile_program(&program_str);
    let proof_data = prove_execution(
        &bytecode,
        &program_str,
        &function_locations,
        &public_input,
        &private_input,
        whir_config_builder(),
        false,
    )
    .0;
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();
}

use compiler::*;
use p3_field::PrimeCharacteristicRing;
use vm::*;
use zk_vm::{
    build_batch_pcs, prove_execution::prove_execution, verify_execution::verify_execution,
};

#[test]
fn test_zk_vm() {
    let program_str = r#"
    
    fn main() {
        for i in 0..1000 unroll {  if 1 == 0 {  return; } } // increase bytecode size artificially

        for i in 0..500 {
            x = malloc_vec(6);
            poseidon16(i + 3, i, x);
            poseidon24(i + 3, i, x + 2);
            dot_product(i*2, i, (x + 3) * 8, 1);
            dot_product(i*3, i + 7, (x + 4) * 8, 2);
        }
        
        point_1 = malloc(10 * 5);
        for i in 0..10 {
            point_1[i*5 + 0] = 785 + i;
            point_1[i*5 + 1] = 4152 - i;
            point_1[i*5 + 2] = 471*82 + i*i;
            point_1[i*5 + 3] = 7577 + i;
            point_1[i*5 + 4] = 676 - i;
        }

        res1 = malloc(5);
        multilinear_eval(2**3, point_1, res1, 10);

        point_2 = 785;
        res2 = malloc(5);
        multilinear_eval(1, point_2, res2, 7);

        point_3 = 785;
        res3 = malloc(5);
        multilinear_eval(2, point_3, res3, 7);

        print(res3[0], res2[0]);

        assert res3[0] == res2[0] + 2**7;

        for i in 0..1000 {
            assert i != 1000;
        }

        return;
    }
   "#
    .to_string();

    let public_input = (0..(1 << 13) - PUBLIC_INPUT_START)
        .map(F::from_usize)
        .collect::<Vec<_>>();

    let private_input = (0..1 << 13)
        .map(|i| F::from_usize(i).square())
        .collect::<Vec<_>>();

    // utils::init_tracing();
    let (bytecode, function_locations) = compile_program(&program_str);
    let batch_pcs = build_batch_pcs();
    let proof_data = prove_execution(
        &bytecode,
        &program_str,
        &function_locations,
        &public_input,
        &private_input,
        &batch_pcs,
        false,
    );
    verify_execution(&bytecode, &public_input, proof_data, &batch_pcs).unwrap();
}

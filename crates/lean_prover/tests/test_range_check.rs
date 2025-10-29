use lean_compiler::*;
use lean_prover::{
    prove_execution::prove_execution, whir_config_builder,
};
use lean_vm::*;
use p3_field::PrimeCharacteristicRing;
use std::collections::BTreeSet;
use rand::Rng;
use rand_chacha::ChaCha20Rng;
use rand_chacha::rand_core::SeedableRng;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

const NO_VEC_RUNTIME_MEMORY: usize = 1 << 20;

fn critical_test_cases() -> (BTreeSet<(usize, usize)>, BTreeSet<(usize, usize)>) {
    let mut happy_test_cases = BTreeSet::<(usize, usize)>::new();
    let mut sad_test_cases = BTreeSet::<(usize, usize)>::new();

    for t in 69..70 {
        for v in 0..t {
            if v < t {
                happy_test_cases.insert((v, t));
            } else {
                sad_test_cases.insert((v, t));
            }
        }
        //for v in 16777215..16777300 {
            //if v < t {
                //happy_test_cases.insert((v, t));
            //} else {
                //sad_test_cases.insert((v, t));
            //}
        //}
    }

    (happy_test_cases, sad_test_cases)
}

fn random_test_cases(num_test_cases: usize) -> BTreeSet<(usize, usize)> {
    let v_max = 16777215 * 2;
    let t_max = 65536;
    let mut rng = ChaCha20Rng::seed_from_u64(0);

    let mut test_cases = BTreeSet::new();

    for _ in 0..num_test_cases / 2 {
        let t = rng.random_range(0..t_max) as usize;
        let v = rng.random_range(0..v_max) as usize;
        test_cases.insert((v, t));
    }

    for _ in 0..num_test_cases / 2 {
        let t = rng.random_range(0..t_max) as usize;
        let v = rng.random_range(0..v_max) as usize;
        if v >= t {
            test_cases.insert((v, t));
        } else {
            test_cases.insert((t, v));
        }
    }

    test_cases
}

fn range_check_program(value: usize, max: usize) -> String {
    let program = format!(r#"
    const DIM = 5;
    const SECOND_POINT = 2;
    const SECOND_N_VARS = 7;
    const COMPRESSION = 1;
    const PERMUTATION = 0;
    
    fn main() {{
        x = 1;
        y = {value};
        value = x * y;
        range_check(value, {max});

        // Need to add the following to avoid a "TODO small GKR, no packing" error

        for i in 10..50 {{
            x = malloc_vec(6);
            poseidon16(i + 3, i, x, PERMUTATION);
            poseidon24(i + 3, i, x + 2);
            dot_product(i*2, i, (x + 3) * 8, 1);
            dot_product(i*3, i + 7, (x + 4) * 8, 2);
        }}

        for i in 0..1000 {{
            assert i != 1000;
        }}

        return;
    }}
   "#);
   program.to_string()
}

fn do_test_range_check(v: usize, t: usize) {
    let program_str = range_check_program(v, t);

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

    let bytecode = compile_program(program_str);
    let _proof_data = prove_execution(
        &bytecode,
        (&public_input, &private_input),
        whir_config_builder(),
        NO_VEC_RUNTIME_MEMORY,
        false,
        (&vec![], &vec![]),
    );
}

#[test]
fn test_prove_range_check_happy() {
    let (happy_test_cases, _sad_test_cases) = critical_test_cases();
    println!("Running {} test cases:", happy_test_cases.len());
    //happy_test_cases.par_iter().for_each(|(v, t)| {
        //do_test_range_check(*v, *t);
    //});
    for (v, t) in happy_test_cases {
        do_test_range_check(v, t);
    }
}

//#[test]
//fn test_prove_range_check_sad() {
    //let (_happy_test_cases, sad_test_cases) = critical_test_cases();
    //for (v, t) in sad_test_cases {
        //let result = std::panic::catch_unwind(|| {
            //do_test_range_check(v, t);
        //});
        //assert!(result.is_err(), "Expected panic for test case v={}, t={}", v, t);
    //}
//}

#[test]
#[should_panic]
fn test_prove_range_check_sad_1() {
    do_test_range_check(0, 0);
}

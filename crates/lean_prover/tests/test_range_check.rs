use lean_compiler::compile_program;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{prove_execution::prove_execution, whir_config_builder};
use lean_vm::{DIMENSION, F, NONRESERVED_PROGRAM_INPUT_START};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::collections::BTreeSet;
use whir_p3::WhirConfigBuilder;
use multilinear_toolkit::prelude::*;

const NO_VEC_RUNTIME_MEMORY: usize = 1 << 20;

fn range_check_program(value: usize, max: usize) -> String {
    let program = format!(
        r#"
    fn func() {{
        x = 1;
        y = {value};
        value = x * y;
        range_check(value, {max});
        return;
    }}

    fn main() {{
        x = 1;
        y = {value};
        value = x * y;
        range_check(value, {max});

        func();

        if 0 == 0 {{
            a = 1;
            b = {value};
            c = a * b;
            range_check(c, {max});
        }}
        return;
    }}
   "#
    );
    program.to_string()
}

fn random_test_cases(num_test_cases: usize, valid: bool) -> BTreeSet<(usize, usize)> {
    let t_max = 1 << 16;
    let mut rng = StdRng::seed_from_u64(0);

    let mut test_cases = BTreeSet::new();

    while test_cases.len() < num_test_cases {
        let t = rng.random_range(1..t_max);
        let v = if valid {
            rng.random_range(0..t)
        } else {
            rng.random_range(t..1 << 31)
        };

        test_cases.insert((v, t));
    }

    test_cases
}

fn prepare_inputs() -> (Vec<F>, Vec<F>) {
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

    (public_input, private_input)
}

fn do_test_range_check(
    v: usize,
    t: usize,
    whir_config_builder: &WhirConfigBuilder,
    public_input: &[F],
    private_input: &[F],
) {
    let program_str = range_check_program(v, t);

    let bytecode = compile_program(program_str);

    let (proof_data, _, _) = prove_execution(
        &bytecode,
        (public_input, private_input),
        whir_config_builder.clone(),
        NO_VEC_RUNTIME_MEMORY,
        false,
        (&vec![], &vec![]),
    );
    verify_execution(
        &bytecode,
        public_input,
        proof_data,
        whir_config_builder.clone(),
    )
    .unwrap();
}

#[test]
fn test_range_check_valid() {
    test_range_check_random(100, true);
}

#[test]
#[should_panic]
fn test_range_check_invalid() {
    test_range_check_random(1, false);
}

fn test_range_check_random(num_test_cases: usize, valid: bool) {
    let (public_input, private_input) = prepare_inputs();
    let whir_config_builder = whir_config_builder();

    let test_cases = random_test_cases(num_test_cases, valid);

    println!("Running {} random test cases", test_cases.len());

    for (v, t) in test_cases {
        println!("v: {v}; t: {t}");
        do_test_range_check(v, t, &whir_config_builder, &public_input, &private_input);
    }
}

#[test]
fn test_range_check_valid_1() {
    let (public_input, private_input) = prepare_inputs();
    let whir_config_builder = whir_config_builder();
    do_test_range_check(
        3716,
        20122,
        &whir_config_builder,
        &public_input,
        &private_input,
    );
}

#[test]
#[should_panic]
fn test_range_check_invalid_1() {
    let (public_input, private_input) = prepare_inputs();
    let whir_config_builder = whir_config_builder();
    do_test_range_check(
        1,
        0,
        &whir_config_builder,
        &public_input,
        &private_input,
    );
}

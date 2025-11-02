use lean_compiler::compile_program;
use lean_prover::{prove_execution::prove_execution, whir_config_builder};
use lean_vm::{DIMENSION, F, PUBLIC_INPUT_START};
use p3_field::PrimeCharacteristicRing;
use rand::Rng;
use rand_chacha::ChaCha20Rng;
use rand_chacha::rand_core::SeedableRng;
use std::collections::BTreeSet;
use whir_p3::WhirConfigBuilder;

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

fn prepare_inputs() -> (Vec<F>, Vec<F>) {
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

    (public_input, private_input)
}

fn do_test_range_check(
    v: usize,
    t: usize,
    whir_config_builder: &WhirConfigBuilder,
    public_input: &Vec<F>,
    private_input: &Vec<F>,
) {
    let program_str = range_check_program(v, t);

    let bytecode = compile_program(program_str);

    let r = prove_execution(
        &bytecode,
        (public_input, private_input),
        whir_config_builder.clone(),
        NO_VEC_RUNTIME_MEMORY,
        false,
        (&vec![], &vec![]),
    );

    if v < t {
        assert!(r.is_ok(), "Proof generation should work for v < t");
    } else {
        assert!(r.is_err(), "Proof generation should fail for v >= t");
    }
}

#[test]
fn test_range_check() {
    let (public_input, private_input) = prepare_inputs();
    let whir_config_builder = whir_config_builder();

    let test_cases = random_test_cases(500);

    println!("Running {} random test cases", test_cases.len());

    for (v, t) in test_cases {
        do_test_range_check(v, t, &whir_config_builder, &public_input, &private_input);
    }
}

use lean_vm::error::ExecutionResult;
use lean_vm::*;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use p3_util::log2_ceil_usize;
use std::collections::BTreeMap;
use utils::ToUsize;

// Pointers for precompile inputs allocated in public memory.
const POSEIDON16_ARG_A_PTR: usize = 6;
const POSEIDON16_ARG_B_PTR: usize = 7;
const POSEIDON24_ARG_A_PTR: usize = 11; // uses ptr and ptr + 1
const POSEIDON24_ARG_B_PTR: usize = 13;
const DOT_ARG0_PTR: usize = 180; // normal pointer, len 2
const DOT_ARG1_PTR: usize = 200; // normal pointer, len 2
const MLE_COEFF_PTR: usize = 32; // interpreted with shift << n_vars
const MLE_POINT_PTR: usize = 15; // interpreted with shift << log_point_size

// Offsets used in hints for storing result pointers at fp + offset.
const POSEIDON16_RES_OFFSET: usize = 0;
const POSEIDON24_RES_OFFSET: usize = 1;
const DOT_RES_OFFSET: usize = 2;
const MLE_RES_OFFSET: usize = 3;

const DOT_PRODUCT_LEN: usize = 2;
const MLE_N_VARS: usize = 1;

// Ensure public input covers the highest index used (dot product arg1 slice).
const MAX_MEMORY_INDEX: usize = DOT_ARG1_PTR + DOT_PRODUCT_LEN * DIMENSION - 1;
const PUBLIC_INPUT_LEN: usize = MAX_MEMORY_INDEX - PUBLIC_INPUT_START + 1;

const POSEIDON16_ARG_A_VALUES: [u64; VECTOR_LEN] = [1, 2, 3, 4, 5, 6, 7, 8];
const POSEIDON16_ARG_B_VALUES: [u64; VECTOR_LEN] = [101, 102, 103, 104, 105, 106, 107, 108];
const POSEIDON24_ARG_A_VALUES: [[u64; VECTOR_LEN]; 2] = [
    [201, 202, 203, 204, 205, 206, 207, 208],
    [211, 212, 213, 214, 215, 216, 217, 218],
];
const POSEIDON24_ARG_B_VALUES: [u64; VECTOR_LEN] = [221, 222, 223, 224, 225, 226, 227, 228];
const DOT_ARG0_VALUES: [[u64; DIMENSION]; DOT_PRODUCT_LEN] = [[1, 2, 3, 4, 5], [6, 7, 8, 9, 10]];
const DOT_ARG1_VALUES: [[u64; DIMENSION]; DOT_PRODUCT_LEN] =
    [[11, 12, 13, 14, 15], [16, 17, 18, 19, 20]];
const MLE_COEFF_VALUES: [u64; 1 << MLE_N_VARS] = [7, 9];
const MLE_POINT_VALUES: [u64; DIMENSION] = [21, 22, 23, 24, 25];

fn f(value: u64) -> F {
    F::from_isize(value as isize)
}

fn set_public_input_cell(public_input: &mut [F], memory_index: usize, value: F) {
    assert!(memory_index >= PUBLIC_INPUT_START);
    let idx = memory_index - PUBLIC_INPUT_START;
    assert!(idx < public_input.len());
    public_input[idx] = value;
}

fn set_vector(public_input: &mut [F], ptr: usize, values: &[u64]) {
    assert_eq!(values.len(), VECTOR_LEN);
    for (i, &value) in values.iter().enumerate() {
        set_public_input_cell(public_input, ptr * VECTOR_LEN + i, f(value));
    }
}

fn set_multivector(public_input: &mut [F], ptr: usize, chunks: &[&[u64]]) {
    for (chunk_index, chunk) in chunks.iter().enumerate() {
        assert_eq!(chunk.len(), VECTOR_LEN);
        for (i, &value) in chunk.iter().enumerate() {
            set_public_input_cell(public_input, (ptr + chunk_index) * VECTOR_LEN + i, f(value));
        }
    }
}

fn set_ef_slice(public_input: &mut [F], ptr: usize, elements: &[[u64; DIMENSION]]) {
    for (i, coeffs) in elements.iter().enumerate() {
        for (j, &value) in coeffs.iter().enumerate() {
            set_public_input_cell(public_input, ptr + i * DIMENSION + j, f(value));
        }
    }
}

fn set_base_slice(public_input: &mut [F], start_index: usize, values: &[u64]) {
    for (i, &value) in values.iter().enumerate() {
        set_public_input_cell(public_input, start_index + i, f(value));
    }
}

fn build_test_case() -> (Bytecode, Vec<F>) {
    let mut public_input = vec![F::ZERO; PUBLIC_INPUT_LEN];

    set_vector(
        &mut public_input,
        POSEIDON16_ARG_A_PTR,
        &POSEIDON16_ARG_A_VALUES,
    );
    set_vector(
        &mut public_input,
        POSEIDON16_ARG_B_PTR,
        &POSEIDON16_ARG_B_VALUES,
    );

    let poseidon24_chunks = [
        &POSEIDON24_ARG_A_VALUES[0][..],
        &POSEIDON24_ARG_A_VALUES[1][..],
    ];
    set_multivector(&mut public_input, POSEIDON24_ARG_A_PTR, &poseidon24_chunks);
    set_vector(
        &mut public_input,
        POSEIDON24_ARG_B_PTR,
        &POSEIDON24_ARG_B_VALUES,
    );

    set_ef_slice(&mut public_input, DOT_ARG0_PTR, &DOT_ARG0_VALUES);
    set_ef_slice(&mut public_input, DOT_ARG1_PTR, &DOT_ARG1_VALUES);

    let coeff_base = MLE_COEFF_PTR << MLE_N_VARS;
    set_base_slice(&mut public_input, coeff_base, &MLE_COEFF_VALUES);

    let log_point_size = log2_ceil_usize(MLE_N_VARS * DIMENSION);
    let point_base = MLE_POINT_PTR << log_point_size;
    set_base_slice(&mut public_input, point_base, &MLE_POINT_VALUES);

    let mut hints = BTreeMap::new();
    hints.insert(
        0,
        vec![Hint::RequestMemory {
            offset: POSEIDON16_RES_OFFSET,
            size: MemOrConstant::Constant(f(2)),
            vectorized: true,
            vectorized_len: LOG_VECTOR_LEN + 1,
        }],
    );
    hints.insert(
        1,
        vec![Hint::RequestMemory {
            offset: POSEIDON24_RES_OFFSET,
            size: MemOrConstant::Constant(f(1)),
            vectorized: true,
            vectorized_len: LOG_VECTOR_LEN,
        }],
    );
    hints.insert(
        2,
        vec![Hint::RequestMemory {
            offset: DOT_RES_OFFSET,
            size: MemOrConstant::Constant(f(1)),
            vectorized: false,
            vectorized_len: 0,
        }],
    );
    hints.insert(
        3,
        vec![Hint::RequestMemory {
            offset: MLE_RES_OFFSET,
            size: MemOrConstant::Constant(f(1)),
            vectorized: true,
            vectorized_len: LOG_VECTOR_LEN,
        }],
    );

    let instructions = vec![
        Instruction::Poseidon2_16 {
            arg_a: MemOrConstant::Constant(f(POSEIDON16_ARG_A_PTR as u64)),
            arg_b: MemOrConstant::Constant(f(POSEIDON16_ARG_B_PTR as u64)),
            res: MemOrFp::MemoryAfterFp {
                offset: POSEIDON16_RES_OFFSET,
            },
        },
        Instruction::Poseidon2_24 {
            arg_a: MemOrConstant::Constant(f(POSEIDON24_ARG_A_PTR as u64)),
            arg_b: MemOrConstant::Constant(f(POSEIDON24_ARG_B_PTR as u64)),
            res: MemOrFp::MemoryAfterFp {
                offset: POSEIDON24_RES_OFFSET,
            },
        },
        Instruction::DotProductExtensionExtension {
            arg0: MemOrConstant::Constant(f(DOT_ARG0_PTR as u64)),
            arg1: MemOrConstant::Constant(f(DOT_ARG1_PTR as u64)),
            res: MemOrFp::MemoryAfterFp {
                offset: DOT_RES_OFFSET,
            },
            size: DOT_PRODUCT_LEN,
        },
        Instruction::MultilinearEval {
            coeffs: MemOrConstant::Constant(f(MLE_COEFF_PTR as u64)),
            point: MemOrConstant::Constant(f(MLE_POINT_PTR as u64)),
            res: MemOrFp::MemoryAfterFp {
                offset: MLE_RES_OFFSET,
            },
            n_vars: MLE_N_VARS,
        },
    ];

    let bytecode = Bytecode {
        instructions,
        hints,
        starting_frame_memory: 512,
        ending_pc: 4,
    };

    (bytecode, public_input)
}

fn run_program() -> (Bytecode, ExecutionResult) {
    let (bytecode, public_input) = build_test_case();
    let result = execute_bytecode(&bytecode, &public_input, &[], "", &BTreeMap::new(), false);
    (bytecode, result)
}

#[test]
fn vm_precompile_events_capture_expected_data() {
    let (_bytecode, execution_result) = run_program();

    assert_eq!(execution_result.poseidons_16.len(), 1);
    assert_eq!(execution_result.poseidons_24.len(), 1);
    assert_eq!(execution_result.dot_products.len(), 1);
    assert_eq!(execution_result.multilinear_evals.len(), 1);

    let poseidon16_event = &execution_result.poseidons_16[0];
    assert_eq!(poseidon16_event.cycle, Some(0));
    assert_eq!(poseidon16_event.addr_input_a, POSEIDON16_ARG_A_PTR);
    assert_eq!(poseidon16_event.addr_input_b, POSEIDON16_ARG_B_PTR);

    let poseidon16_res_ptr = execution_result
        .memory
        .get(execution_result.fps[poseidon16_event.cycle.unwrap()] + POSEIDON16_RES_OFFSET)
        .unwrap()
        .to_usize();
    assert_eq!(poseidon16_event.addr_output, poseidon16_res_ptr);

    let poseidon16_input_a = POSEIDON16_ARG_A_VALUES.map(f);
    let poseidon16_input_b = POSEIDON16_ARG_B_VALUES.map(f);
    let mut expected_poseidon16_input = [F::ZERO; 16];
    expected_poseidon16_input[..VECTOR_LEN].copy_from_slice(&poseidon16_input_a);
    expected_poseidon16_input[VECTOR_LEN..].copy_from_slice(&poseidon16_input_b);
    assert_eq!(poseidon16_event.input, expected_poseidon16_input);

    let poseidon16_output = execution_result
        .memory
        .get_vectorized_slice(poseidon16_event.addr_output, 2)
        .unwrap();
    assert_eq!(poseidon16_output, poseidon16_event.output.to_vec());

    let poseidon24_event = &execution_result.poseidons_24[0];
    assert_eq!(poseidon24_event.cycle, Some(1));
    assert_eq!(poseidon24_event.addr_input_a, POSEIDON24_ARG_A_PTR);
    assert_eq!(poseidon24_event.addr_input_b, POSEIDON24_ARG_B_PTR);

    let poseidon24_res_ptr = execution_result
        .memory
        .get(execution_result.fps[poseidon24_event.cycle.unwrap()] + POSEIDON24_RES_OFFSET)
        .unwrap()
        .to_usize();
    assert_eq!(poseidon24_event.addr_output, poseidon24_res_ptr);

    let poseidon24_input_a0 = POSEIDON24_ARG_A_VALUES[0].map(f);
    let poseidon24_input_a1 = POSEIDON24_ARG_A_VALUES[1].map(f);
    let poseidon24_input_b = POSEIDON24_ARG_B_VALUES.map(f);
    let mut expected_poseidon24_input = [F::ZERO; 24];
    expected_poseidon24_input[..VECTOR_LEN].copy_from_slice(&poseidon24_input_a0);
    expected_poseidon24_input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&poseidon24_input_a1);
    expected_poseidon24_input[2 * VECTOR_LEN..].copy_from_slice(&poseidon24_input_b);
    assert_eq!(poseidon24_event.input, expected_poseidon24_input);

    let poseidon24_output = execution_result
        .memory
        .get_vector(poseidon24_event.addr_output)
        .unwrap();
    assert_eq!(poseidon24_output, poseidon24_event.output);

    let dot_event = &execution_result.dot_products[0];
    assert_eq!(dot_event.cycle, 2);
    assert_eq!(dot_event.addr_0, DOT_ARG0_PTR);
    assert_eq!(dot_event.addr_1, DOT_ARG1_PTR);

    let dot_res_ptr = execution_result
        .memory
        .get(execution_result.fps[dot_event.cycle] + DOT_RES_OFFSET)
        .unwrap()
        .to_usize();
    assert_eq!(dot_event.addr_res, dot_res_ptr);

    let dot_slice_0 = DOT_ARG0_VALUES
        .iter()
        .map(|coeffs| coeffs.map(f))
        .map(|coeffs| EF::from_basis_coefficients_slice(&coeffs).unwrap())
        .collect::<Vec<_>>();
    let dot_slice_1 = DOT_ARG1_VALUES
        .iter()
        .map(|coeffs| coeffs.map(f))
        .map(|coeffs| EF::from_basis_coefficients_slice(&coeffs).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(dot_event.slice_0, dot_slice_0);
    assert_eq!(dot_event.slice_1, dot_slice_1);

    let dot_res = execution_result
        .memory
        .get_ef_element(dot_event.addr_res)
        .unwrap();
    assert_eq!(dot_event.res, dot_res);

    let mle_event = &execution_result.multilinear_evals[0];
    assert_eq!(mle_event.cycle, 3);
    assert_eq!(mle_event.addr_coeffs, MLE_COEFF_PTR);
    assert_eq!(mle_event.addr_point, MLE_POINT_PTR);

    let mle_res_ptr = execution_result
        .memory
        .get(execution_result.fps[mle_event.cycle] + MLE_RES_OFFSET)
        .unwrap()
        .to_usize();
    assert_eq!(mle_event.addr_res, mle_res_ptr);

    let expected_point = vec![EF::from_basis_coefficients_slice(&MLE_POINT_VALUES.map(f)).unwrap()];
    assert_eq!(mle_event.point, expected_point);

    let mle_res_vec = execution_result
        .memory
        .get_vector(mle_event.addr_res)
        .unwrap();
    let mle_res_coeffs: [F; DIMENSION] = mle_res_vec[..DIMENSION].try_into().unwrap();
    let mle_res = EF::from_basis_coefficients_slice(&mle_res_coeffs).unwrap();
    assert_eq!(mle_event.res, mle_res);
}

// #[test]
// fn vm_precompile_events_only_final_pass() {
//     let (bytecode, public_input) = build_test_case();
//     let mut std_out = String::new();
//     let mut history = ExecutionHistory::default();

//     let first_pass = execute_bytecode_helper(
//         &bytecode,
//         &public_input,
//         &[],
//         MAX_RUNNER_MEMORY_SIZE / 2,
//         false,
//         &mut std_out,
//         &mut history,
//         false,
//         &BTreeMap::new(),
//     )
//     .expect("first execution should succeed");

//     assert!(first_pass.vm_poseidon16_events.is_empty());
//     assert!(first_pass.vm_poseidon24_events.is_empty());
//     assert!(first_pass.vm_dot_product_events.is_empty());
//     assert!(first_pass.vm_multilinear_eval_events.is_empty());

//     let mut history_final = ExecutionHistory::default();
//     let final_pass = execute_bytecode_helper(
//         &bytecode,
//         &public_input,
//         &[],
//         first_pass.no_vec_runtime_memory,
//         true,
//         &mut String::new(),
//         &mut history_final,
//         false,
//         &BTreeMap::new(),
//     )
//     .expect("final execution should succeed");

//     assert_eq!(final_pass.vm_poseidon16_events.len(), 1);
//     assert_eq!(final_pass.vm_poseidon24_events.len(), 1);
//     assert_eq!(final_pass.vm_dot_product_events.len(), 1);
//     assert_eq!(final_pass.vm_multilinear_eval_events.len(), 1);
// }

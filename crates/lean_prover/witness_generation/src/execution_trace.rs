use crate::instruction_encoder::field_representation;
use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C,
    COL_INDEX_MEM_VALUE_A, COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC,
    N_EXEC_COLUMNS, N_INSTRUCTION_COLUMNS,
};
use lean_vm::*;
use p3_field::Field;
use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use rayon::prelude::*;
use utils::{ToUsize, get_poseidon16, get_poseidon24};

#[derive(Debug)]
pub struct WitnessDotProduct {
    pub cycle: usize,
    pub addr_0: usize,   // normal pointer
    pub addr_1: usize,   // normal pointer
    pub addr_res: usize, // normal pointer
    pub len: usize,
    pub slice_0: Vec<EF>,
    pub slice_1: Vec<EF>,
    pub res: EF,
}
impl WitnessDotProduct {
    pub fn addresses_and_len_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_0),
            F::from_usize(self.addr_1),
            F::from_usize(self.addr_res),
            F::from_usize(self.len),
        ]
    }
}

#[derive(Debug)]
pub struct RowMultilinearEval {
    pub addr_coeffs: usize,
    pub addr_point: usize,
    pub addr_res: usize,
    pub point: Vec<EF>,
    pub res: EF,
}

impl RowMultilinearEval {
    pub fn n_vars(&self) -> usize {
        self.point.len()
    }

    pub fn addresses_and_n_vars_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_coeffs),
            F::from_usize(self.addr_point),
            F::from_usize(self.addr_res),
            F::from_usize(self.n_vars()),
        ]
    }
}

#[derive(Debug, derive_more::Deref)]
pub struct WitnessMultilinearEval {
    pub cycle: usize,
    #[deref]
    pub inner: RowMultilinearEval,
}

#[derive(Debug)]
pub struct WitnessPoseidon16 {
    pub cycle: Option<usize>,
    pub addr_input_a: usize, // vectorized pointer (of size 1)
    pub addr_input_b: usize, // vectorized pointer (of size 1)
    pub addr_output: usize,  // vectorized pointer (of size 2)
    pub input: [F; 16],
    pub output: [F; 16],
}

impl WitnessPoseidon16 {
    pub fn poseidon_of_zero() -> Self {
        Self {
            cycle: None,
            addr_input_a: ZERO_VEC_PTR,
            addr_input_b: ZERO_VEC_PTR,
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            output: get_poseidon16().permute([F::ZERO; 16]),
        }
    }

    pub fn addresses_field_repr(&self) -> [F; 3] {
        [
            F::from_usize(self.addr_input_a),
            F::from_usize(self.addr_input_b),
            F::from_usize(self.addr_output),
        ]
    }
}

#[derive(Debug)]
pub struct WitnessPoseidon24 {
    pub cycle: Option<usize>,
    pub addr_input_a: usize, // vectorized pointer (of size 2)
    pub addr_input_b: usize, // vectorized pointer (of size 1)
    pub addr_output: usize,  // vectorized pointer (of size 1)
    pub input: [F; 24],
    pub output: [F; 8], // last 8 elements of the output
}

impl WitnessPoseidon24 {
    pub fn poseidon_of_zero() -> Self {
        Self {
            cycle: None,
            addr_input_a: ZERO_VEC_PTR,
            addr_input_b: ZERO_VEC_PTR,
            addr_output: POSEIDON_24_NULL_HASH_PTR,
            input: [F::ZERO; 24],
            output: get_poseidon24().permute([F::ZERO; 24])[16..24]
                .try_into()
                .unwrap(),
        }
    }

    pub fn addresses_field_repr(&self) -> [F; 3] {
        [
            F::from_usize(self.addr_input_a),
            F::from_usize(self.addr_input_b),
            F::from_usize(self.addr_output),
        ]
    }
}

#[derive(Debug)]
pub struct ExecutionTrace {
    pub full_trace: Vec<Vec<F>>,
    pub n_poseidons_16: usize,
    pub n_poseidons_24: usize,
    pub poseidons_16: Vec<WitnessPoseidon16>, // padded with empty poseidons
    pub poseidons_24: Vec<WitnessPoseidon24>, // padded with empty poseidons
    pub dot_products: Vec<WitnessDotProduct>,
    pub vm_multilinear_evals: Vec<WitnessMultilinearEval>,
    pub public_memory_size: usize,
    pub non_zero_memory_size: usize,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
}

pub fn get_execution_trace(
    bytecode: &Bytecode,
    execution_result: &ExecutionResult,
) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());
    let n_cycles = execution_result.pcs.len();
    let memory = &execution_result.memory;
    let log_n_cycles_rounded_up = n_cycles.next_power_of_two().ilog2() as usize;
    let mut trace = (0..N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS)
        .map(|_| F::zero_vec(1 << log_n_cycles_rounded_up))
        .collect::<Vec<Vec<F>>>();
    let mut poseidons_16 = Vec::new();
    let mut poseidons_24 = Vec::new();
    let mut dot_products = Vec::new();
    let mut vm_multilinear_evals = Vec::new();

    for (cycle, (&pc, &fp)) in execution_result
        .pcs
        .iter()
        .zip(&execution_result.fps)
        .enumerate()
    {
        if pc == bytecode.ending_pc {
            if pc < bytecode.instructions.len() {
                let field_repr = field_representation(&bytecode.instructions[pc]);
                for (j, field) in field_repr.iter().enumerate() {
                    trace[j][cycle] = *field;
                }
            }
            trace[COL_INDEX_PC][cycle] = F::from_usize(pc);
            trace[COL_INDEX_FP][cycle] = F::from_usize(fp);
            continue;
        }
        let instruction = &bytecode.instructions[pc];
        let field_repr = field_representation(instruction);

        // println!(
        //     "Cycle {}: PC = {}, FP = {}, Instruction = {}",
        //     i, pc, fp, instruction.to_string()
        // );

        for (j, field) in field_repr.iter().enumerate() {
            trace[j][cycle] = *field;
        }

        let mut addr_a = F::ZERO;
        if field_repr[3].is_zero() {
            // flag_a == 0
            addr_a = F::from_usize(fp) + field_repr[0]; // fp + operand_a
        }
        let value_a = memory.0[addr_a.to_usize()].unwrap();
        let mut addr_b = F::ZERO;
        if field_repr[4].is_zero() {
            // flag_b == 0
            addr_b = F::from_usize(fp) + field_repr[1]; // fp + operand_b
        }
        let value_b = memory.0[addr_b.to_usize()].unwrap();

        let mut addr_c = F::ZERO;
        if field_repr[5].is_zero() {
            // flag_c == 0
            addr_c = F::from_usize(fp) + field_repr[2]; // fp + operand_c
        } else if let Instruction::Deref { shift_1, .. } = instruction {
            let operand_c = F::from_usize(*shift_1);
            assert_eq!(field_repr[2], operand_c); // debug purpose
            addr_c = value_a + operand_c;
        }
        let value_c = memory.0[addr_c.to_usize()].unwrap();

        trace[COL_INDEX_MEM_VALUE_A][cycle] = value_a;
        trace[COL_INDEX_MEM_VALUE_B][cycle] = value_b;
        trace[COL_INDEX_MEM_VALUE_C][cycle] = value_c;
        trace[COL_INDEX_PC][cycle] = F::from_usize(pc);
        trace[COL_INDEX_FP][cycle] = F::from_usize(fp);
        trace[COL_INDEX_MEM_ADDRESS_A][cycle] = addr_a;
        trace[COL_INDEX_MEM_ADDRESS_B][cycle] = addr_b;
        trace[COL_INDEX_MEM_ADDRESS_C][cycle] = addr_c;
    }

    // repeat the last row to get to a power of two
    for column in trace
        .iter_mut()
        .take(N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS)
    {
        let last_value = column[n_cycles - 1];
        for cell in column.iter_mut().skip(n_cycles) {
            *cell = last_value;
        }
    }

    let mut memory_padded = memory
        .0
        .par_iter()
        .map(|&v| v.unwrap_or(F::ZERO))
        .collect::<Vec<F>>();
    memory_padded.resize(memory.0.len().next_power_of_two(), F::ZERO);

    // Build witnesses from VM-collected events
    for e in &execution_result.vm_poseidon16_events {
        poseidons_16.push(WitnessPoseidon16 {
            cycle: Some(e.cycle),
            addr_input_a: e.addr_input_a,
            addr_input_b: e.addr_input_b,
            addr_output: e.addr_output,
            input: e.input,
            output: e.output,
        });
    }
    for e in &execution_result.vm_poseidon24_events {
        poseidons_24.push(WitnessPoseidon24 {
            cycle: Some(e.cycle),
            addr_input_a: e.addr_input_a,
            addr_input_b: e.addr_input_b,
            addr_output: e.addr_output,
            input: e.input,
            output: e.output,
        });
    }
    for e in &execution_result.vm_dot_product_events {
        dot_products.push(WitnessDotProduct {
            cycle: e.cycle,
            addr_0: e.addr_0,
            addr_1: e.addr_1,
            addr_res: e.addr_res,
            len: e.len,
            slice_0: e.slice_0.clone(),
            slice_1: e.slice_1.clone(),
            res: e.res,
        });
    }
    for e in &execution_result.vm_multilinear_eval_events {
        vm_multilinear_evals.push(WitnessMultilinearEval {
            cycle: e.cycle,
            inner: RowMultilinearEval {
                addr_coeffs: e.addr_coeffs,
                addr_point: e.addr_point,
                addr_res: e.addr_res,
                point: e.point.clone(),
                res: e.res,
            },
        });
    }

    let n_poseidons_16 = poseidons_16.len();
    let n_poseidons_24 = poseidons_24.len();

    let empty_poseidon16_output = get_poseidon16().permute([F::ZERO; 16]);
    let empty_poseidon24_output = get_poseidon24().permute([F::ZERO; 24])[16..24]
        .try_into()
        .unwrap();

    poseidons_16.extend(
        (0..n_poseidons_16.next_power_of_two() - n_poseidons_16).map(|_| WitnessPoseidon16 {
            cycle: None,
            addr_input_a: 0,
            addr_input_b: 0,
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            output: empty_poseidon16_output,
        }),
    );
    poseidons_24.extend(
        (0..n_poseidons_24.next_power_of_two() - n_poseidons_24).map(|_| WitnessPoseidon24 {
            cycle: None,
            addr_input_a: 0,
            addr_input_b: 0,
            addr_output: POSEIDON_24_NULL_HASH_PTR,
            input: [F::ZERO; 24],
            output: empty_poseidon24_output,
        }),
    );

    ExecutionTrace {
        full_trace: trace,
        n_poseidons_16,
        n_poseidons_24,
        poseidons_16,
        poseidons_24,
        dot_products,
        vm_multilinear_evals,
        public_memory_size: execution_result.public_memory_size,
        non_zero_memory_size: memory.0.len(),
        memory: memory_padded,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, dot_product};
    use p3_util::log2_ceil_usize;
    use std::collections::BTreeMap;
    use utils::ToUsize;

    const POSEIDON16_ARG_A_PTR: usize = 6;
    const POSEIDON16_ARG_B_PTR: usize = 7;
    const POSEIDON24_ARG_A_PTR: usize = 11;
    const POSEIDON24_ARG_B_PTR: usize = 13;
    const DOT_ARG0_PTR: usize = 180;
    const DOT_ARG1_PTR: usize = 200;
    const MLE_COEFF_PTR: usize = 32;
    const MLE_POINT_PTR: usize = 15;

    const POSEIDON16_RES_OFFSET: usize = 0;
    const POSEIDON24_RES_OFFSET: usize = 1;
    const DOT_RES_OFFSET: usize = 2;
    const MLE_RES_OFFSET: usize = 3;

    const DOT_PRODUCT_LEN: usize = 2;
    const MLE_N_VARS: usize = 1;

    const MAX_MEMORY_INDEX: usize = DOT_ARG1_PTR + DOT_PRODUCT_LEN * DIMENSION - 1;
    const PUBLIC_INPUT_LEN: usize = MAX_MEMORY_INDEX - PUBLIC_INPUT_START + 1;

    const POSEIDON16_ARG_A_VALUES: [u64; VECTOR_LEN] = [1, 2, 3, 4, 5, 6, 7, 8];
    const POSEIDON16_ARG_B_VALUES: [u64; VECTOR_LEN] = [101, 102, 103, 104, 105, 106, 107, 108];
    const POSEIDON24_ARG_A_VALUES: [[u64; VECTOR_LEN]; 2] = [
        [201, 202, 203, 204, 205, 206, 207, 208],
        [211, 212, 213, 214, 215, 216, 217, 218],
    ];
    const POSEIDON24_ARG_B_VALUES: [u64; VECTOR_LEN] = [221, 222, 223, 224, 225, 226, 227, 228];
    const DOT_ARG0_VALUES: [[u64; DIMENSION]; DOT_PRODUCT_LEN] =
        [[1, 2, 3, 4, 5], [6, 7, 8, 9, 10]];
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
        for (chunk_idx, chunk) in chunks.iter().enumerate() {
            assert_eq!(chunk.len(), VECTOR_LEN);
            for (i, &value) in chunk.iter().enumerate() {
                set_public_input_cell(public_input, (ptr + chunk_idx) * VECTOR_LEN + i, f(value));
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

    fn embed_base_into_extension(value: F) -> EF {
        let mut coeffs = [F::ZERO; DIMENSION];
        coeffs[0] = value;
        EF::from_basis_coefficients_slice(&coeffs).unwrap()
    }

    #[test]
    fn execution_trace_uses_vm_events() {
        let (bytecode, public_input) = build_test_case();
        let execution_result =
            execute_bytecode(&bytecode, &public_input, &[], "", &BTreeMap::new(), false);

        let trace = get_execution_trace(&bytecode, &execution_result);

        assert_eq!(execution_result.vm_poseidon16_events.len(), 1);
        assert_eq!(execution_result.vm_poseidon24_events.len(), 1);
        assert_eq!(execution_result.vm_dot_product_events.len(), 1);
        assert_eq!(execution_result.vm_multilinear_eval_events.len(), 1);

        assert_eq!(trace.n_poseidons_16, 1);
        assert_eq!(trace.poseidons_16.len(), 1);
        assert_eq!(trace.n_poseidons_24, 1);
        assert_eq!(trace.poseidons_24.len(), 1);
        assert_eq!(trace.dot_products.len(), 1);
        assert_eq!(trace.vm_multilinear_evals.len(), 1);

        let poseidon16_event = &execution_result.vm_poseidon16_events[0];
        let witness16 = &trace.poseidons_16[0];
        assert_eq!(witness16.cycle, Some(poseidon16_event.cycle));
        assert_eq!(witness16.addr_input_a, poseidon16_event.addr_input_a);
        assert_eq!(witness16.addr_input_b, poseidon16_event.addr_input_b);
        assert_eq!(witness16.addr_output, poseidon16_event.addr_output);
        assert_eq!(witness16.input, poseidon16_event.input);
        assert_eq!(witness16.output, poseidon16_event.output);

        let mut expected_poseidon16_input = [F::ZERO; 16];
        expected_poseidon16_input[..VECTOR_LEN].copy_from_slice(&POSEIDON16_ARG_A_VALUES.map(f));
        expected_poseidon16_input[VECTOR_LEN..].copy_from_slice(&POSEIDON16_ARG_B_VALUES.map(f));
        assert_eq!(witness16.input, expected_poseidon16_input);

        let poseidon16_perm = get_poseidon16().permute(poseidon16_event.input);
        assert_eq!(witness16.output, poseidon16_perm);

        let poseidon24_event = &execution_result.vm_poseidon24_events[0];
        let witness24 = &trace.poseidons_24[0];
        assert_eq!(witness24.cycle, Some(poseidon24_event.cycle));
        assert_eq!(witness24.addr_input_a, poseidon24_event.addr_input_a);
        assert_eq!(witness24.addr_input_b, poseidon24_event.addr_input_b);
        assert_eq!(witness24.addr_output, poseidon24_event.addr_output);
        assert_eq!(witness24.input, poseidon24_event.input);
        assert_eq!(witness24.output, poseidon24_event.output);

        let mut expected_poseidon24_input = [F::ZERO; 24];
        expected_poseidon24_input[..VECTOR_LEN].copy_from_slice(&POSEIDON24_ARG_A_VALUES[0].map(f));
        expected_poseidon24_input[VECTOR_LEN..2 * VECTOR_LEN]
            .copy_from_slice(&POSEIDON24_ARG_A_VALUES[1].map(f));
        expected_poseidon24_input[2 * VECTOR_LEN..]
            .copy_from_slice(&POSEIDON24_ARG_B_VALUES.map(f));
        assert_eq!(witness24.input, expected_poseidon24_input);

        let mut poseidon24_input = poseidon24_event.input;
        get_poseidon24().permute_mut(&mut poseidon24_input);
        let expected_poseidon24: [F; VECTOR_LEN] =
            poseidon24_input[2 * VECTOR_LEN..].try_into().unwrap();
        assert_eq!(witness24.output, expected_poseidon24);

        let dot_event = &execution_result.vm_dot_product_events[0];
        let witness_dot = &trace.dot_products[0];
        assert_eq!(witness_dot.cycle, dot_event.cycle);
        assert_eq!(witness_dot.addr_0, dot_event.addr_0);
        assert_eq!(witness_dot.addr_1, dot_event.addr_1);
        assert_eq!(witness_dot.addr_res, dot_event.addr_res);
        assert_eq!(witness_dot.len, dot_event.len);
        assert_eq!(witness_dot.slice_0, dot_event.slice_0);
        assert_eq!(witness_dot.slice_1, dot_event.slice_1);
        assert_eq!(witness_dot.res, dot_event.res);

        let expected_dot_slice_0 = DOT_ARG0_VALUES
            .iter()
            .map(|coeffs| coeffs.map(f))
            .map(|coeffs| EF::from_basis_coefficients_slice(&coeffs).unwrap())
            .collect::<Vec<_>>();
        let expected_dot_slice_1 = DOT_ARG1_VALUES
            .iter()
            .map(|coeffs| coeffs.map(f))
            .map(|coeffs| EF::from_basis_coefficients_slice(&coeffs).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(witness_dot.slice_0, expected_dot_slice_0);
        assert_eq!(witness_dot.slice_1, expected_dot_slice_1);

        let expected_dot = dot_product::<EF, _, _>(
            witness_dot.slice_0.iter().copied(),
            witness_dot.slice_1.iter().copied(),
        );
        assert_eq!(witness_dot.res, expected_dot);

        let mle_event = &execution_result.vm_multilinear_eval_events[0];
        let witness_mle = &trace.vm_multilinear_evals[0];
        let witness_mle_row = &witness_mle.inner;
        assert_eq!(witness_mle.cycle, mle_event.cycle);
        assert_eq!(witness_mle_row.addr_coeffs, mle_event.addr_coeffs);
        assert_eq!(witness_mle_row.addr_point, mle_event.addr_point);
        assert_eq!(witness_mle_row.addr_res, mle_event.addr_res);
        assert_eq!(witness_mle_row.n_vars(), mle_event.n_vars);
        let witness_point = &witness_mle_row.point;
        assert_eq!(witness_point, &mle_event.point);
        assert_eq!(witness_mle_row.res, mle_event.res);

        let expected_point =
            vec![EF::from_basis_coefficients_slice(&MLE_POINT_VALUES.map(f)).unwrap()];
        assert_eq!(witness_point, &expected_point);

        let coeff_slice = execution_result
            .memory
            .slice(
                mle_event.addr_coeffs << mle_event.n_vars,
                1 << mle_event.n_vars,
            )
            .unwrap();
        let point = witness_point[0];
        let c0 = embed_base_into_extension(coeff_slice[0]);
        let c1 = embed_base_into_extension(coeff_slice[1]);
        let expected_mle = c0 * (EF::ONE - point) + c1 * point;
        assert_eq!(witness_mle_row.res, expected_mle);

        assert_eq!(
            trace.poseidons_16.len(),
            trace.n_poseidons_16.next_power_of_two()
        );
        assert_eq!(
            trace.poseidons_24.len(),
            trace.n_poseidons_24.next_power_of_two()
        );
        assert_eq!(
            trace.public_memory_size,
            execution_result.public_memory_size
        );

        let poseidon16_res_ptr = execution_result
            .memory
            .get(execution_result.fps[poseidon16_event.cycle] + POSEIDON16_RES_OFFSET)
            .unwrap()
            .to_usize();
        assert_eq!(witness16.addr_output, poseidon16_res_ptr);

        let poseidon24_res_ptr = execution_result
            .memory
            .get(execution_result.fps[poseidon24_event.cycle] + POSEIDON24_RES_OFFSET)
            .unwrap()
            .to_usize();
        assert_eq!(witness24.addr_output, poseidon24_res_ptr);

        let dot_res_ptr = execution_result
            .memory
            .get(execution_result.fps[dot_event.cycle] + DOT_RES_OFFSET)
            .unwrap()
            .to_usize();
        assert_eq!(witness_dot.addr_res, dot_res_ptr);

        let mle_res_ptr = execution_result
            .memory
            .get(execution_result.fps[mle_event.cycle] + MLE_RES_OFFSET)
            .unwrap()
            .to_usize();
        assert_eq!(witness_mle_row.addr_res, mle_res_ptr);
    }
}

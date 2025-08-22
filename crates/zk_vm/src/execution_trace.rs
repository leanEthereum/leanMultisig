use p3_field::{Field, PrimeCharacteristicRing};
use p3_symmetric::Permutation;
use rayon::prelude::*;
use utils::{ToUsize, build_poseidon16, build_poseidon24};
use vm::{
    Bytecode, ExecutionResult, F, Instruction, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR,
};

use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C,
    COL_INDEX_MEM_VALUE_A, COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC,
    N_EXEC_COLUMNS, N_INSTRUCTION_COLUMNS,
    instruction_encoder::field_representation,
    witness::{
        dot_product::WitnessDotProduct,
        multilinear_eval::WitnessMultilinearEval,
        poseidon::{WitnessPoseidon16, WitnessPoseidon24},
    },
};

/// Represents the complete trace of a program's execution, including precompile data.
#[derive(Debug)]
pub struct ExecutionTrace {
    /// The main CPU trace columns.
    pub full_trace: Vec<Vec<F>>,
    /// The actual number of Poseidon16 operations executed.
    pub n_poseidons_16: usize,
    /// The actual number of Poseidon24 operations executed.
    pub n_poseidons_24: usize,
    /// Padded witness data for all Poseidon16 operations.
    pub poseidons_16: Vec<WitnessPoseidon16>,
    /// Padded witness data for all Poseidon24 operations.
    pub poseidons_24: Vec<WitnessPoseidon24>,
    /// Witness data for all dot product operations.
    pub dot_products: Vec<WitnessDotProduct>,
    /// Witness data for all multilinear evaluation operations.
    pub vm_multilinear_evals: Vec<WitnessMultilinearEval>,
    /// The size of the public memory region.
    pub public_memory_size: usize,
    /// The final, flattened state of the VM's memory.
    pub memory: Vec<F>,
}

impl ExecutionTrace {
    pub fn new(bytecode: &Bytecode, execution_result: &ExecutionResult) -> Self {
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
            let instruction = &bytecode.instructions[pc];
            let field_repr = field_representation(instruction);

            for (j, field) in field_repr.iter().enumerate() {
                trace[j][cycle] = *field;
            }

            let addr_a = if field_repr[3].is_zero() {
                // flag_a == 0
                // fp + operand_a
                F::from_usize(fp) + field_repr[0]
            } else {
                F::ZERO
            };

            let value_a = memory.0[addr_a.to_usize()].unwrap();
            let addr_b = if field_repr[4].is_zero() {
                // flag_b == 0
                // fp + operand_b
                F::from_usize(fp) + field_repr[1]
            } else {
                F::ZERO
            };
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

            match instruction {
                Instruction::Poseidon2_16 { arg_a, arg_b, res } => {
                    let addr_input_a = arg_a.read_value(memory, fp).unwrap().to_usize();
                    let addr_input_b = arg_b.read_value(memory, fp).unwrap().to_usize();
                    let addr_output = res.read_value(memory, fp).unwrap().to_usize();
                    let value_a = memory.get_vector(addr_input_a).unwrap();
                    let value_b = memory.get_vector(addr_input_b).unwrap();
                    let output = memory.get_vectorized_slice(addr_output, 2).unwrap();
                    poseidons_16.push(WitnessPoseidon16 {
                        cycle: Some(cycle),
                        addr_input_a,
                        addr_input_b,
                        addr_output,
                        input: [value_a, value_b].concat().try_into().unwrap(),
                        output: output.try_into().unwrap(),
                    });
                }
                Instruction::Poseidon2_24 { arg_a, arg_b, res } => {
                    let addr_input_a = arg_a.read_value(memory, fp).unwrap().to_usize();
                    let addr_input_b = arg_b.read_value(memory, fp).unwrap().to_usize();
                    let addr_output = res.read_value(memory, fp).unwrap().to_usize();
                    let value_a = memory.get_vectorized_slice(addr_input_a, 2).unwrap();
                    let value_b = memory.get_vector(addr_input_b).unwrap().to_vec();
                    let output = memory.get_vector(addr_output).unwrap();
                    poseidons_24.push(WitnessPoseidon24 {
                        cycle: Some(cycle),
                        addr_input_a,
                        addr_input_b,
                        addr_output,
                        input: [value_a, value_b].concat().try_into().unwrap(),
                        output,
                    });
                }
                Instruction::DotProductExtensionExtension {
                    arg0,
                    arg1,
                    res,
                    size,
                } => {
                    let addr_0 = arg0.read_value(memory, fp).unwrap().to_usize();
                    let addr_1 = arg1.read_value(memory, fp).unwrap().to_usize();
                    let addr_res = res.read_value(memory, fp).unwrap().to_usize();
                    let slice_0 = memory
                        .get_vectorized_slice_extension(addr_0, *size)
                        .unwrap();
                    let slice_1 = memory
                        .get_vectorized_slice_extension(addr_1, *size)
                        .unwrap();
                    let res = memory.get_extension(addr_res).unwrap();
                    dot_products.push(WitnessDotProduct {
                        cycle,
                        addr_0,
                        addr_1,
                        addr_res,
                        len: *size,
                        slice_0,
                        slice_1,
                        res,
                    });
                }
                Instruction::MultilinearEval {
                    coeffs,
                    point,
                    res,
                    n_vars,
                } => {
                    let addr_coeffs = coeffs.read_value(memory, fp).unwrap().to_usize();
                    let addr_point = point.read_value(memory, fp).unwrap().to_usize();
                    let addr_res = res.read_value(memory, fp).unwrap().to_usize();
                    let point = memory
                        .get_vectorized_slice_extension(addr_point, *n_vars)
                        .unwrap();
                    let res = memory.get_extension(addr_res).unwrap();
                    vm_multilinear_evals.push(WitnessMultilinearEval {
                        cycle,
                        addr_coeffs,
                        addr_point,
                        addr_res,
                        n_vars: *n_vars,
                        point,
                        res,
                    });
                }
                _ => {}
            }
        }

        // repeat the last row to get to a power of two
        for t in trace
            .iter_mut()
            .take(N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS)
        {
            let last_value = t[n_cycles - 1];
            for tt in t
                .iter_mut()
                .take(1 << log_n_cycles_rounded_up)
                .skip(n_cycles)
            {
                *tt = last_value;
            }
        }

        let mut memory = memory
            .0
            .par_iter()
            .map(|&v| v.unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        memory.resize(
            memory
                .len()
                .next_multiple_of(execution_result.public_memory_size),
            F::ZERO,
        );

        let n_poseidons_16 = poseidons_16.len();
        let n_poseidons_24 = poseidons_24.len();

        let empty_poseidon16_output = build_poseidon16().permute([F::ZERO; 16]);
        let empty_poseidon24_output = build_poseidon24().permute([F::ZERO; 24])[16..24]
            .try_into()
            .unwrap();

        poseidons_16.resize_with(n_poseidons_16.next_power_of_two(), || WitnessPoseidon16 {
            cycle: None,
            addr_input_a: 0,
            addr_input_b: 0,
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            output: empty_poseidon16_output,
        });

        poseidons_24.resize_with(n_poseidons_24.next_power_of_two(), || WitnessPoseidon24 {
            cycle: None,
            addr_input_a: 0,
            addr_input_b: 0,
            addr_output: POSEIDON_24_NULL_HASH_PTR,
            input: [F::ZERO; 24],
            output: empty_poseidon24_output,
        });

        Self {
            full_trace: trace,
            n_poseidons_16,
            n_poseidons_24,
            poseidons_16,
            poseidons_24,
            dot_products,
            vm_multilinear_evals,
            public_memory_size: execution_result.public_memory_size,
            memory,
        }
    }
}

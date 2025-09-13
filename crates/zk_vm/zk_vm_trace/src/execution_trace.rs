use crate::instruction_encoder::field_representation;
use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C,
    COL_INDEX_MEM_VALUE_A, COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC,
    N_EXEC_COLUMNS, N_INSTRUCTION_COLUMNS,
};
use p3_field::PrimeCharacteristicRing;
use p3_field::{BasedVectorSpace, Field};
use p3_symmetric::Permutation;
use p3_util::log2_ceil_usize;
use rayon::prelude::*;
use utils::{ToUsize, get_poseidon16, get_poseidon24};
use vm::*;

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

#[derive(Debug)]
pub struct WitnessMultilinearEval {
    pub cycle: usize,
    pub addr_coeffs: usize, // vectorized pointer, of size 8.2^size
    pub addr_point: usize,  // vectorized pointer, of size `size`
    pub addr_res: usize,    // vectorized pointer
    pub n_vars: usize,
    pub point: Vec<EF>,
    pub res: EF,
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
                    .get_continuous_slice_of_ef_elements(addr_0, *size)
                    .unwrap();
                let slice_1 = memory
                    .get_continuous_slice_of_ef_elements(addr_1, *size)
                    .unwrap();
                let res = memory.get_ef_element(addr_res).unwrap();
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

                let log_point_size = log2_ceil_usize(*n_vars * DIMENSION);
                let point_slice = memory
                    .slice(addr_point << log_point_size, *n_vars * DIMENSION)
                    .unwrap();
                for i in *n_vars * DIMENSION..(*n_vars * DIMENSION).next_power_of_two() {
                    assert!(
                        memory
                            .get((addr_point << log_point_size) + i)
                            .unwrap()
                            .is_zero()
                    ); // padding
                }
                let point = point_slice[..*n_vars * DIMENSION]
                    .chunks_exact(DIMENSION)
                    .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
                    .collect::<Vec<_>>();

                let res = memory.get_vector(addr_res).unwrap();
                assert!(res[DIMENSION..].iter().all(|&x| x.is_zero()));
                vm_multilinear_evals.push(WitnessMultilinearEval {
                    cycle,
                    addr_coeffs,
                    addr_point,
                    addr_res,
                    n_vars: *n_vars,
                    point,
                    res: EF::from_basis_coefficients_slice(&res[..DIMENSION]).unwrap(),
                });
            }
            _ => {}
        }
    }

    // repeat the last row to get to a power of two
    for j in 0..N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS {
        let last_value = trace[j][n_cycles - 1];
        for i in n_cycles..(1 << log_n_cycles_rounded_up) {
            trace[j][i] = last_value;
        }
    }

    let memory = memory
        .0
        .par_iter()
        .map(|&v| v.unwrap_or(F::ZERO))
        .collect::<Vec<F>>();

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
        memory,
    }
}

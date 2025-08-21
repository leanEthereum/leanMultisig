use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, dot_product};
use p3_symmetric::Permutation;
use rayon::prelude::*;
use utils::{ToUsize, build_poseidon16, build_poseidon24, pretty_integer};
use whir_p3::poly::{evals::EvaluationsList, multilinear::MultilinearPoint};

use crate::{
    DIMENSION, EF, F, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR, PUBLIC_INPUT_START,
    ZERO_VEC_PTR,
    bytecode::{Bytecode, Hint, Instruction, MemOrConstant, MemOrFp, MemOrFpOrConstant},
};

const MAX_MEMORY_SIZE: usize = 1 << 23;

#[derive(Debug, Clone)]
pub enum RunnerError {
    OutOfMemory,
    MemoryAlreadySet,
    NotAPointer,
    DivByZero,
    NotEqual(F, F),
    UndefinedMemory,
    PCOutOfBounds,
}

impl ToString for RunnerError {
    fn to_string(&self) -> String {
        match self {
            Self::OutOfMemory => "Out of memory".to_string(),
            Self::MemoryAlreadySet => "Memory already set".to_string(),
            Self::NotAPointer => "Not a pointer".to_string(),
            Self::DivByZero => "Division by zero".to_string(),
            Self::NotEqual(expected, actual) => {
                format!("Computation Invalid: {expected} != {actual}")
            }
            Self::UndefinedMemory => "Undefined memory access".to_string(),
            Self::PCOutOfBounds => "Program counter out of bounds".to_string(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Memory(pub Vec<Option<F>>);

impl MemOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::Constant(c) => Ok(*c),
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
        }
    }

    #[must_use]
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::Constant(_) => Err(RunnerError::NotAPointer),
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
        }
    }
}

impl MemOrFp {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
        }
    }

    #[must_use]
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp => Err(RunnerError::NotAPointer),
        }
    }
}

impl MemOrFpOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
            Self::Constant(c) => Ok(*c),
        }
    }

    #[must_use]
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp | Self::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }
}

impl Memory {
    pub fn new(public_memory: Vec<F>) -> Self {
        Self(public_memory.into_par_iter().map(Some).collect::<Vec<_>>())
    }
    pub fn get(&self, index: usize) -> Result<F, RunnerError> {
        self.0
            .get(index)
            .and_then(|opt| *opt)
            .ok_or(RunnerError::UndefinedMemory)
    }

    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.0.len() {
            if index >= MAX_MEMORY_SIZE {
                return Err(RunnerError::OutOfMemory);
            }
            self.0.resize(index + 1, None);
        }
        if let Some(existing) = &mut self.0[index] {
            if *existing != value {
                return Err(RunnerError::MemoryAlreadySet);
            }
        } else {
            self.0[index] = Some(value);
        }
        Ok(())
    }

    pub fn get_vector(&self, index: usize) -> Result<[F; DIMENSION], RunnerError> {
        Ok(self.get_vectorized_slice(index, 1)?.try_into().unwrap())
    }

    pub fn get_extension(&self, index: usize) -> Result<EF, RunnerError> {
        Ok(EF::from_basis_coefficients_slice(&self.get_vector(index)?).unwrap())
    }

    pub fn get_vectorized_slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let mut vector = Vec::with_capacity(len * DIMENSION);
        for i in 0..len * DIMENSION {
            vector.push(self.get(index * DIMENSION + i)?);
        }
        Ok(vector)
    }

    pub fn get_vectorized_slice_extension<EF: ExtensionField<F>>(
        &self,
        index: usize,
        len: usize,
    ) -> Result<Vec<EF>, RunnerError> {
        let mut vector = Vec::with_capacity(len);
        for i in 0..len {
            let v = self.get_vector(index + i)?;
            vector.push(EF::from_basis_coefficients_slice(&v).unwrap());
        }
        Ok(vector)
    }

    pub fn slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let mut vector = Vec::with_capacity(len);
        for i in 0..len {
            vector.push(self.get(index + i)?);
        }
        Ok(vector)
    }

    pub fn set_vector(&mut self, index: usize, value: [F; DIMENSION]) -> Result<(), RunnerError> {
        for (i, v) in value.iter().enumerate() {
            let idx = DIMENSION * index + i;
            self.set(idx, *v)?;
        }
        Ok(())
    }

    pub fn set_vectorized_slice(&mut self, index: usize, value: &[F]) -> Result<(), RunnerError> {
        assert!(value.len() % DIMENSION == 0);
        for (i, v) in value.iter().enumerate() {
            let idx = DIMENSION * index + i;
            self.set(idx, *v)?;
        }
        Ok(())
    }
}

#[must_use]
pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
) -> ExecutionResult {
    let mut std_out = String::new();
    let first_exec = match execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        MAX_MEMORY_SIZE / 2,
        false,
        &mut std_out,
    ) {
        Ok(first_exec) => first_exec,
        Err(err) => {
            if !std_out.is_empty() {
                print!("{std_out}");
            }
            panic!("Error during bytecode execution: {}", err.to_string());
        }
    };
    execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        first_exec.no_vec_runtime_memory,
        true,
        &mut String::new(),
    )
    .unwrap()
}

#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
}

#[must_use]
pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);
    for pm in public_memory.iter_mut().take((ZERO_VEC_PTR + 2) * 8) {
        *pm = F::ZERO; // zero vector
    }
    public_memory[POSEIDON_16_NULL_HASH_PTR * 8..(POSEIDON_16_NULL_HASH_PTR + 2) * 8]
        .copy_from_slice(&build_poseidon16().permute([F::ZERO; 16]));
    public_memory[POSEIDON_24_NULL_HASH_PTR * 8..(POSEIDON_24_NULL_HASH_PTR + 1) * 8]
        .copy_from_slice(&build_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}

fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    final_execution: bool,
    std_out: &mut String,
) -> Result<ExecutionResult, RunnerError> {
    let poseidon_16 = build_poseidon16(); // TODO avoid rebuilding each time
    let poseidon_24 = build_poseidon24();

    // set public memory
    let mut memory = Memory::new(build_public_memory(public_input));

    let public_memory_size = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut fp = public_memory_size;

    for (i, value) in private_input.iter().enumerate() {
        memory.set(fp + i, *value)?;
    }
    fp += private_input.len();
    fp = fp.next_multiple_of(DIMENSION);

    let initial_ap = fp + bytecode.starting_frame_memory;
    let initial_ap_vec =
        (initial_ap + no_vec_runtime_memory).next_multiple_of(DIMENSION) / DIMENSION;

    let mut pc = 0;
    let mut ap = initial_ap;
    let mut ap_vec = initial_ap_vec;

    let mut poseidon16_calls = 0;
    let mut poseidon24_calls = 0;
    let mut dot_product_ext_ext_calls = 0;
    let mut dot_product_base_ext_calls = 0;
    let mut cpu_cycles = 0;

    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;
    let mut checkpoint_ap_vec = ap_vec;

    let mut pcs = Vec::new();
    let mut fps = Vec::new();

    while pc != bytecode.ending_pc {
        if pc >= bytecode.instructions.len() {
            return Err(RunnerError::PCOutOfBounds);
        }

        pcs.push(pc);
        fps.push(fp);

        cpu_cycles += 1;

        for hint in bytecode.hints.get(&pc).unwrap_or(&vec![]) {
            match hint {
                Hint::RequestMemory {
                    offset,
                    size,
                    vectorized,
                } => {
                    let size = size.read_value(&memory, fp)?.to_usize();

                    if *vectorized {
                        // find the next multiple of 8
                        memory.set(fp + *offset, F::from_usize(ap_vec))?;
                        ap_vec += size;
                    } else {
                        memory.set(fp + *offset, F::from_usize(ap))?;
                        ap += size;
                    }
                    // does not increase PC
                }
                Hint::DecomposeBits {
                    res_offset,
                    to_decompose,
                } => {
                    let to_decompose_value = to_decompose.read_value(&memory, fp)?.to_usize();
                    for i in 0..F::bits() {
                        let bit = if to_decompose_value & (1 << i) != 0 {
                            F::ONE
                        } else {
                            F::ZERO
                        };
                        memory.set(fp + *res_offset + i, bit)?;
                    }
                }
                Hint::Inverse { arg, res_offset } => {
                    let value = arg.read_value(&memory, fp)?;
                    let result = value.try_inverse().unwrap_or(F::ZERO);
                    memory.set(fp + *res_offset, result)?;
                }
                Hint::Print { line_info, content } => {
                    let values = content
                        .iter()
                        .map(|value| Ok(value.read_value(&memory, fp)?.to_string()))
                        .collect::<Result<Vec<_>, _>>()?;
                    // Logs for performance analysis:
                    if values[0] == "123456789" {
                        if values.len() == 1 {
                            *std_out += "[CHECKPOINT]\n";
                        } else {
                            assert_eq!(values.len(), 2);
                            let new_no_vec_memory = ap - checkpoint_ap;
                            let new_vec_memory = (ap_vec - checkpoint_ap_vec) * DIMENSION;
                            *std_out += &format!(
                                "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {} ({:.1}% vec)\n",
                                values[1],
                                pretty_integer(cpu_cycles - last_checkpoint_cpu_cycles),
                                pretty_integer(new_no_vec_memory + new_vec_memory),
                                new_vec_memory as f64 / (new_no_vec_memory + new_vec_memory) as f64
                                    * 100.0
                            );
                        }

                        last_checkpoint_cpu_cycles = cpu_cycles;
                        checkpoint_ap = ap;
                        checkpoint_ap_vec = ap_vec;
                        continue;
                    }

                    let line_info = line_info.replace(';', "");
                    *std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
                    // does not increase PC
                }
            }
        }

        let instruction = &bytecode.instructions[pc];
        match instruction {
            Instruction::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                if res.is_value_unknown(&memory, fp) {
                    let memory_address_res = res.memory_address(fp)?;
                    let a_value = arg_a.read_value(&memory, fp)?;
                    let b_value = arg_c.read_value(&memory, fp)?;
                    let res_value = operation.compute(a_value, b_value);
                    memory.set(memory_address_res, res_value)?;
                } else if arg_a.is_value_unknown(&memory, fp) {
                    let memory_address_a = arg_a.memory_address(fp)?;
                    let res_value = res.read_value(&memory, fp)?;
                    let b_value = arg_c.read_value(&memory, fp)?;
                    let a_value = operation
                        .inverse_compute(res_value, b_value)
                        .ok_or(RunnerError::DivByZero)?;
                    memory.set(memory_address_a, a_value)?;
                } else if arg_c.is_value_unknown(&memory, fp) {
                    let memory_address_b = arg_c.memory_address(fp)?;
                    let res_value = res.read_value(&memory, fp)?;
                    let a_value = arg_a.read_value(&memory, fp)?;
                    let b_value = operation
                        .inverse_compute(res_value, a_value)
                        .ok_or(RunnerError::DivByZero)?;
                    memory.set(memory_address_b, b_value)?;
                } else {
                    let a_value = arg_a.read_value(&memory, fp)?;
                    let b_value = arg_c.read_value(&memory, fp)?;
                    let res_value = res.read_value(&memory, fp)?;
                    let computed_value = operation.compute(a_value, b_value);
                    if res_value != computed_value {
                        return Err(RunnerError::NotEqual(computed_value, res_value));
                    }
                }

                pc += 1;
            }
            Instruction::Deref {
                shift_0,
                shift_1,
                res,
            } => {
                if res.is_value_unknown(&memory, fp) {
                    let memory_address_res = res.memory_address(fp)?;
                    let ptr = memory.get(fp + shift_0)?;
                    let value = memory.get(ptr.to_usize() + shift_1)?;
                    memory.set(memory_address_res, value)?;
                } else {
                    let value = res.read_value(&memory, fp)?;
                    let ptr = memory.get(fp + shift_0)?;
                    memory.set(ptr.to_usize() + shift_1, value)?;
                }
                pc += 1;
            }
            Instruction::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                let condition_value = condition.read_value(&memory, fp)?;
                assert!([F::ZERO, F::ONE].contains(&condition_value),);
                if condition_value == F::ZERO {
                    pc += 1;
                } else {
                    pc = dest.read_value(&memory, fp)?.to_usize();
                    fp = updated_fp.read_value(&memory, fp)?.to_usize();
                }
            }
            Instruction::Poseidon2_16 { arg_a, arg_b, res } => {
                poseidon16_calls += 1;

                let a_value = arg_a.read_value(&memory, fp)?;
                let b_value = arg_b.read_value(&memory, fp)?;
                let res_value = res.read_value(&memory, fp)?;

                let arg0 = memory.get_vector(a_value.to_usize())?;
                let arg1 = memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; DIMENSION * 2];
                input[..DIMENSION].copy_from_slice(&arg0);
                input[DIMENSION..].copy_from_slice(&arg1);

                poseidon_16.permute_mut(&mut input);

                let res0: [F; DIMENSION] = input[..DIMENSION].try_into().unwrap();
                let res1: [F; DIMENSION] = input[DIMENSION..].try_into().unwrap();

                memory.set_vector(res_value.to_usize(), res0)?;
                memory.set_vector(1 + res_value.to_usize(), res1)?;

                pc += 1;
            }
            Instruction::Poseidon2_24 { arg_a, arg_b, res } => {
                poseidon24_calls += 1;

                let a_value = arg_a.read_value(&memory, fp)?;
                let b_value = arg_b.read_value(&memory, fp)?;
                let res_value = res.read_value(&memory, fp)?;

                let arg0 = memory.get_vector(a_value.to_usize())?;
                let arg1 = memory.get_vector(1 + a_value.to_usize())?;
                let arg2 = memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; DIMENSION * 3];
                input[..DIMENSION].copy_from_slice(&arg0);
                input[DIMENSION..2 * DIMENSION].copy_from_slice(&arg1);
                input[2 * DIMENSION..].copy_from_slice(&arg2);

                poseidon_24.permute_mut(&mut input);

                let res: [F; DIMENSION] = input[2 * DIMENSION..].try_into().unwrap();

                memory.set_vector(res_value.to_usize(), res)?;

                pc += 1;
            }
            Instruction::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                dot_product_ext_ext_calls += 1;

                let ptr_arg_0 = arg0.read_value(&memory, fp)?.to_usize();
                let ptr_arg_1 = arg1.read_value(&memory, fp)?.to_usize();
                let ptr_res = res.read_value(&memory, fp)?.to_usize();

                let slice_0 = (ptr_arg_0..ptr_arg_0 + *size)
                    .map(|i| Ok(EF::from_basis_coefficients_slice(&memory.get_vector(i)?).unwrap()))
                    .collect::<Result<Vec<EF>, _>>()?;

                let slice_1 = (ptr_arg_1..ptr_arg_1 + *size)
                    .map(|i| Ok(EF::from_basis_coefficients_slice(&memory.get_vector(i)?).unwrap()))
                    .collect::<Result<Vec<EF>, _>>()?;

                let dot_product = dot_product::<EF, _, _>(slice_0.into_iter(), slice_1.into_iter())
                    .as_basis_coefficients_slice()
                    .try_into()
                    .unwrap();
                memory.set_vector(ptr_res, dot_product)?;

                pc += 1;
            }
            Instruction::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                dot_product_base_ext_calls += 1;

                let ptr_coeffs = coeffs.read_value(&memory, fp)?.to_usize();
                let ptr_point = point.read_value(&memory, fp)?.to_usize();
                let ptr_res = res.read_value(&memory, fp)?.to_usize();
                let slice_coeffs = (ptr_coeffs << *n_vars..(1 + ptr_coeffs) << *n_vars)
                    .map(|i| memory.get(i))
                    .collect::<Result<Vec<F>, _>>()?;
                let point = (ptr_point..ptr_point + *n_vars)
                    .map(|i| Ok(EF::from_basis_coefficients_slice(&memory.get_vector(i)?).unwrap()))
                    .collect::<Result<Vec<EF>, _>>()?;

                let eval = slice_coeffs.evaluate(&MultilinearPoint(point.clone()));
                let eval_base: [F; 8] = eval.as_basis_coefficients_slice().try_into().unwrap();
                memory.set_vector(ptr_res, eval_base)?;

                pc += 1;
            }
        }
    }

    debug_assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    if final_execution {
        if !std_out.is_empty() {
            print!("{std_out}");
        }
        let runtime_memory_size = memory.0.len() - (PUBLIC_INPUT_START + public_input.len());
        println!(
            "\nBytecode size: {}",
            pretty_integer(bytecode.instructions.len())
        );
        println!("Public input size: {}", pretty_integer(public_input.len()));
        println!(
            "Private input size: {}",
            pretty_integer(private_input.len())
        );
        println!("Executed {} instructions", pretty_integer(cpu_cycles));
        println!(
            "Runtime memory: {} ({:.2}% vec)",
            pretty_integer(runtime_memory_size),
            (DIMENSION * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0
        );
        if poseidon16_calls + poseidon24_calls > 0 {
            println!(
                "Poseidon2_16 calls: {}, Poseidon2_24 calls: {} (1 poseidon per {} instructions)",
                pretty_integer(poseidon16_calls),
                pretty_integer(poseidon24_calls),
                cpu_cycles / (poseidon16_calls + poseidon24_calls)
            );
        }
        if dot_product_ext_ext_calls > 0 {
            println!(
                "DotProductExtExt calls: {}",
                pretty_integer(dot_product_ext_ext_calls)
            );
        }
        if dot_product_base_ext_calls > 0 {
            println!(
                "DotProductBaseExt calls: {}",
                pretty_integer(dot_product_base_ext_calls)
            );
        }
        let used_memory_cells = memory
            .0
            .iter()
            .skip(PUBLIC_INPUT_START + public_input.len())
            .filter(|&&x| x.is_some())
            .count();
        println!(
            "Memory usage: {:.1}%",
            used_memory_cells as f64 / runtime_memory_size as f64 * 100.0
        );
    }
    let no_vec_runtime_memory = ap - initial_ap;
    Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
    })
}

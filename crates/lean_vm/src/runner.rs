use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use p3_field::dot_product;
use p3_util::log2_ceil_usize;
use std::collections::BTreeMap;
use utils::ToUsize;
use utils::get_poseidon16;
use utils::get_poseidon24;
use utils::pretty_integer;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;

use crate::lean_isa::*;
use crate::profiler::profiling_report;
use crate::stack_trace::pretty_stack_trace;
use crate::*;
use p3_field::Field;
use p3_symmetric::Permutation;

const STACK_TRACE_INSTRUCTIONS: usize = 5000;

impl MemOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::Constant(c) => Ok(*c),
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
        }
    }

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

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp => Err(RunnerError::NotAPointer),
            Self::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ExecutionHistory {
    pub(crate) lines: Vec<LocationInSourceCode>,
    pub(crate) cycles: Vec<usize>, // for each line, how many cycles it took
}

pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    source_code: &str,                            // debug purpose
    function_locations: &BTreeMap<usize, String>, // debug purpose
    profiler: bool,
) -> ExecutionResult {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::default();
    let first_exec = match execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        MAX_RUNNER_MEMORY_SIZE / 2,
        false,
        &mut std_out,
        &mut instruction_history,
        false,
        function_locations,
    ) {
        Ok(first_exec) => first_exec,
        Err(err) => {
            let lines_history = &instruction_history.lines;
            let latest_instructions =
                &lines_history[lines_history.len().saturating_sub(STACK_TRACE_INSTRUCTIONS)..];
            println!(
                "\n{}",
                pretty_stack_trace(source_code, latest_instructions, function_locations)
            );
            if !std_out.is_empty() {
                println!("╔══════════════════════════════════════════════════════════════╗");
                println!("║                         STD-OUT                              ║");
                println!("╚══════════════════════════════════════════════════════════════╝\n");
                print!("{std_out}");
            }
            panic!("Error during bytecode execution: {err}");
        }
    };
    instruction_history = ExecutionHistory::default();
    execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        first_exec.no_vec_runtime_memory,
        true,
        &mut String::new(),
        &mut instruction_history,
        profiler,
        function_locations,
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
    pub vm_poseidon16_events: Vec<VmPoseidon16Event>,
    pub vm_poseidon24_events: Vec<VmPoseidon24Event>,
    pub vm_dot_product_events: Vec<VmDotProductEvent>,
    pub vm_multilinear_eval_events: Vec<VmMultilinearEvalEvent>,
}

pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);

    // "zero" vector
    let zero_start = ZERO_VEC_PTR * VECTOR_LEN;
    for slot in public_memory
        .iter_mut()
        .skip(zero_start)
        .take(2 * VECTOR_LEN)
    {
        *slot = F::ZERO;
    }

    // "one" vector
    public_memory[ONE_VEC_PTR * VECTOR_LEN] = F::ONE;
    let one_start = ONE_VEC_PTR * VECTOR_LEN + 1;
    for slot in public_memory
        .iter_mut()
        .skip(one_start)
        .take(VECTOR_LEN - 1)
    {
        *slot = F::ZERO;
    }

    public_memory
        [POSEIDON_16_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_16_NULL_HASH_PTR + 2) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon16().permute([F::ZERO; 16]));
    public_memory
        [POSEIDON_24_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_24_NULL_HASH_PTR + 1) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}

#[allow(clippy::too_many_arguments)] // TODO
fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    final_execution: bool,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiler: bool,
    function_locations: &BTreeMap<usize, String>,
) -> Result<ExecutionResult, RunnerError> {
    let poseidon_16 = get_poseidon16();
    let poseidon_24 = get_poseidon24();

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
        (initial_ap + no_vec_runtime_memory).next_multiple_of(VECTOR_LEN) / VECTOR_LEN;

    let mut pc = 0;
    let mut ap = initial_ap;
    let mut ap_vec = initial_ap_vec;

    let mut poseidon16_calls = 0;
    let mut poseidon24_calls = 0;
    let mut dot_product_ext_ext_calls = 0;
    let mut multilinear_eval_calls = 0;
    let mut cpu_cycles = 0;

    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;
    let mut checkpoint_ap_vec = ap_vec;

    let mut pcs = Vec::new();
    let mut fps = Vec::new();

    // Events collected only in final execution
    let mut vm_poseidon16_events: Vec<VmPoseidon16Event> = Vec::new();
    let mut vm_poseidon24_events: Vec<VmPoseidon24Event> = Vec::new();
    let mut vm_dot_product_events: Vec<VmDotProductEvent> = Vec::new();
    let mut vm_multilinear_eval_events: Vec<VmMultilinearEvalEvent> = Vec::new();

    let mut add_counts = 0;
    let mut mul_counts = 0;
    let mut deref_counts = 0;
    let mut jump_counts = 0;

    let mut counter_hint = 0;
    let mut cpu_cycles_before_new_line = 0;

    while pc != bytecode.ending_pc {
        if pc >= bytecode.instructions.len() {
            return Err(RunnerError::PCOutOfBounds);
        }

        pcs.push(pc);
        fps.push(fp);

        cpu_cycles += 1;
        cpu_cycles_before_new_line += 1;

        for hint in bytecode.hints.get(&pc).unwrap_or(&vec![]) {
            match hint {
                Hint::RequestMemory {
                    offset,
                    size,
                    vectorized,
                    vectorized_len,
                } => {
                    let size = size.read_value(&memory, fp)?.to_usize();

                    if *vectorized {
                        assert!(*vectorized_len >= LOG_VECTOR_LEN, "TODO");

                        // padding:
                        while !(ap_vec * VECTOR_LEN).is_multiple_of(1 << *vectorized_len) {
                            ap_vec += 1;
                        }
                        memory.set(
                            fp + *offset,
                            F::from_usize(ap_vec >> (*vectorized_len - LOG_VECTOR_LEN)),
                        )?;
                        ap_vec += size << (*vectorized_len - LOG_VECTOR_LEN);
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
                    let mut memory_index = fp + *res_offset;
                    for value_source in to_decompose {
                        let value = value_source.read_value(&memory, fp)?.to_usize();
                        for i in 0..F::bits() {
                            let bit = F::from_bool(value & (1 << i) != 0);
                            memory.set(memory_index, bit)?;
                            memory_index += 1;
                        }
                    }
                }
                Hint::CounterHint { res_offset } => {
                    memory.set(fp + *res_offset, F::from_usize(counter_hint))?;
                    counter_hint += 1;
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
                Hint::LocationReport { location } => {
                    instruction_history.lines.push(*location);
                    instruction_history.cycles.push(cpu_cycles_before_new_line);
                    cpu_cycles_before_new_line = 0;
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

                match operation {
                    Operation::Add => add_counts += 1,
                    Operation::Mul => mul_counts += 1,
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

                deref_counts += 1;
                pc += 1;
            }
            Instruction::Jump {
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

                jump_counts += 1;
            }
            Instruction::Poseidon2_16 { arg_a, arg_b, res } => {
                poseidon16_calls += 1;

                let a_value = arg_a.read_value(&memory, fp)?;
                let b_value = arg_b.read_value(&memory, fp)?;
                let res_value = res.read_value(&memory, fp)?;

                let arg0 = memory.get_vector(a_value.to_usize())?;
                let arg1 = memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; VECTOR_LEN * 2];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..].copy_from_slice(&arg1);

                // Keep a copy of the input before permutation for event recording
                let input_before = input;
                poseidon_16.permute_mut(&mut input);

                let res0: [F; VECTOR_LEN] = input[..VECTOR_LEN].try_into().unwrap();
                let res1: [F; VECTOR_LEN] = input[VECTOR_LEN..].try_into().unwrap();

                memory.set_vector(res_value.to_usize(), res0)?;
                memory.set_vector(1 + res_value.to_usize(), res1)?;

                if final_execution {
                    let cycle = pcs.len() - 1;
                    let addr_input_a = a_value.to_usize();
                    let addr_input_b = b_value.to_usize();
                    let addr_output = res_value.to_usize();
                    // Build output by concatenating the two result vectors we wrote to memory
                    let output: [F; 16] = [res0.as_slice(), res1.as_slice()]
                        .concat()
                        .try_into()
                        .unwrap();
                    vm_poseidon16_events.push(VmPoseidon16Event {
                        cycle,
                        addr_input_a,
                        addr_input_b,
                        addr_output,
                        input: input_before,
                        output,
                    });
                }

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

                let mut input = [F::ZERO; VECTOR_LEN * 3];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
                input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

                // Keep a copy of the input before permutation for event recording
                let input_before = input;
                poseidon_24.permute_mut(&mut input);

                let res: [F; VECTOR_LEN] = input[2 * VECTOR_LEN..].try_into().unwrap();

                memory.set_vector(res_value.to_usize(), res)?;

                if final_execution {
                    let cycle = pcs.len() - 1;
                    let addr_input_a = a_value.to_usize();
                    let addr_input_b = b_value.to_usize();
                    let addr_output = res_value.to_usize();
                    vm_poseidon24_events.push(VmPoseidon24Event {
                        cycle,
                        addr_input_a,
                        addr_input_b,
                        addr_output,
                        input: input_before,
                        output: res,
                    });
                }

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

                let slice_0 = memory.get_continuous_slice_of_ef_elements(ptr_arg_0, *size)?;
                let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1, *size)?;

                let dot_product =
                    dot_product::<EF, _, _>(slice_0.iter().copied(), slice_1.iter().copied());
                memory.set_ef_element(ptr_res, dot_product)?;

                if final_execution {
                    let cycle = pcs.len() - 1;
                    vm_dot_product_events.push(VmDotProductEvent {
                        cycle,
                        addr_0: ptr_arg_0,
                        addr_1: ptr_arg_1,
                        addr_res: ptr_res,
                        len: *size,
                        slice_0: slice_0.clone(),
                        slice_1: slice_1.clone(),
                        res: dot_product,
                    });
                }

                pc += 1;
            }
            Instruction::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                multilinear_eval_calls += 1;

                let ptr_coeffs = coeffs.read_value(&memory, fp)?.to_usize();
                let ptr_point = point.read_value(&memory, fp)?.to_usize();
                let ptr_res = res.read_value(&memory, fp)?.to_usize();
                let n_coeffs = 1 << *n_vars;
                let slice_coeffs = memory.slice(ptr_coeffs << *n_vars, n_coeffs)?;

                let log_point_size = log2_ceil_usize(*n_vars * DIMENSION);
                let point_slice = memory.slice(ptr_point << log_point_size, *n_vars * DIMENSION)?;
                for i in *n_vars * DIMENSION..(*n_vars * DIMENSION).next_power_of_two() {
                    memory.set((ptr_point << log_point_size) + i, F::ZERO)?; // padding
                }
                let point = point_slice[..*n_vars * DIMENSION]
                    .chunks_exact(DIMENSION)
                    .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
                    .collect::<Vec<_>>();

                let eval = slice_coeffs.evaluate(&MultilinearPoint(point.clone()));
                let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
                res_vec.resize(VECTOR_LEN, F::ZERO);
                memory.set_vector(ptr_res, res_vec.try_into().unwrap())?;

                if final_execution {
                    let cycle = pcs.len() - 1;
                    vm_multilinear_eval_events.push(VmMultilinearEvalEvent {
                        cycle,
                        addr_coeffs: ptr_coeffs,
                        addr_point: ptr_point,
                        addr_res: ptr_res,
                        n_vars: *n_vars,
                        point,
                        res: eval,
                    });
                }

                pc += 1;
            }
        }
    }

    debug_assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    if final_execution {
        // Ensure event counts match call counts in final execution
        debug_assert_eq!(poseidon16_calls, vm_poseidon16_events.len());
        debug_assert_eq!(poseidon24_calls, vm_poseidon24_events.len());
        debug_assert_eq!(dot_product_ext_ext_calls, vm_dot_product_events.len());
        debug_assert_eq!(multilinear_eval_calls, vm_multilinear_eval_events.len());
        if profiler {
            let report = profiling_report(instruction_history, function_locations);
            println!("\n{report}");
        }
        if !std_out.is_empty() {
            println!("╔═════════════════════════════════════════════════════════════════════════╗");
            println!("║                                STD-OUT                                  ║");
            println!("╚═════════════════════════════════════════════════════════════════════════╝");
            print!("\n{std_out}");
            println!(
                "──────────────────────────────────────────────────────────────────────────\n"
            );
        }

        println!("╔═════════════════════════════════════════════════════════════════════════╗");
        println!("║                                 STATS                                   ║");
        println!("╚═════════════════════════════════════════════════════════════════════════╝\n");

        println!("CYCLES: {}", pretty_integer(cpu_cycles));
        println!("MEMORY: {}", pretty_integer(memory.0.len()));
        println!();

        let runtime_memory_size = memory.0.len() - (PUBLIC_INPUT_START + public_input.len());
        println!(
            "Bytecode size: {}",
            pretty_integer(bytecode.instructions.len())
        );
        println!("Public input size: {}", pretty_integer(public_input.len()));
        println!(
            "Private input size: {}",
            pretty_integer(private_input.len())
        );
        println!(
            "Runtime memory: {} ({:.2}% vec)",
            pretty_integer(runtime_memory_size),
            (DIMENSION * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0
        );
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

        println!();

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
                "DotProduct calls: {}",
                pretty_integer(dot_product_ext_ext_calls)
            );
        }
        if multilinear_eval_calls > 0 {
            println!(
                "MultilinearEval calls: {}",
                pretty_integer(multilinear_eval_calls)
            );
        }

        if false {
            println!("Low level instruction counts:");
            println!(
                "COMPUTE: {} ({} ADD, {} MUL)",
                add_counts + mul_counts,
                add_counts,
                mul_counts
            );
            println!("DEREF: {deref_counts}");
            println!("JUMP: {jump_counts}");
        }

        println!("──────────────────────────────────────────────────────────────────────────\n");
    }

    let no_vec_runtime_memory = ap - initial_ap;
    Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
        vm_poseidon16_events,
        vm_poseidon24_events,
        vm_dot_product_events,
        vm_multilinear_eval_events,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::BasedVectorSpace;
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

        assert_eq!(execution_result.vm_poseidon16_events.len(), 1);
        assert_eq!(execution_result.vm_poseidon24_events.len(), 1);
        assert_eq!(execution_result.vm_dot_product_events.len(), 1);
        assert_eq!(execution_result.vm_multilinear_eval_events.len(), 1);

        let poseidon16_event = &execution_result.vm_poseidon16_events[0];
        assert_eq!(poseidon16_event.cycle, 0);
        assert_eq!(poseidon16_event.addr_input_a, POSEIDON16_ARG_A_PTR);
        assert_eq!(poseidon16_event.addr_input_b, POSEIDON16_ARG_B_PTR);

        let poseidon16_res_ptr = execution_result
            .memory
            .get(execution_result.fps[poseidon16_event.cycle] + POSEIDON16_RES_OFFSET)
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

        let poseidon24_event = &execution_result.vm_poseidon24_events[0];
        assert_eq!(poseidon24_event.cycle, 1);
        assert_eq!(poseidon24_event.addr_input_a, POSEIDON24_ARG_A_PTR);
        assert_eq!(poseidon24_event.addr_input_b, POSEIDON24_ARG_B_PTR);

        let poseidon24_res_ptr = execution_result
            .memory
            .get(execution_result.fps[poseidon24_event.cycle] + POSEIDON24_RES_OFFSET)
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

        let dot_event = &execution_result.vm_dot_product_events[0];
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

        let mle_event = &execution_result.vm_multilinear_eval_events[0];
        assert_eq!(mle_event.cycle, 3);
        assert_eq!(mle_event.addr_coeffs, MLE_COEFF_PTR);
        assert_eq!(mle_event.addr_point, MLE_POINT_PTR);

        let mle_res_ptr = execution_result
            .memory
            .get(execution_result.fps[mle_event.cycle] + MLE_RES_OFFSET)
            .unwrap()
            .to_usize();
        assert_eq!(mle_event.addr_res, mle_res_ptr);

        let expected_point =
            vec![EF::from_basis_coefficients_slice(&MLE_POINT_VALUES.map(f)).unwrap()];
        assert_eq!(mle_event.point, expected_point);

        let mle_res_vec = execution_result
            .memory
            .get_vector(mle_event.addr_res)
            .unwrap();
        let mle_res_coeffs: [F; DIMENSION] = mle_res_vec[..DIMENSION].try_into().unwrap();
        let mle_res = EF::from_basis_coefficients_slice(&mle_res_coeffs).unwrap();
        assert_eq!(mle_event.res, mle_res);
    }

    #[test]
    fn vm_precompile_events_only_final_pass() {
        let (bytecode, public_input) = build_test_case();
        let mut std_out = String::new();
        let mut history = ExecutionHistory::default();

        let first_pass = execute_bytecode_helper(
            &bytecode,
            &public_input,
            &[],
            MAX_RUNNER_MEMORY_SIZE / 2,
            false,
            &mut std_out,
            &mut history,
            false,
            &BTreeMap::new(),
        )
        .expect("first execution should succeed");

        assert!(first_pass.vm_poseidon16_events.is_empty());
        assert!(first_pass.vm_poseidon24_events.is_empty());
        assert!(first_pass.vm_dot_product_events.is_empty());
        assert!(first_pass.vm_multilinear_eval_events.is_empty());

        let mut history_final = ExecutionHistory::default();
        let final_pass = execute_bytecode_helper(
            &bytecode,
            &public_input,
            &[],
            first_pass.no_vec_runtime_memory,
            true,
            &mut String::new(),
            &mut history_final,
            false,
            &BTreeMap::new(),
        )
        .expect("final execution should succeed");

        assert_eq!(final_pass.vm_poseidon16_events.len(), 1);
        assert_eq!(final_pass.vm_poseidon24_events.len(), 1);
        assert_eq!(final_pass.vm_dot_product_events.len(), 1);
        assert_eq!(final_pass.vm_multilinear_eval_events.len(), 1);
    }
}

use p3_field::PrimeCharacteristicRing;
use p3_field::dot_product;
use std::collections::BTreeMap;
use utils::ToUsize;
use utils::get_poseidon16;
use utils::get_poseidon24;
use utils::pretty_integer;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;

use crate::bytecode::*;
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
        MAX_MEMORY_SIZE / 2,
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
}

pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);

    // "zero" vector
    for i in ZERO_VEC_PTR * VECTOR_LEN..(ZERO_VEC_PTR + 2) * VECTOR_LEN {
        public_memory[i] = F::ZERO;
    }

    // "one" vector
    public_memory[ONE_VEC_PTR * VECTOR_LEN] = F::ONE;
    for i in ONE_VEC_PTR * VECTOR_LEN + 1..(ONE_VEC_PTR + 1) * VECTOR_LEN {
        public_memory[i] = F::ZERO;
    }

    public_memory
        [POSEIDON_16_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_16_NULL_HASH_PTR + 2) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon16().permute([F::ZERO; 16]));
    public_memory
        [POSEIDON_24_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_24_NULL_HASH_PTR + 1) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}

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
        (initial_ap + no_vec_runtime_memory).next_multiple_of(DIMENSION) / DIMENSION;

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
                } => {
                    let size = size.read_value(&memory, fp)?.to_usize();

                    if *vectorized {
                        // find the next multiple of VECTOR_LEN
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

                poseidon_16.permute_mut(&mut input);

                let res0: [F; VECTOR_LEN] = input[..VECTOR_LEN].try_into().unwrap();
                let res1: [F; VECTOR_LEN] = input[VECTOR_LEN..].try_into().unwrap();

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

                let mut input = [F::ZERO; VECTOR_LEN * 3];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
                input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

                poseidon_24.permute_mut(&mut input);

                let res: [F; VECTOR_LEN] = input[2 * VECTOR_LEN..].try_into().unwrap();

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

                let slice_0 = memory.get_continuous_slice_of_ef_elements(ptr_arg_0, *size)?;
                let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1, *size)?;

                let dot_product = dot_product::<EF, _, _>(slice_0.into_iter(), slice_1.into_iter());
                memory.set_ef_element(ptr_res, dot_product)?;

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
                let point = memory.get_continuous_slice_of_ef_elements(ptr_point, *n_vars)?;

                let eval = slice_coeffs.evaluate(&MultilinearPoint(point));
                memory.set_ef_element(ptr_res, eval)?;

                pc += 1;
            }
        }
    }

    debug_assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    if final_execution {
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
    })
}

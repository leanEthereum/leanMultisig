//! VM execution runner

use crate::core::{
    DIMENSION, F, ONE_VEC_PTR, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR,
    PUBLIC_INPUT_START, VECTOR_LEN, ZERO_VEC_PTR,
};
use crate::diagnostics::{ExecutionResult, RunnerError};
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::Bytecode;
use crate::isa::instruction::InstructionContext;
use crate::witness::{
    WitnessDotProduct, WitnessMultilinearEval, WitnessPoseidon16, WitnessPoseidon24,
};
use crate::{CodeAddress, HintExecutionContext, SourceLineNumber};
use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use std::collections::BTreeMap;
use utils::{get_poseidon16, get_poseidon24, pretty_integer};

/// Number of instructions to show in stack trace
const STACK_TRACE_INSTRUCTIONS: usize = 5000;

/// Build public memory with standard initialization
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

/// Execute bytecode with the given inputs and execution context
///
/// This is the main VM execution entry point that processes bytecode instructions
/// and generates execution traces with witness data.
pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    source_code: &str,
    function_locations: &BTreeMap<usize, String>,
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    profiler: bool,
) -> ExecutionResult {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::new();
    let result = execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        no_vec_runtime_memory,
        &mut std_out,
        &mut instruction_history,
        profiler,
        function_locations,
    )
    .unwrap_or_else(|err| {
        let lines_history = &instruction_history.lines;
        let latest_instructions =
            &lines_history[lines_history.len().saturating_sub(STACK_TRACE_INSTRUCTIONS)..];
        println!(
            "\n{}",
            crate::diagnostics::pretty_stack_trace(
                source_code,
                latest_instructions,
                function_locations
            )
        );
        if !std_out.is_empty() {
            println!("╔══════════════════════════════════════════════════════════════╗");
            println!("║                         STD-OUT                              ║");
            println!("╚══════════════════════════════════════════════════════════════╝\n");
            print!("{std_out}");
        }
        panic!("Error during bytecode execution: {err}");
    });
    if profiler {
        print_line_cycle_counts(instruction_history);
        print_instruction_cycle_counts(bytecode, result.pcs.clone());
    }
    result
}

fn print_line_cycle_counts(history: ExecutionHistory) {
    println!("Line by line cycle counts");
    println!("=========================\n");

    let mut gross_cycle_counts: BTreeMap<SourceLineNumber, usize> = BTreeMap::new();
    for (line, cycle_count) in history.lines.iter().zip(history.lines_cycles.iter()) {
        let prev_count = gross_cycle_counts.get(line).unwrap_or(&0);
        gross_cycle_counts.insert(*line, *prev_count + cycle_count);
    }
    for (line, cycle_count) in gross_cycle_counts.iter() {
        println!("line {line}: {cycle_count} cycles");
    }
    println!();
}

fn print_instruction_cycle_counts(bytecode: &Bytecode, pcs: Vec<CodeAddress>) {
    println!("Instruction level cycle counts");
    println!("==============================");

    let mut gross_cycle_counts: BTreeMap<CodeAddress, usize> = BTreeMap::new();
    for pc in pcs.iter() {
        let prev_count = gross_cycle_counts.get(pc).unwrap_or(&0);
        gross_cycle_counts.insert(*pc, *prev_count + 1);
    }
    for (pc, cycle_count) in gross_cycle_counts.iter() {
        let instruction = &bytecode.instructions[*pc];
        let hints = bytecode.hints.get(pc);
        if let Some(hints) = hints {
            for hint in hints {
                println!("hint: {hint}");
            }
        }
        println!("pc {pc}: {cycle_count} cycles: {instruction}");
    }
    println!();
}

/// Helper function that performs the actual bytecode execution
#[allow(clippy::too_many_arguments)] // TODO
fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiler: bool,
    function_locations: &BTreeMap<usize, String>,
) -> Result<ExecutionResult, RunnerError> {
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

    let mut cpu_cycles = 0;

    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;
    let mut checkpoint_ap_vec = ap_vec;

    let mut pcs = Vec::new();
    let mut fps = Vec::new();

    // Events collected only in final execution
    let mut poseidons_16: Vec<WitnessPoseidon16> = Vec::new();
    let mut poseidons_24: Vec<WitnessPoseidon24> = Vec::new();
    let mut dot_products: Vec<WitnessDotProduct> = Vec::new();
    let mut multilinear_evals: Vec<WitnessMultilinearEval> = Vec::new();

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
            let mut hint_ctx = HintExecutionContext {
                memory: &mut memory,
                fp,
                ap: &mut ap,
                ap_vec: &mut ap_vec,
                counter_hint: &mut counter_hint,
                std_out,
                instruction_history,
                cpu_cycles_before_new_line: &mut cpu_cycles_before_new_line,
                cpu_cycles,
                last_checkpoint_cpu_cycles: &mut last_checkpoint_cpu_cycles,
                checkpoint_ap: &mut checkpoint_ap,
                checkpoint_ap_vec: &mut checkpoint_ap_vec,
            };
            hint.execute_hint(&mut hint_ctx)?;
        }

        let instruction = &bytecode.instructions[pc];
        let mut instruction_ctx = InstructionContext {
            memory: &mut memory,
            fp: &mut fp,
            pc: &mut pc,
            pcs: &pcs,
            poseidons_16: &mut poseidons_16,
            poseidons_24: &mut poseidons_24,
            dot_products: &mut dot_products,
            multilinear_evals: &mut multilinear_evals,
            add_counts: &mut add_counts,
            mul_counts: &mut mul_counts,
            deref_counts: &mut deref_counts,
            jump_counts: &mut jump_counts,
        };
        instruction.execute_instruction(&mut instruction_ctx)?;
    }

    assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    let no_vec_runtime_memory = ap - initial_ap;

    // Ensure event counts match call counts in final execution
    if profiler {
        let report = crate::diagnostics::profiling_report(instruction_history, function_locations);
        println!("\n{report}");
    }
    if !std_out.is_empty() {
        println!("╔═════════════════════════════════════════════════════════════════════════╗");
        println!("║                                STD-OUT                                  ║");
        println!("╚═════════════════════════════════════════════════════════════════════════╝");
        print!("\n{std_out}");
        println!("──────────────────────────────────────────────────────────────────────────\n");
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
        "Runtime memory: {} ({:.2}% vec) (no vec mem: {})",
        pretty_integer(runtime_memory_size),
        (VECTOR_LEN * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0,
        no_vec_runtime_memory
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

    if poseidons_16.len() + poseidons_24.len() > 0 {
        println!(
            "Poseidon2_16 calls: {}, Poseidon2_24 calls: {} (1 poseidon per {} instructions)",
            pretty_integer(poseidons_16.len()),
            pretty_integer(poseidons_24.len()),
            cpu_cycles / (poseidons_16.len() + poseidons_24.len())
        );
    }
    if !dot_products.is_empty() {
        println!("DotProduct calls: {}", pretty_integer(dot_products.len()));
    }
    if !multilinear_evals.is_empty() {
        println!(
            "MultilinearEval calls: {}",
            pretty_integer(multilinear_evals.len())
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

    Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
        poseidons_16,
        poseidons_24,
        dot_products,
        multilinear_evals,
    })
}

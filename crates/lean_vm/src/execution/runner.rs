//! VM execution runner

use crate::core::{
    DIMENSION, F, FileId, NONRESERVED_PROGRAM_INPUT_START, ONE_VEC_PTR, POSEIDON_16_NULL_HASH_PTR, VECTOR_LEN,
    ZERO_VEC_PTR,
};
use crate::diagnostics::{ExecutionResult, MemoryProfile, RunnerError, memory_profiling_report};
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::Bytecode;
use crate::isa::instruction::InstructionContext;
use crate::{
    ALL_TABLES, CodeAddress, ENDING_PC, HintExecutionContext, N_TABLES, STARTING_PC, SourceLocation, Table, TableTrace,
    UNIVARIATE_SELECTORS_PTR, UNIVARIATE_SKIPS,
};
use multilinear_toolkit::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use utils::{poseidon16_permute, pretty_integer};
use xmss::Poseidon16History;

/// Number of instructions to show in stack trace
const STACK_TRACE_INSTRUCTIONS: usize = 5000;

/// Build public memory with standard initialization
pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (NONRESERVED_PROGRAM_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[NONRESERVED_PROGRAM_INPUT_START..][..public_input.len()].copy_from_slice(public_input);

    // "zero" vector
    let zero_start = ZERO_VEC_PTR;
    for slot in public_memory.iter_mut().skip(zero_start).take(2 * VECTOR_LEN) {
        *slot = F::ZERO;
    }

    // "one" vector
    public_memory[ONE_VEC_PTR] = F::ONE;
    for slot in public_memory.iter_mut().skip(ONE_VEC_PTR + 1).take(VECTOR_LEN - 1) {
        *slot = F::ZERO;
    }

    public_memory[POSEIDON_16_NULL_HASH_PTR..][..2 * VECTOR_LEN].copy_from_slice(&poseidon16_permute([F::ZERO; 16]));
    for (i, pol) in univariate_selectors::<F>(UNIVARIATE_SKIPS).iter().enumerate() {
        public_memory[UNIVARIATE_SELECTORS_PTR + i * (1 << UNIVARIATE_SKIPS)..][..(1 << UNIVARIATE_SKIPS)]
            .copy_from_slice(&pol.coeffs);
    }
    public_memory
}

/// Execute bytecode with the given inputs and execution context, returning a Result
///
/// This is the main VM execution entry point that processes bytecode instructions
/// and generates execution traces with witness data.
pub fn try_execute_bytecode(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    profiling: bool,
    poseidons_16_precomputed: &Poseidon16History,
) -> Result<ExecutionResult, RunnerError> {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::new();
    let result = execute_bytecode_helper(
        bytecode,
        (public_input, private_input),
        &mut std_out,
        &mut instruction_history,
        profiling,
        poseidons_16_precomputed,
    )
    .map_err(|(last_pc, err)| {
        let lines_history = &instruction_history.lines;
        let latest_instructions = &lines_history[lines_history.len().saturating_sub(STACK_TRACE_INSTRUCTIONS)..];
        eprintln!(
            "\n{}",
            crate::diagnostics::pretty_stack_trace(
                &bytecode.source_code,
                latest_instructions,
                &bytecode.function_locations,
                &bytecode.filepaths,
                last_pc
            )
        );
        if !std_out.is_empty() {
            eprintln!("╔══════════════════════════════════════════════════════════════╗");
            eprintln!("║                         STD-OUT                              ║");
            eprintln!("╚══════════════════════════════════════════════════════════════╝\n");
            eprint!("{std_out}");
        }
        err
    })?;
    if profiling {
        print_line_cycle_counts(instruction_history, &bytecode.filepaths);
        print_instruction_cycle_counts(bytecode, result.pcs.clone());
        if let Some(ref mem_profile) = result.memory_profile {
            print!("{}", memory_profiling_report(mem_profile));
        }
    }
    Ok(result)
}

/// Execute bytecode with the given inputs and execution context
///
/// Panics on execution errors. Use `try_execute_bytecode` for error handling.
pub fn execute_bytecode(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    profiling: bool,
    poseidons_16_precomputed: &Poseidon16History,
) -> ExecutionResult {
    try_execute_bytecode(
        bytecode,
        (public_input, private_input),
        profiling,
        poseidons_16_precomputed,
    )
    .unwrap_or_else(|err| panic!("Error during bytecode execution: {err}"))
}

fn print_line_cycle_counts(history: ExecutionHistory, filepaths: &BTreeMap<FileId, String>) {
    println!("Line by line cycle counts");
    println!("=========================\n");

    let mut gross_cycle_counts: BTreeMap<SourceLocation, usize> = BTreeMap::new();
    for (line, cycle_count) in history.lines.iter().zip(history.lines_cycles.iter()) {
        let prev_count = gross_cycle_counts.get(line).unwrap_or(&0);
        gross_cycle_counts.insert(*line, *prev_count + cycle_count);
    }
    for (location, cycle_count) in gross_cycle_counts.iter() {
        let filepath = filepaths.get(&location.file_id).expect("Unmapped FileId");
        println!("{filepath}:{}: {cycle_count} cycles", location.line_number);
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
    (public_input, private_input): (&[F], &[F]),
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiling: bool,
    poseidons_16_precomputed: &Poseidon16History,
) -> Result<ExecutionResult, (CodeAddress, RunnerError)> {
    // set public memory
    let mut memory = Memory::new(build_public_memory(public_input));

    let public_memory_size = (NONRESERVED_PROGRAM_INPUT_START + public_input.len()).next_power_of_two();
    let mut fp = public_memory_size;

    for (i, value) in private_input.iter().enumerate() {
        memory.set(fp + i, *value).expect("to set private input in memory");
    }

    let mut mem_profile = MemoryProfile {
        used: BTreeSet::new(),
        public_inputs: NONRESERVED_PROGRAM_INPUT_START..NONRESERVED_PROGRAM_INPUT_START + public_memory_size,
        private_inputs: fp..fp + private_input.len(),
        objects: BTreeMap::new(),
    };

    fp += private_input.len();
    fp = fp.next_multiple_of(DIMENSION);

    let initial_ap = fp + bytecode.starting_frame_memory;

    let mut pc = STARTING_PC;
    let mut ap = initial_ap;

    let mut cpu_cycles = 0;

    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;

    let mut pcs = Vec::new();
    let mut fps = Vec::new();

    let mut n_poseidon16_precomputed_used = 0;

    let mut traces = BTreeMap::from_iter((0..N_TABLES).map(|i| (ALL_TABLES[i], TableTrace::new(&ALL_TABLES[i]))));

    let mut add_counts = 0;
    let mut mul_counts = 0;
    let mut deref_counts = 0;
    let mut jump_counts = 0;

    let mut counter_hint = 0;
    let mut cpu_cycles_before_new_line = 0;

    while pc != ENDING_PC {
        if pc >= bytecode.instructions.len() {
            return Err((pc, RunnerError::PCOutOfBounds));
        }

        pcs.push(pc);
        fps.push(fp);

        cpu_cycles += 1;
        cpu_cycles_before_new_line += 1;

        for hint in bytecode.hints.get(&pc).unwrap_or(&vec![]) {
            let mut hint_ctx = HintExecutionContext {
                memory: &mut memory,
                private_input_start: public_memory_size,
                fp,
                ap: &mut ap,
                counter_hint: &mut counter_hint,
                std_out,
                instruction_history,
                cpu_cycles_before_new_line: &mut cpu_cycles_before_new_line,
                cpu_cycles,
                last_checkpoint_cpu_cycles: &mut last_checkpoint_cpu_cycles,
                checkpoint_ap: &mut checkpoint_ap,
                profiling,
                memory_profile: &mut mem_profile,
            };
            hint.execute_hint(&mut hint_ctx).map_err(|e| (pc, e))?;
        }

        let instruction = &bytecode.instructions[pc];
        let mut instruction_ctx = InstructionContext {
            memory: &mut memory,
            fp: &mut fp,
            pc: &mut pc,
            pcs: &pcs,
            traces: &mut traces,
            add_counts: &mut add_counts,
            mul_counts: &mut mul_counts,
            deref_counts: &mut deref_counts,
            jump_counts: &mut jump_counts,
            poseidon16_precomputed: poseidons_16_precomputed,
            n_poseidon16_precomputed_used: &mut n_poseidon16_precomputed_used,
        };
        instruction
            .execute_instruction(&mut instruction_ctx)
            .map_err(|e| (pc, e))?;
    }

    assert_eq!(
        n_poseidon16_precomputed_used,
        poseidons_16_precomputed.len(),
        "Warning: not all precomputed Poseidon16 were used"
    );

    assert_eq!(pc, ENDING_PC);
    pcs.push(pc);
    fps.push(fp);

    let no_vec_runtime_memory = ap - initial_ap;

    let mut summary = String::new();

    if profiling {
        let report = crate::diagnostics::profiling_report(instruction_history, &bytecode.function_locations);
        summary.push_str(&report);
    }

    if !std_out.is_empty() {
        summary.push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
        summary.push_str("║                                STD-OUT                                  ║\n");
        summary.push_str("╚═════════════════════════════════════════════════════════════════════════╝\n");
        summary.push_str(&format!("\n{std_out}"));
        summary.push_str("──────────────────────────────────────────────────────────────────────────\n\n");
    }

    summary.push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
    summary.push_str("║                                 STATS                                   ║\n");
    summary.push_str("╚═════════════════════════════════════════════════════════════════════════╝\n\n");

    summary.push_str(&format!("CYCLES: {}\n", pretty_integer(cpu_cycles)));
    summary.push_str(&format!("MEMORY: {}\n", pretty_integer(memory.0.len())));
    summary.push('\n');

    let runtime_memory_size = memory.0.len() - (NONRESERVED_PROGRAM_INPUT_START + public_input.len());
    summary.push_str(&format!(
        "Bytecode size: {}\n",
        pretty_integer(bytecode.instructions.len())
    ));
    summary.push_str(&format!("Public input size: {}\n", pretty_integer(public_input.len())));
    summary.push_str(&format!(
        "Private input size: {}\n",
        pretty_integer(private_input.len())
    ));
    summary.push_str(&format!("Runtime memory: {}\n", pretty_integer(runtime_memory_size),));
    let used_memory_cells = memory
        .0
        .iter()
        .skip(NONRESERVED_PROGRAM_INPUT_START + public_input.len())
        .filter(|&&x| x.is_some())
        .count();
    summary.push_str(&format!(
        "Memory usage: {:.1}%\n",
        used_memory_cells as f64 / runtime_memory_size as f64 * 100.0
    ));

    // precomputed poseidons
    summary.push_str(&format!(
        "Poseidon2_16 precomputed used: {}/{}\n",
        pretty_integer(n_poseidon16_precomputed_used),
        pretty_integer(poseidons_16_precomputed.len())
    ));

    summary.push('\n');

    if !traces[&Table::poseidon16()].base[0].is_empty() {
        summary.push_str(&format!(
            "Poseidon2_16 calls: {} (1 poseidon per {} instructions)\n",
            pretty_integer(traces[&Table::poseidon16()].base[0].len()),
            cpu_cycles / traces[&Table::poseidon16()].base[0].len()
        ));
    }
    // if !dot_products.is_empty() {
    //     summary.push_str(&format!(
    //         "DotProduct calls: {}\n",
    //         pretty_integer(dot_products.len())
    //     ));
    // }

    if false {
        summary.push_str("Low level instruction counts:\n");
        summary.push_str(&format!(
            "COMPUTE: {} ({} ADD, {} MUL)\n",
            add_counts + mul_counts,
            add_counts,
            mul_counts
        ));
        summary.push_str(&format!("DEREF: {deref_counts}\n"));
        summary.push_str(&format!("JUMP: {jump_counts}\n"));
    }

    summary.push_str("──────────────────────────────────────────────────────────────────────────\n");

    if profiling {
        for (addr, val) in (0..).zip(memory.0.iter()) {
            if val.is_some() {
                mem_profile.used.insert(addr);
            }
        }
    }

    Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
        traces,
        summary,
        memory_profile: if profiling { Some(mem_profile) } else { None },
    })
}

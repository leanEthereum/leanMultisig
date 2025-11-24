//! VM execution runner

use crate::core::{
    DIMENSION, F, NONRESERVED_PROGRAM_INPUT_START, ONE_VEC_PTR, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR,
    VECTOR_LEN, ZERO_VEC_PTR,
};
use crate::diagnostics::{ExecutionResult, MemoryProfile, RunnerError, memory_profiling_report};
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::Bytecode;
use crate::isa::instruction::InstructionContext;
use crate::{
    ALL_TABLES, CodeAddress, ENDING_PC, HintExecutionContext, N_TABLES, STARTING_PC, SourceLineNumber, Table,
    TableTrace,
};
use multilinear_toolkit::prelude::*;
use std::array;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use utils::{poseidon16_permute, poseidon24_permute, pretty_integer};
use xmss::{Poseidon16History, Poseidon24History};

/// Number of instructions to show in stack trace
const STACK_TRACE_INSTRUCTIONS: usize = 5000;

/// Build public memory with standard initialization
pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (NONRESERVED_PROGRAM_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[NONRESERVED_PROGRAM_INPUT_START..][..public_input.len()].copy_from_slice(public_input);

    // "zero" vector
    let zero_start = ZERO_VEC_PTR * VECTOR_LEN;
    for slot in public_memory.iter_mut().skip(zero_start).take(2 * VECTOR_LEN) {
        *slot = F::ZERO;
    }

    // "one" vector
    public_memory[ONE_VEC_PTR * VECTOR_LEN] = F::ONE;
    let one_start = ONE_VEC_PTR * VECTOR_LEN + 1;
    for slot in public_memory.iter_mut().skip(one_start).take(VECTOR_LEN - 1) {
        *slot = F::ZERO;
    }

    public_memory[POSEIDON_16_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_16_NULL_HASH_PTR + 2) * VECTOR_LEN]
        .copy_from_slice(&poseidon16_permute([F::ZERO; 16]));
    public_memory[POSEIDON_24_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_24_NULL_HASH_PTR + 1) * VECTOR_LEN]
        .copy_from_slice(&poseidon24_permute([F::ZERO; 24])[16..]);
    public_memory
}

/// Execute bytecode with the given inputs and execution context
///
/// This is the main VM execution entry point that processes bytecode instructions
/// and generates execution traces with witness data.
pub fn execute_bytecode(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    profiling: bool,
    (poseidons_16_precomputed, poseidons_24_precomputed): (&Poseidon16History, &Poseidon24History),
    merkle_path_hints: VecDeque<Vec<[F; 8]>>,
) -> ExecutionResult {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::new();
    let result = execute_bytecode_helper(
        bytecode,
        (public_input, private_input),
        &mut std_out,
        &mut instruction_history,
        no_vec_runtime_memory,
        profiling,
        (poseidons_16_precomputed, poseidons_24_precomputed),
        merkle_path_hints,
    )
    .unwrap_or_else(|err| {
        let lines_history = &instruction_history.lines;
        let latest_instructions = &lines_history[lines_history.len().saturating_sub(STACK_TRACE_INSTRUCTIONS)..];
        println!(
            "\n{}",
            crate::diagnostics::pretty_stack_trace(
                &bytecode.program,
                latest_instructions,
                &bytecode.function_locations
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
    if profiling {
        print_line_cycle_counts(instruction_history);
        print_instruction_cycle_counts(bytecode, result.pcs.clone());
        if let Some(ref mem_profile) = result.memory_profile {
            print!("{}", memory_profiling_report(mem_profile));
        }
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
    (public_input, private_input): (&[F], &[F]),
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    no_vec_runtime_memory: usize,
    profiling: bool,
    (poseidons_16_precomputed, poseidons_24_precomputed): (&Poseidon16History, &Poseidon24History),
    mut merkle_path_hints: VecDeque<Vec<[F; 8]>>,
) -> Result<ExecutionResult, RunnerError> {
    // set public memory
    let mut memory = Memory::new(build_public_memory(public_input));

    let public_memory_size = (NONRESERVED_PROGRAM_INPUT_START + public_input.len()).next_power_of_two();
    let mut fp = public_memory_size;

    for (i, value) in private_input.iter().enumerate() {
        memory.set(fp + i, *value)?;
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
    let initial_ap_vec = (initial_ap + no_vec_runtime_memory).next_multiple_of(VECTOR_LEN) / VECTOR_LEN;

    let mut pc = STARTING_PC;
    let mut ap = initial_ap;
    let mut ap_vec = initial_ap_vec;

    let mut cpu_cycles = 0;

    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;
    let mut checkpoint_ap_vec = ap_vec;

    let mut pcs = Vec::new();
    let mut fps = Vec::new();

    let mut n_poseidon16_precomputed_used = 0;
    let mut n_poseidon24_precomputed_used = 0;

    // Events collected only in final execution
    let mut traces: [TableTrace; N_TABLES] = array::from_fn(|i| TableTrace::new(&ALL_TABLES[i]));

    let mut add_counts = 0;
    let mut mul_counts = 0;
    let mut deref_counts = 0;
    let mut jump_counts = 0;

    let mut counter_hint = 0;
    let mut cpu_cycles_before_new_line = 0;

    while pc != ENDING_PC {
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
                profiling,
                memory_profile: &mut mem_profile,
            };
            hint.execute_hint(&mut hint_ctx)?;
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
            poseidon24_precomputed: poseidons_24_precomputed,
            merkle_path_hints: &mut merkle_path_hints,
            n_poseidon16_precomputed_used: &mut n_poseidon16_precomputed_used,
            n_poseidon24_precomputed_used: &mut n_poseidon24_precomputed_used,
        };
        instruction.execute_instruction(&mut instruction_ctx)?;
    }

    assert_eq!(
        n_poseidon16_precomputed_used,
        poseidons_16_precomputed.len(),
        "Warning: not all precomputed Poseidon16 were used"
    );
    assert_eq!(
        n_poseidon24_precomputed_used,
        poseidons_24_precomputed.len(),
        "Warning: not all precomputed Poseidon24 were used"
    );
    assert!(
        merkle_path_hints.is_empty(),
        "Warning: not all merkle path hints were used"
    );
    tracing::info!(
        "{}% of Poseidon16 precomputed",
        if poseidons_16_precomputed.is_empty() {
            0.
        } else {
            (n_poseidon16_precomputed_used as f64 / poseidons_16_precomputed.len() as f64) * 100.0
        }
    );
    tracing::info!(
        "{}% of Poseidon24 precomputed",
        if poseidons_24_precomputed.is_empty() {
            0.
        } else {
            (n_poseidon24_precomputed_used as f64 / poseidons_24_precomputed.len() as f64) * 100.0
        }
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
    summary.push_str(&format!(
        "Runtime memory: {} ({:.2}% vec) (no vec mem: {})\n",
        pretty_integer(runtime_memory_size),
        (VECTOR_LEN * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0,
        no_vec_runtime_memory
    ));
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

    summary.push('\n');

    if traces[Table::poseidon16().index()].base[0].len() + traces[Table::poseidon24().index()].base[0].len() > 0 {
        summary.push_str(&format!(
            "Poseidon2_16 calls: {}, Poseidon2_24 calls: {}, (1 poseidon per {} instructions)\n",
            pretty_integer(traces[Table::poseidon16().index()].base[0].len()),
            pretty_integer(traces[Table::poseidon24().index()].base[0].len()),
            cpu_cycles
                / (traces[Table::poseidon16().index()].base[0].len()
                    + traces[Table::poseidon24().index()].base[0].len())
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

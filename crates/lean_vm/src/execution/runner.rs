//! VM execution runner

use crate::core::{
    DIGEST_LEN, DIMENSION, F, FileId, NONRESERVED_PROGRAM_INPUT_START, POSEIDON_16_NULL_HASH_PTR, ZERO_VEC_PTR,
};
use crate::diagnostics::{ExecutionResult, MemoryProfile, RunnerError, memory_profiling_report};
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::Bytecode;
use crate::isa::instruction::InstructionContext;
use crate::{
    ALL_TABLES, CodeAddress, ENDING_PC, EXTENSION_BASIS_PTR, HintExecutionContext, N_TABLES, NUM_REPEATED_ONES_IN_RESERVED_MEMORY, REPEATED_ONES_PTR, SAMPLING_DOMAIN_SEPARATOR_PTR, STARTING_PC, SourceLocation, Table, TableTrace
};
use multilinear_toolkit::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use utils::{ToUsize, get_poseidon_16_of_zero, pretty_integer};
use xmss::Poseidon16History;

/// Build public memory with standard initialization
pub fn build_public_memory(non_reserved_public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (NONRESERVED_PROGRAM_INPUT_START + non_reserved_public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[NONRESERVED_PROGRAM_INPUT_START..][..non_reserved_public_input.len()]
        .copy_from_slice(non_reserved_public_input);

    // "zero" vector
    let zero_start = ZERO_VEC_PTR;
    for slot in public_memory.iter_mut().skip(zero_start).take(2 * DIGEST_LEN) {
        *slot = F::ZERO;
    }

    // sampling domain separator
    public_memory[SAMPLING_DOMAIN_SEPARATOR_PTR] = F::ONE;

    // extension basis
    for i in 0..DIMENSION {
        let mut vec = F::zero_vec(DIMENSION);
        vec[i] = F::ONE;
        public_memory[EXTENSION_BASIS_PTR + i * DIMENSION..][..DIMENSION].copy_from_slice(&vec);
    }

    public_memory[POSEIDON_16_NULL_HASH_PTR..][..DIGEST_LEN].copy_from_slice(get_poseidon_16_of_zero());
    public_memory[REPEATED_ONES_PTR..][..NUM_REPEATED_ONES_IN_RESERVED_MEMORY].fill(F::ONE);
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
        eprintln!(
            "\n{}",
            crate::diagnostics::pretty_stack_trace(bytecode, last_pc, &instruction_history.lines)
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

/// Resolve pending deref hints in correct order
///
/// Each constraint has form: memory[target_addr] = memory[memory[src_addr]]
/// Order matters because some src addresses might point to targets of other hints.
/// We iteratively resolve constraints until no more progress, then fill remaining with 0.
fn resolve_deref_hints(memory: &mut Memory, pending: &[(usize, usize)]) {
    let mut resolved: BTreeSet<usize> = BTreeSet::new();

    loop {
        let mut made_progress = false;

        for &(target_addr, src_addr) in pending {
            if resolved.contains(&target_addr) {
                continue;
            }
            let Some(addr) = memory.0.get(src_addr).copied().flatten() else {
                continue;
            };
            let Some(value) = memory.0.get(addr.to_usize()).copied().flatten() else {
                continue;
            };
            memory.set(target_addr, value).unwrap();
            resolved.insert(target_addr);
            made_progress = true;
        }

        if !made_progress {
            break;
        }
    }

    // Fill any remaining unresolved targets with 0
    for &(target_addr, _src_addr) in pending {
        if !resolved.contains(&target_addr) {
            let _ = memory.set(target_addr, F::ZERO);
        }
    }
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

    // Pending deref hints: (target_addr, src_addr) constraints to resolve at end
    let mut pending_deref_hints: Vec<(usize, usize)> = Vec::new();

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
                private_input_start: public_memory_size,
                pending_deref_hints: &mut pending_deref_hints,
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

    // Resolve pending deref hints in correct order
    // Constraint: memory[target_addr] = memory[memory[src_addr]]
    // Order matters because some src addresses might point to targets of other hints
    resolve_deref_hints(&mut memory, &pending_deref_hints);

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

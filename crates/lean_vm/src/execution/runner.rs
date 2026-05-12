//! VM execution runner

use crate::core::{DIMENSION, F};
use crate::diagnostics::{ExecutionMetadata, ExecutionResult, RunnerError};
use crate::execution::memory::MemoryAccess;
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::Bytecode;
use crate::isa::hint::{DiagnosticState, Hint, HintState, NamedHintCursor};
use crate::isa::instruction::{InstructionContext, InstructionCounts};
use crate::{
    ALL_TABLES, CodeAddress, ENDING_PC, HintExecutionContext, MemOrConstant, N_TABLES, STARTING_PC, Table, TableTrace,
};
use backend::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use utils::{ToUsize, padd_with_zero_to_next_power_of_two};

use super::memory::SegmentMemory;

#[derive(Debug, Default)]
pub struct ExecutionWitness {
    /// Length of the program's "preamble memory" — a region between public
    /// memory and runtime memory that the runner leaves unset, that is filled
    /// manually by the program at startup.
    pub preamble_memory_len: usize,
    pub hints: HashMap<String, Vec<Vec<F>>>,
}

pub fn try_execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    profiling: bool,
) -> Result<ExecutionResult, RunnerError> {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::new();
    execute_bytecode_helper(
        bytecode,
        public_input,
        witness,
        &mut std_out,
        &mut instruction_history,
        profiling,
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
    })
}

pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    profiling: bool,
) -> ExecutionResult {
    try_execute_bytecode(bytecode, public_input, witness, profiling)
        .unwrap_or_else(|err| panic!("Error during bytecode execution: {err}"))
}

struct Trace {
    pcs: Vec<usize>,
    fps: Vec<usize>,
    tables: BTreeMap<Table, TableTrace>,
    counts: InstructionCounts,
    pending_deref_hints: Vec<(usize, usize)>, // (target_addr, src_addr) constraints to resolve at end
}

impl Trace {
    fn new() -> Self {
        Self {
            pcs: Vec::new(),
            fps: Vec::new(),
            tables: BTreeMap::from_iter((0..N_TABLES).map(|i| (ALL_TABLES[i], TableTrace::new(&ALL_TABLES[i])))),
            counts: InstructionCounts::default(),
            pending_deref_hints: Vec::new(),
        }
    }

    fn merge(&mut self, other: Self) {
        self.pcs.extend(other.pcs);
        self.fps.extend(other.fps);
        self.counts += other.counts;
        self.pending_deref_hints.extend(other.pending_deref_hints);
        for (table, other_t) in other.tables {
            let mine = self.tables.get_mut(&table).unwrap();
            for (col, new_data) in mine.columns.iter_mut().zip(other_t.columns) {
                col.extend(new_data);
            }
        }
    }
}

enum LoopExit {
    Halted,
    LoopBack,
    ParallelBatch(ParallelBatchInfo),
}

struct ParallelBatchInfo {
    batch_pc: usize,
    batch_fp: usize,
    frame_size: usize,
    n_args: usize,
    end_value: MemOrConstant,
    /// Per-name cursor indices at the moment iteration 0 started consuming
    /// hints. Diffed against the post-iteration-0 state to learn per-name
    /// consumption.
    hint_indices_at_start: HashMap<String, usize>,
}

#[allow(clippy::too_many_arguments)]
fn run_loop<M: MemoryAccess>(
    bytecode: &Bytecode,
    memory: &mut M,
    trace: &mut Trace,
    pc: &mut usize,
    fp: &mut usize,
    ap: &mut usize,
    hints: &mut HintState<'_, '_>,
    stop_pc: Option<usize>,
) -> Result<LoopExit, RunnerError> {
    let mut parallel_batch: Option<ParallelBatchInfo> = None;

    loop {
        if *pc == ENDING_PC {
            return Ok(LoopExit::Halted);
        }
        if *pc >= bytecode.code.len() {
            return Err(RunnerError::PCOutOfBounds);
        }
        trace.pcs.push(*pc);
        trace.fps.push(*fp);
        if let Some(diag) = &mut hints.diagnostics {
            *diag.cpu_cycles_before_new_line += 1;
        }

        let entry = &bytecode.code[*pc];

        for hint in entry.hints.iter() {
            if let Hint::ParallelBatchStart { n_args, end_value } = hint {
                if parallel_batch.is_none() {
                    parallel_batch = Some(ParallelBatchInfo {
                        batch_pc: *pc,
                        batch_fp: *fp,
                        frame_size: *ap - *fp,
                        n_args: *n_args,
                        end_value: *end_value,
                        hint_indices_at_start: hints
                            .named_hints
                            .iter()
                            .map(|(name, cursor)| (name.clone(), cursor.index))
                            .collect(),
                    });
                }
                continue;
            }
            let mut ctx = HintExecutionContext {
                hints,
                memory,
                fp: *fp,
                ap,
                cpu_cycles: trace.pcs.len(),
                pending_deref_hints: &mut trace.pending_deref_hints,
            };
            hint.execute_hint(&mut ctx)?;
        }

        let instruction = &entry.instruction;
        let mut ctx = InstructionContext {
            memory,
            fp,
            pc,
            pcs: &trace.pcs,
            traces: &mut trace.tables,
            counts: &mut trace.counts,
        };
        instruction.execute_instruction(&mut ctx)?;

        if stop_pc == Some(*pc) {
            // we are at the end of a parallel batch segment
            return Ok(LoopExit::LoopBack);
        }

        // Parallel batch ready: we have run the first iteration, so we know the memory usage and
        // can spawn parallel execution for the remaining iterations.
        if let Some(ref batch) = parallel_batch
            && *pc == batch.batch_pc
        {
            return Ok(LoopExit::ParallelBatch(parallel_batch.take().unwrap()));
        }
    }
}

/// Resolve pending deref hints in correct order
///
/// Each constraint has form: memory[target_addr] = memory[memory[src_addr]]
/// Order matters because some src addresses might point to targets of other hints.
/// We iteratively resolve constraints until no more progress, then fill remaining with 0.
/// Assumption: every memory[src_addr] is defined (i.e. is Some(_)) (which is true when DEREFs come from range checks)
fn resolve_deref_hints(memory: &mut Memory, pending: &[(usize, usize)]) {
    let mut resolved: BTreeSet<usize> = BTreeSet::new();
    loop {
        let mut made_progress = false;
        for &(target_addr, src_addr) in pending {
            if resolved.contains(&target_addr) {
                continue;
            }
            let addr = memory.0[src_addr].unwrap();
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
    // Fill any remaining unresolved targets with 0 (this can happen in case of cycles)
    for &(target_addr, _src_addr) in pending {
        if !resolved.contains(&target_addr) {
            memory.set(target_addr, F::ZERO).unwrap();
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiling: bool,
) -> Result<ExecutionResult, (CodeAddress, RunnerError)> {
    let mut named_hints: HashMap<String, NamedHintCursor<'_>> = witness
        .hints
        .iter()
        .map(|(name, entries)| (name.clone(), NamedHintCursor::new(entries)))
        .collect();
    let public_memory = padd_with_zero_to_next_power_of_two(public_input);
    let public_memory_size = public_memory.len();
    let mut memory = Memory::new(public_memory);
    let mut fp = public_memory_size + witness.preamble_memory_len;
    fp = fp.next_multiple_of(DIMENSION);
    let initial_ap = fp + bytecode.starting_frame_memory;
    let mut pc = STARTING_PC;
    let mut ap = initial_ap;
    let mut trace = Trace::new();
    let mut cpu_cycles_before_new_line = 0;
    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;

    loop {
        let mut hints = HintState {
            diagnostics: Some(DiagnosticState {
                std_out,
                instruction_history,
                cpu_cycles_before_new_line: &mut cpu_cycles_before_new_line,
                last_checkpoint_cpu_cycles: &mut last_checkpoint_cpu_cycles,
                checkpoint_ap: &mut checkpoint_ap,
            }),
            named_hints: &mut named_hints,
        };
        match run_loop(
            bytecode,
            &mut memory,
            &mut trace,
            &mut pc,
            &mut fp,
            &mut ap,
            &mut hints,
            None,
        )
        .map_err(|e| (pc, e))?
        {
            LoopExit::Halted => break,
            LoopExit::ParallelBatch(batch) => {
                handle_parallel_batch(
                    bytecode,
                    &mut memory,
                    &mut trace,
                    &mut named_hints,
                    &mut pc,
                    &mut fp,
                    &mut ap,
                    &batch,
                )
                .map_err(|e| (pc, e))?;
            }
            LoopExit::LoopBack => unreachable!("main loop has no stop_pc"),
        }
    }

    resolve_deref_hints(&mut memory, &trace.pending_deref_hints);
    assert_eq!(pc, ENDING_PC);
    for (name, cursor) in &named_hints {
        assert_eq!(
            cursor.index,
            cursor.entries.len(),
            "Not all entries of named hint '{name}' were consumed ({} of {} used)",
            cursor.index,
            cursor.entries.len(),
        );
    }
    trace.pcs.push(pc);
    trace.fps.push(fp);

    let no_vec_runtime_memory = ap - initial_ap;
    let profiling_report = if profiling {
        Some(crate::diagnostics::profiling_report(
            instruction_history,
            &bytecode.function_locations,
        ))
    } else {
        None
    };
    let runtime_memory_size = memory.0.len() - public_memory_size - witness.preamble_memory_len;
    let used_memory_cells = memory.0.par_iter().filter(|&&x| x.is_some()).count();
    let metadata = ExecutionMetadata {
        cycles: trace.pcs.len(),
        memory: memory.0.len(),
        n_poseidons: trace.tables[&Table::poseidon16()].columns[0].len(),
        n_extension_ops: trace.tables[&Table::extension_op()].columns[0].len(),
        bytecode_size: bytecode.code.len(),
        public_input_size: public_input.len(),
        runtime_memory: runtime_memory_size,
        memory_usage_percent: used_memory_cells as f64 / memory.0.len() as f64 * 100.0,
        stdout: std::mem::take(std_out),
        profiling_report,
    };
    Ok(ExecutionResult {
        runtime_memory_size: no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs: trace.pcs,
        fps: trace.fps,
        traces: trace.tables,
        metadata,
    })
}

fn write_call_frame(
    memory: &mut Memory,
    fp: usize,
    return_pc: usize,
    saved_fp: usize,
    iterator_val: usize,
    args: &[F],
) -> Result<(), RunnerError> {
    memory.set(fp, F::from_usize(return_pc))?;
    memory.set(fp + 1, F::from_usize(saved_fp))?;
    memory.set(fp + 2, F::from_usize(iterator_val))?;
    for (j, &v) in args.iter().enumerate().skip(1) {
        memory.set(fp + 2 + j, v)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn handle_parallel_batch(
    bytecode: &Bytecode,
    memory: &mut Memory,
    trace: &mut Trace,
    named_hints: &mut HashMap<String, NamedHintCursor<'_>>,
    pc: &mut usize,
    fp: &mut usize,
    ap: &mut usize,
    batch: &ParallelBatchInfo,
) -> Result<(), RunnerError> {
    let start_value = memory.get(batch.batch_fp + 2)?.to_usize();
    let end_value = batch.end_value.read_value(memory, batch.batch_fp)?.to_usize();
    let n_iters = end_value - start_value;

    if n_iters == 1 {
        return Ok(());
    }

    let stride = *fp - batch.batch_fp;
    let return_pc = memory.get(*fp)?.to_usize();
    let args: Vec<F> = (0..batch.n_args)
        .map(|i| memory.get(batch.batch_fp + 2 + i).unwrap())
        .collect();

    // Per-name deltas for named hints (measured from iteration 0).
    let named_per_iter: HashMap<String, usize> = named_hints
        .iter()
        .map(|(name, cursor)| (name.clone(), cursor.index - batch.hint_indices_at_start[name]))
        .collect();

    for i in 1..=n_iters {
        let iter_val = if i < n_iters { start_value + i } else { end_value };
        write_call_frame(
            memory,
            batch.batch_fp + i * stride,
            return_pc,
            batch.batch_fp + (i - 1) * stride,
            iter_val,
            &args,
        )?;
    }

    let max_addr = batch.batch_fp + (n_iters + 1) * stride;
    if max_addr > memory.0.len() {
        memory.0.resize(max_addr, None);
    }

    let n_par = n_iters - 1;

    // Split memory into a shared read-only region and per-segment mutable slices.
    // Iteration 0 has already been executed and wrote into [batch_fp, batch_fp + stride).
    // Iterations 1..n_par each get their own [batch_fp + (i+1)*stride, batch_fp + (i+2)*stride).
    let split_at = batch.batch_fp + stride; // end of iteration 0's frame
    let (left, right) = memory.0.split_at_mut(split_at);
    let shared: &[Option<F>] = &*left;
    let segment_slices: Vec<&mut [Option<F>]> = right.chunks_mut(stride).take(n_par).collect();

    type SegResult = Result<(Trace, Vec<(usize, F)>), RunnerError>;
    let results: Vec<SegResult> = segment_slices
        .into_par_iter()
        .enumerate()
        .map(|(i, seg_slice)| {
            let seg_start = split_at + i * stride;
            let mut seg_mem = SegmentMemory::new(shared, seg_slice, seg_start);
            let fp_i = batch.batch_fp + (i + 1) * stride;
            let mut seg_trace = Trace::new();
            let mut seg_pc = batch.batch_pc;
            let mut seg_fp = fp_i;
            let mut seg_ap = fp_i + batch.frame_size;
            let mut seg_named_hints = named_hints.clone();
            for (name, delta) in &named_per_iter {
                if let Some(cursor) = seg_named_hints.get_mut(name) {
                    cursor.index += i * delta;
                }
            }
            let mut hints = HintState {
                diagnostics: None,
                named_hints: &mut seg_named_hints,
            };
            run_loop(
                bytecode,
                &mut seg_mem,
                &mut seg_trace,
                &mut seg_pc,
                &mut seg_fp,
                &mut seg_ap,
                &mut hints,
                Some(batch.batch_pc),
            )?;
            let deferred = seg_mem.into_deferred_writes();
            Ok((seg_trace, deferred))
        })
        .collect();

    for (idx, result) in results.into_iter().enumerate() {
        let (seg_trace, deferred) = result.map_err(|e| RunnerError::ParallelSegmentFailed(idx + 1, Box::new(e)))?;
        trace.merge(seg_trace);
        for (addr, val) in deferred {
            memory.set(addr, val)?;
        }
    }

    for (name, delta) in &named_per_iter {
        if let Some(cursor) = named_hints.get_mut(name) {
            cursor.index += n_par * delta;
        }
    }

    *pc = batch.batch_pc;
    *fp = batch.batch_fp + n_iters * stride;
    *ap = *fp + batch.frame_size;
    Ok(())
}

use crate::core::{F, Label, SourceLocation};
use crate::diagnostics::RunnerError;
use crate::execution::ExecutionHistory;
use crate::execution::memory::MemoryAccess;
use crate::isa::operands::{MemOrConstant, MemOrFpOrConstant};
use backend::*;
use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use utils::{ToUsize, to_big_endian_in_field, to_little_endian_in_field};

/// VM hints provide execution guidance and debugging information, but does not appear
/// in the verified bytecode.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum Hint {
    /// Compute the inverse of a field element
    Inverse {
        /// The value to invert (return 0 if arg is zero)
        arg: MemOrConstant,
        /// Memory offset where result will be stored: m[fp + res_offset]
        res_offset: usize,
    },
    /// Request memory allocation
    RequestMemory {
        /// Memory offset where hint will be stored: m[fp + offset]
        offset: usize,
        /// The requested memory size
        size: MemOrConstant,
    },
    /// Print debug information during execution
    Print {
        /// Source code location information
        line_info: String,
        /// Values to print
        content: Vec<MemOrConstant>,
    },
    /// Report source code location for debugging
    LocationReport {
        /// Source code location
        location: SourceLocation,
    },
    /// Jump destination label (for debugging purposes)
    Label {
        label: Label,
    },
    /// Assert a boolean expression for debugging purposes
    DebugAssert(BooleanExpr<MemOrConstant>, SourceLocation),
    Custom(CustomHint, Vec<MemOrFpOrConstant>),
    /// Deref hint for range checks - records a constraint to be resolved at end of execution
    /// Constraint: memory[fp + offset_target] = memory[memory[fp + offset_src]]
    /// The runner resolves all these constraints at the end, in the correct order.
    DerefHint {
        offset_src: usize,
        offset_target: usize,
    },
    /// Panic hint with optional error message (for debugging)
    Panic {
        message: Option<String>,
    },
    /// Marks the start of a parallelizable loop body.
    /// Placed at the entry of the loop's recursive function, before the condition check.
    /// The runner executes the first iteration to learn the per-iteration allocation,
    /// then executes remaining iterations in parallel.
    ParallelBatchStart {
        /// Total number of function args (iterator + external vars).
        /// Frame layout: [return_pc, saved_fp, arg0=iterator, arg1, ..., argN-1, locals...]
        n_args: usize,
        /// End value of the loop: either `m[fp + offset]` (runtime) or a constant.
        end_value: MemOrConstant,
    },
    /// fetch the next `Vec<F>` entry from `named_hints[name]`.
    ///
    /// When `size` is `None`, the data is dynamically written at the allocation pointer `ap`
    /// and a pointer to it is stored at `m[fp + offset]`.
    ///
    /// When `size` is `Some(n)`, the data is copied directly into `m[fp + offset .. fp + offset + n]`
    HintRead {
        name: String,
        offset: usize,
        size: Option<usize>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum CustomHint {
    // Decompose values into their custom representations:
    /// each field element x is decomposed to: (a0, a1, a2, ..., a11, b) where:
    /// x = a0 + a1.4 + a2.4^2 + a3.4^3 + ... + a11.4^11 + b.2^24
    /// and ai < 4, b < 2^7 - 1
    /// The decomposition is unique, and always exists (except for x = -1)
    DecomposeBitsXMSS,
    DecomposeBitsMerkleWhir,
    DecomposeBits,
    LessThan,
    Log2Ceil,
}

pub const CUSTOM_HINTS: [CustomHint; 5] = [
    CustomHint::DecomposeBitsXMSS,
    CustomHint::DecomposeBitsMerkleWhir,
    CustomHint::DecomposeBits,
    CustomHint::LessThan,
    CustomHint::Log2Ceil,
];

impl CustomHint {
    pub fn name(&self) -> &str {
        match self {
            Self::DecomposeBitsXMSS => "hint_decompose_bits_xmss",
            Self::DecomposeBitsMerkleWhir => "hint_decompose_bits_merkle_whir",
            Self::DecomposeBits => "hint_decompose_bits",
            Self::LessThan => "hint_less_than",
            Self::Log2Ceil => "hint_log2_ceil",
        }
    }

    pub fn n_args(&self) -> usize {
        match self {
            Self::DecomposeBitsXMSS => 5,
            Self::DecomposeBitsMerkleWhir => 4,
            Self::DecomposeBits => 4,
            Self::LessThan => 3,
            Self::Log2Ceil => 2,
        }
    }

    pub fn execute<M: MemoryAccess>(
        &self,
        args: &[MemOrFpOrConstant],
        ctx: &mut HintExecutionContext<'_, '_, '_, M>,
    ) -> Result<(), RunnerError> {
        match self {
            Self::DecomposeBitsXMSS => {
                // Aborting hypercube decomposition: a_i = Q * d_i + r_i
                // where d_i = floor(a_i / Q), r_i = a_i mod Q, Q = 127
                // Then d_i is decomposed into base-w digits (w = 2^chunk_size)
                let decomposed_ptr = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let remaining_ptr = args[1].read_value(ctx.memory, ctx.fp)?.to_usize();
                let to_decompose_ptr = args[2].read_value(ctx.memory, ctx.fp)?.to_usize();
                let num_to_decompose = args[3].read_value(ctx.memory, ctx.fp)?.to_usize();
                let chunk_size = args[4].read_value(ctx.memory, ctx.fp)?.to_usize();
                assert!(24_usize.is_multiple_of(chunk_size));
                let q: usize = 127; // Q parameter for aborting hypercube (p = Q * w^z + 1)
                let base = 1 << chunk_size;
                let n_chunks = 24 / chunk_size;
                let mut memory_index_decomposed = decomposed_ptr;
                let mut memory_index_remaining = remaining_ptr;
                #[allow(clippy::explicit_counter_loop)]
                for i in 0..num_to_decompose {
                    let value = ctx.memory.get(to_decompose_ptr + i)?.to_usize();
                    let mut d_i = value / q; // floor(a_i / Q)
                    let r_i = value % q; // a_i mod Q
                    for _ in 0..n_chunks {
                        ctx.memory.set(memory_index_decomposed, F::from_usize(d_i % base))?;
                        d_i /= base;
                        memory_index_decomposed += 1;
                    }
                    assert_eq!(
                        d_i, 0,
                        "d_i does not fit in {n_chunks} base-{base} digits -> invalid XMSS encoding"
                    );
                    ctx.memory.set(memory_index_remaining, F::from_usize(r_i))?;
                    memory_index_remaining += 1;
                }
            }
            Self::DecomposeBitsMerkleWhir => {
                let decomposed_ptr = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let value = args[2].read_value(ctx.memory, ctx.fp)?.to_usize();
                let chunk_size = args[3].read_value(ctx.memory, ctx.fp)?.to_usize();
                assert!(24_usize.is_multiple_of(chunk_size));
                let mut memory_index_decomposed = decomposed_ptr;
                #[allow(clippy::explicit_counter_loop)]
                for i in 0..24 / chunk_size {
                    let value = F::from_usize((value >> (chunk_size * i)) & ((1 << chunk_size) - 1));
                    ctx.memory.set(memory_index_decomposed, value)?;
                    memory_index_decomposed += 1;
                }
                ctx.memory
                    .set(args[1].memory_address(ctx.fp)?, F::from_usize(value >> 24))?;
            }
            Self::DecomposeBits => {
                let to_decompose = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let memory_index = args[1].read_value(ctx.memory, ctx.fp)?.to_usize();
                let num_bits = args[2].read_value(ctx.memory, ctx.fp)?.to_usize();
                let endianness = args[3].read_value(ctx.memory, ctx.fp)?.to_usize();
                assert!(
                    endianness == 0 || endianness == 1,
                    "Invalid endianness for DecomposeBits hint"
                );
                assert!(num_bits <= F::bits());
                if endianness == 0 {
                    // Big-endian
                    ctx.memory
                        .set_slice(memory_index, &to_big_endian_in_field::<F>(to_decompose, num_bits))?
                } else {
                    // Little-endian
                    ctx.memory
                        .set_slice(memory_index, &to_little_endian_in_field::<F>(to_decompose, num_bits))?
                }
            }
            Self::LessThan => {
                let a = args[0].read_value(ctx.memory, ctx.fp)?;
                let b = args[1].read_value(ctx.memory, ctx.fp)?;
                let res_ptr = args[2].memory_address(ctx.fp)?;
                let result = if a.to_usize() < b.to_usize() { F::ONE } else { F::ZERO };
                ctx.memory.set(res_ptr, result)?;
            }
            Self::Log2Ceil => {
                let n = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let res_ptr = args[1].memory_address(ctx.fp)?;
                ctx.memory.set(res_ptr, F::from_usize(log2_ceil_usize(n)))?;
            }
        }
        Ok(())
    }

    pub fn find_by_name(name: &str) -> Option<Self> {
        CUSTOM_HINTS.iter().find(|hint| hint.name() == name).copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum Boolean {
    Equal,
    Different,
    LessThan,
    LessOrEqual,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub struct BooleanExpr<E> {
    pub left: E,
    pub right: E,
    pub kind: Boolean,
}

#[derive(Debug)]
pub struct DiagnosticState<'a> {
    pub std_out: &'a mut String,
    pub instruction_history: &'a mut ExecutionHistory,
    pub cpu_cycles_before_new_line: &'a mut usize,
    pub last_checkpoint_cpu_cycles: &'a mut usize,
    pub checkpoint_ap: &'a mut usize,
}

#[derive(Debug, Clone, Copy)]
pub struct NamedHintCursor<'a> {
    pub entries: &'a [Vec<F>],
    pub index: usize,
}

impl<'a> NamedHintCursor<'a> {
    pub fn new(entries: &'a [Vec<F>]) -> Self {
        Self { entries, index: 0 }
    }
}

#[derive(Debug)]
pub struct HintState<'a, 'h> {
    pub diagnostics: Option<DiagnosticState<'a>>,
    pub named_hints: &'a mut HashMap<String, NamedHintCursor<'h>>,
}

#[derive(Debug)]
pub struct HintExecutionContext<'a, 'h, 'hh, M: MemoryAccess> {
    pub hints: &'a mut HintState<'h, 'hh>,
    pub memory: &'a mut M,
    pub fp: usize,
    pub ap: &'a mut usize,
    pub cpu_cycles: usize,
    pub pending_deref_hints: &'a mut Vec<(usize, usize)>,
}

impl Hint {
    /// Execute this hint within the given execution context
    #[inline(always)]
    pub fn execute_hint<M: MemoryAccess>(
        &self,
        ctx: &mut HintExecutionContext<'_, '_, '_, M>,
    ) -> Result<(), RunnerError> {
        match self {
            Self::RequestMemory { offset, size } => {
                let size = size.read_value(ctx.memory, ctx.fp)?.to_usize();

                let allocation_start_addr = *ctx.ap;
                ctx.memory.set(ctx.fp + *offset, F::from_usize(allocation_start_addr))?;
                *ctx.ap += size;
            }
            Self::Custom(hint, args) => {
                hint.execute(args, ctx)?;
            }
            Self::Inverse { arg, res_offset } => {
                let value = arg.read_value(ctx.memory, ctx.fp)?;
                let result = value.try_inverse().unwrap_or(F::ZERO);
                ctx.memory.set(ctx.fp + *res_offset, result)?;
            }
            Self::Print { line_info, content } => {
                if let Some(diag) = &mut ctx.hints.diagnostics {
                    let values = content
                        .iter()
                        .map(|value| Ok(value.read_value(ctx.memory, ctx.fp)?.to_string()))
                        .collect::<Result<Vec<_>, _>>()?;
                    if values[0] == "123456789" {
                        if values.len() == 1 {
                            *diag.std_out += "[CHECKPOINT]\n";
                        } else {
                            assert_eq!(values.len(), 2);
                            let new_no_vec_memory = *ctx.ap - *diag.checkpoint_ap;
                            *diag.std_out += &format!(
                                "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {}\n",
                                values[1],
                                pretty_integer(ctx.cpu_cycles - *diag.last_checkpoint_cpu_cycles),
                                pretty_integer(new_no_vec_memory),
                            );
                        }
                        *diag.last_checkpoint_cpu_cycles = ctx.cpu_cycles;
                        *diag.checkpoint_ap = *ctx.ap;
                    }
                    let line_info = line_info.replace(';', "");
                    *diag.std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
                }
            }
            Self::LocationReport { location } => {
                if let Some(diag) = &mut ctx.hints.diagnostics {
                    diag.instruction_history.lines.push(*location);
                    diag.instruction_history
                        .lines_cycles
                        .push(*diag.cpu_cycles_before_new_line);
                    *diag.cpu_cycles_before_new_line = 0;
                }
            }
            Self::Label { .. } => {}
            Self::DebugAssert(bool_expr, location) => {
                let left = bool_expr.left.read_value(ctx.memory, ctx.fp)?;
                let right = bool_expr.right.read_value(ctx.memory, ctx.fp)?;
                let condition_holds = match bool_expr.kind {
                    Boolean::Equal => left == right,
                    Boolean::Different => left != right,
                    Boolean::LessThan => left < right,
                    Boolean::LessOrEqual => left <= right,
                };
                if !condition_holds {
                    return Err(RunnerError::DebugAssertFailed(
                        format!("{} {} {}", left, bool_expr.kind, right),
                        *location,
                    ));
                }
            }
            Self::DerefHint {
                offset_src,
                offset_target,
            } => {
                // Record a deref constraint: memory[target_addr] = memory[memory[src_addr]]
                let src_addr = ctx.fp + offset_src;
                let target_addr = ctx.fp + offset_target;
                ctx.pending_deref_hints.push((target_addr, src_addr));
            }
            Self::Panic { message } => {
                if let Some(msg) = message
                    && let Some(diag) = &mut ctx.hints.diagnostics
                {
                    *diag.std_out += &format!("[PANIC] {}\n", msg);
                }
            }
            // Handled by the runner's parallel dispatch; no-op in sequential mode.
            Self::ParallelBatchStart { .. } => {}
            Self::HintRead { name, offset, size } => {
                let cursor = ctx.hints.named_hints.get_mut(name).unwrap_or_else(|| {
                    panic!("hint_read: no hint named '{name}'");
                });
                assert!(
                    cursor.index < cursor.entries.len(),
                    "hint_read: exhausted entries for '{name}' (index={}, len={})",
                    cursor.index,
                    cursor.entries.len()
                );
                let data = &cursor.entries[cursor.index];
                cursor.index += 1;
                match size {
                    None => {
                        let allocation_start_addr = *ctx.ap;
                        ctx.memory.set_slice(allocation_start_addr, data)?;
                        *ctx.ap += data.len();
                        ctx.memory.set(ctx.fp + *offset, F::from_usize(allocation_start_addr))?;
                    }
                    Some(expected_size) => {
                        assert_eq!(
                            data.len(),
                            *expected_size,
                            "hint_read: size mismatch for '{name}' (expected={expected_size}, got={})",
                            data.len()
                        );
                        ctx.memory.set_slice(ctx.fp + *offset, data)?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl Display for Hint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RequestMemory { offset, size } => {
                write!(f, "m[fp + {offset}] = request_memory({size})")
            }
            Self::Custom(hint, args) => {
                let args_str = args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>().join(", ");
                write!(f, "{}({args_str})", hint.name())
            }
            Self::Print { line_info, content } => {
                write!(f, "print(")?;
                for (i, v) in content.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ") for \"{line_info}\"")
            }
            Self::Inverse { arg, res_offset } => {
                write!(f, "m[fp + {res_offset}] = inverse({arg})")
            }
            Self::LocationReport {
                location: SourceLocation { file_id, line_number },
            } => {
                // TODO: make a pretty-print method which shows the filepath instead of file_id
                write!(f, "source location: {file_id}:{line_number}")
            }
            Self::Label { label } => {
                write!(f, "label: {label}")
            }
            Self::DebugAssert(bool_expr, location) => {
                write!(f, "debug_assert {bool_expr} at {location:?}")
            }
            Self::DerefHint {
                offset_src,
                offset_target,
            } => {
                write!(f, "m[fp + {offset_target}] = m[m[fp + {offset_src}]]")
            }
            Self::Panic { message } => match message {
                Some(msg) => write!(f, "panic: \"{msg}\""),
                None => write!(f, "panic"),
            },
            Self::ParallelBatchStart { n_args, end_value } => {
                write!(f, "parallel_batch_start(n_args={n_args}, end={end_value})")
            }
            Self::HintRead {
                name,
                offset,
                size: None,
            } => {
                write!(f, "m[fp + {offset}] = hint_read(\"{name}\")")
            }
            Self::HintRead {
                name,
                offset,
                size: Some(size),
            } => {
                write!(f, "m[fp + {offset} .. +{size}] = hint_read(\"{name}\", {size})")
            }
        }
    }
}

impl<E: Display> Display for BooleanExpr<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.left, self.kind, self.right)
    }
}

impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equal => write!(f, "=="),
            Self::Different => write!(f, "!="),
            Self::LessThan => write!(f, "<"),
            Self::LessOrEqual => write!(f, "<="),
        }
    }
}

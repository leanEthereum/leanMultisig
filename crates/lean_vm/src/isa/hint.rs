use crate::core::{F, Label, SourceLocation};
use crate::diagnostics::{MemoryObject, MemoryObjectType, MemoryProfile, RunnerError};
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::operands::MemOrConstant;
use backend::*;
use std::fmt::Debug;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use utils::{ToUsize, pretty_integer, to_big_endian_in_field, to_little_endian_in_field};
use xmss::SIG_SIZE_FE;

/// VM hints provide execution guidance and debugging information, but does not appear
/// in the verified bytecode.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
        /// Function name this allocation is associated with (for profiling)
        function_name: Label,
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
    /// Stack frame size (for memory profiling)
    StackFrame {
        label: Label,
        size: usize,
    },
    /// Assert a boolean expression for debugging purposes
    DebugAssert(BooleanExpr<MemOrConstant>, SourceLocation),
    Custom(CustomHint, Vec<MemOrConstant>),
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CustomHint {
    // Decompose values into their custom representations:
    /// each field element x is decomposed to: (a0, a1, a2, ..., a11, b) where:
    /// x = a0 + a1.4 + a2.4^2 + a3.4^3 + ... + a11.4^11 + b.2^24
    /// and ai < 4, b < 2^7 - 1
    /// The decomposition is unique, and always exists (except for x = -1)
    DecomposeBitsXMSS,
    DecomposeBits,
    /// Decompose a field element into lo (< 2^16) and hi (< 2^14) parts:
    /// a = lo + hi * 2^16
    /// Args: value, lo_ptr, hi_ptr
    Decompose16,
    LessThan,
    Log2Ceil,
    PrivateInputStart,
    Xmss,
    Merkle,
}

pub const CUSTOM_HINTS: [CustomHint; 8] = [
    CustomHint::DecomposeBitsXMSS,
    CustomHint::DecomposeBits,
    CustomHint::Decompose16,
    CustomHint::LessThan,
    CustomHint::Log2Ceil,
    CustomHint::PrivateInputStart,
    CustomHint::Xmss,
    CustomHint::Merkle,
];

impl CustomHint {
    pub fn name(&self) -> &str {
        match self {
            Self::DecomposeBitsXMSS => "hint_decompose_bits_xmss",
            Self::DecomposeBits => "hint_decompose_bits",
            Self::Decompose16 => "hint_decompose_16",
            Self::LessThan => "hint_less_than",
            Self::Log2Ceil => "hint_log2_ceil",
            Self::PrivateInputStart => "hint_private_input_start",
            Self::Xmss => "hint_xmss",
            Self::Merkle => "hint_merkle",
        }
    }

    pub fn n_args(&self) -> usize {
        match self {
            Self::DecomposeBitsXMSS => 5,
            Self::DecomposeBits => 4,
            Self::Decompose16 => 3,
            Self::LessThan => 3,
            Self::Log2Ceil => 2,
            Self::PrivateInputStart => 1,
            Self::Xmss => 1,
            Self::Merkle => 2,
        }
    }

    pub fn execute(&self, args: &[MemOrConstant], ctx: &mut HintExecutionContext<'_>) -> Result<(), RunnerError> {
        match self {
            Self::DecomposeBitsXMSS => {
                let decomposed_ptr = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let remaining_ptr = args[1].read_value(ctx.memory, ctx.fp)?.to_usize();
                let to_decompose_ptr = args[2].read_value(ctx.memory, ctx.fp)?.to_usize();
                let num_to_decompose = args[3].read_value(ctx.memory, ctx.fp)?.to_usize();
                let chunk_size = args[4].read_value(ctx.memory, ctx.fp)?.to_usize();
                assert!(24_usize.is_multiple_of(chunk_size));
                let mut memory_index_decomposed = decomposed_ptr;
                let mut memory_index_remaining = remaining_ptr;
                for i in 0..num_to_decompose {
                    let value = ctx.memory.get(to_decompose_ptr + i)?.to_usize();
                    for i in 0..24 / chunk_size {
                        let value = F::from_usize((value >> (chunk_size * i)) & ((1 << chunk_size) - 1));
                        ctx.memory.set(memory_index_decomposed, value)?;
                        memory_index_decomposed += 1;
                    }
                    ctx.memory.set(memory_index_remaining, F::from_usize(value >> 24))?;
                    memory_index_remaining += 1;
                }
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
            Self::Decompose16 => {
                let value = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let lo_ptr = args[1].memory_address(ctx.fp)?;
                let hi_ptr = args[2].memory_address(ctx.fp)?;
                let lo = value & 0xFFFF;
                let hi = value >> 16;
                ctx.memory.set(lo_ptr, F::from_usize(lo))?;
                ctx.memory.set(hi_ptr, F::from_usize(hi))?;
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
            Self::PrivateInputStart => {
                let res_ptr = args[0].memory_address(ctx.fp)?;
                ctx.memory.set(res_ptr, F::from_usize(ctx.private_input_start))?;
            }
            Self::Xmss => {
                let buf_ptr = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let index = *ctx.xmss_hint_index;
                assert!(
                    index < ctx.xmss_signatures.len(),
                    "hint_xmss: not enough XMSS signatures (index={})",
                    index
                );
                let sig = &ctx.xmss_signatures[index];
                assert_eq!(sig.len(), SIG_SIZE_FE);
                ctx.memory.set_slice(buf_ptr, sig)?;
                *ctx.xmss_hint_index += 1;
            }
            Self::Merkle => {
                let buf_ptr = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let n = args[1].read_value(ctx.memory, ctx.fp)?.to_usize();
                let index = *ctx.merkle_hint_index;
                assert!(
                    index < ctx.merkle_paths.len(),
                    "hint_merkle: not enough Merkle paths (index={})",
                    index
                );
                let path = &ctx.merkle_paths[index];
                assert_eq!(
                    path.len(),
                    n,
                    "hint_merkle: path length mismatch (expected={}, got={})",
                    n,
                    path.len()
                );
                ctx.memory.set_slice(buf_ptr, path)?;
                *ctx.merkle_hint_index += 1;
            }
        }
        Ok(())
    }

    pub fn find_by_name(name: &str) -> Option<Self> {
        CUSTOM_HINTS.iter().find(|hint| hint.name() == name).copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Boolean {
    Equal,
    Different,
    LessThan,
    LessOrEqual,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BooleanExpr<E> {
    pub left: E,
    pub right: E,
    pub kind: Boolean,
}

/// Execution state for hint processing
#[derive(Debug)]
pub struct HintExecutionContext<'a> {
    pub memory: &'a mut Memory,
    pub fp: usize,
    pub ap: &'a mut usize,
    pub std_out: &'a mut String,
    pub instruction_history: &'a mut ExecutionHistory,
    pub cpu_cycles_before_new_line: &'a mut usize,
    pub cpu_cycles: usize,
    pub last_checkpoint_cpu_cycles: &'a mut usize,
    pub checkpoint_ap: &'a mut usize,
    pub profiling: bool,
    pub memory_profile: &'a mut MemoryProfile,
    pub private_input_start: usize,
    pub xmss_signatures: &'a [Vec<F>],
    pub xmss_hint_index: &'a mut usize,
    pub merkle_paths: &'a [Vec<F>],
    pub merkle_hint_index: &'a mut usize,
    /// Pending deref hints: (target_addr, src_addr)
    /// Constraint: memory[target_addr] = memory[memory[src_addr]]
    /// Resolved at end of execution in correct order.
    pub pending_deref_hints: &'a mut Vec<(usize, usize)>,
}

impl Hint {
    /// Execute this hint within the given execution context
    #[inline(always)]
    pub fn execute_hint(&self, ctx: &mut HintExecutionContext<'_>) -> Result<(), RunnerError> {
        match self {
            Self::RequestMemory {
                function_name,
                offset,
                size,
            } => {
                let size = size.read_value(ctx.memory, ctx.fp)?.to_usize();

                let allocation_start_addr = *ctx.ap;
                ctx.memory.set(ctx.fp + *offset, F::from_usize(allocation_start_addr))?;
                *ctx.ap += size;

                if ctx.profiling {
                    ctx.memory_profile.objects.insert(
                        allocation_start_addr,
                        MemoryObject {
                            object_type: MemoryObjectType::NonVectorHeapObject,
                            function_name: function_name.clone(),
                            size,
                        },
                    );
                }
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
                let values = content
                    .iter()
                    .map(|value| Ok(value.read_value(ctx.memory, ctx.fp)?.to_string()))
                    .collect::<Result<Vec<_>, _>>()?;
                // Logs for performance analysis:
                if values[0] == "123456789" {
                    if values.len() == 1 {
                        *ctx.std_out += "[CHECKPOINT]\n";
                    } else {
                        assert_eq!(values.len(), 2);
                        let new_no_vec_memory = *ctx.ap - *ctx.checkpoint_ap;
                        *ctx.std_out += &format!(
                            "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {}\n",
                            values[1],
                            pretty_integer(ctx.cpu_cycles - *ctx.last_checkpoint_cpu_cycles),
                            pretty_integer(new_no_vec_memory),
                        );
                    }

                    *ctx.last_checkpoint_cpu_cycles = ctx.cpu_cycles;
                    *ctx.checkpoint_ap = *ctx.ap;
                }

                let line_info = line_info.replace(';', "");
                *ctx.std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
            }
            Self::LocationReport { location } => {
                ctx.instruction_history.lines.push(*location);
                ctx.instruction_history
                    .lines_cycles
                    .push(*ctx.cpu_cycles_before_new_line);
                *ctx.cpu_cycles_before_new_line = 0;
            }
            Self::Label { .. } => {}
            Self::StackFrame { label, size } => {
                if ctx.profiling {
                    ctx.memory_profile.objects.insert(
                        ctx.fp,
                        MemoryObject {
                            object_type: MemoryObjectType::StackFrame,
                            function_name: label.clone(),
                            size: *size,
                        },
                    );
                }
            }
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
                if let Some(msg) = message {
                    *ctx.std_out += &format!("[PANIC] {}\n", msg);
                }
            }
        }
        Ok(())
    }
}

impl Display for Hint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RequestMemory {
                function_name: _,
                offset,
                size,
            } => {
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
            Self::StackFrame { label, size } => {
                write!(f, "stack frame for {label} size {size}")
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

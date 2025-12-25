use crate::core::{F, Label, SourceLocation};
use crate::diagnostics::{MemoryObject, MemoryObjectType, MemoryProfile, RunnerError};
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::operands::MemOrConstant;
use multilinear_toolkit::prelude::*;
use std::fmt::Debug;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::ops::Range;
use strum::IntoEnumIterator;
use utils::{ToUsize, pretty_integer};

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
    PrivateInputStart {
        res_offset: usize,
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, strum::EnumIter)]
pub enum CustomHint {
    // Decompose values into their custom representations:
    /// each field element x is decomposed to: (a0, a1, a2, ..., a11, b) where:
    /// x = a0 + a1.4 + a2.4^2 + a3.4^3 + ... + a11.4^11 + b.2^24
    /// and ai < 4, b < 2^7 - 1
    /// The decomposition is unique, and always exists (except for x = -1)
    DecomposeBitsXMSS,
    DecomposeBits,
}

impl CustomHint {
    pub fn name(&self) -> &str {
        match self {
            Self::DecomposeBitsXMSS => "hint_decompose_bits_xmss",
            Self::DecomposeBits => "hint_decompose_bits",
        }
    }

    pub fn n_args_range(&self) -> Range<usize> {
        match self {
            Self::DecomposeBitsXMSS => 3..usize::MAX,
            Self::DecomposeBits => 3..4,
        }
    }

    pub fn execute(&self, args: &[MemOrConstant], ctx: &mut HintExecutionContext<'_>) -> Result<(), RunnerError> {
        match self {
            Self::DecomposeBitsXMSS => {
                let decomposed = &args[0];
                let remaining = &args[1];
                let to_decompose = &args[2..];
                let mut memory_index_decomposed = decomposed.read_value(ctx.memory, ctx.fp)?.to_usize();
                let mut memory_index_remaining = remaining.read_value(ctx.memory, ctx.fp)?.to_usize();
                for value_source in to_decompose {
                    let value = value_source.read_value(ctx.memory, ctx.fp)?.to_usize();
                    for i in 0..12 {
                        let value = F::from_usize((value >> (2 * i)) & 0b11);
                        ctx.memory.set(memory_index_decomposed, value)?;
                        memory_index_decomposed += 1;
                    }
                    ctx.memory.set(memory_index_remaining, F::from_usize(value >> 24))?;
                    memory_index_remaining += 1;
                }
            }
            Self::DecomposeBits => {
                let to_decompose = args[0].read_value(ctx.memory, ctx.fp)?.to_usize();
                let mut memory_index = args[1].read_value(ctx.memory, ctx.fp)?.to_usize();
                let num_bits = args[2].read_value(ctx.memory, ctx.fp)?.to_usize();
                assert!(num_bits <= F::bits());
                for i in 0..num_bits {
                    let bit = F::from_bool(to_decompose & (1 << i) != 0);
                    ctx.memory.set(memory_index, bit)?;
                    memory_index += 1;
                }
            }
        }
        Ok(())
    }

    pub fn find_by_name(name: &str) -> Option<Self> {
        for hint in Self::iter() {
            if hint.name() == name {
                return Some(hint);
            }
        }
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Boolean {
    Equal,
    Different,
    LessThan,
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
    pub private_input_start: usize, // normal pointer
    pub fp: usize,
    pub ap: &'a mut usize,
    pub counter_hint: &'a mut usize,
    pub std_out: &'a mut String,
    pub instruction_history: &'a mut ExecutionHistory,
    pub cpu_cycles_before_new_line: &'a mut usize,
    pub cpu_cycles: usize,
    pub last_checkpoint_cpu_cycles: &'a mut usize,
    pub checkpoint_ap: &'a mut usize,
    pub profiling: bool,
    pub memory_profile: &'a mut MemoryProfile,
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
            Self::PrivateInputStart { res_offset } => {
                ctx.memory
                    .set(ctx.fp + *res_offset, F::from_usize(ctx.private_input_start))?;
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
                };
                if !condition_holds {
                    return Err(RunnerError::DebugAssertFailed(
                        format!("{} {} {}", left, bool_expr.kind, right),
                        *location,
                    ));
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
            Self::PrivateInputStart { res_offset } => {
                write!(f, "m[fp + {res_offset}] = private_input_start()")
            }
            Self::Custom(hint, args) => {
                let decomposed = &args[0];
                let remaining = &args[1];
                let to_decompose = &args[2..];
                write!(f, "{}(m[fp + {decomposed}], m[fp + {remaining}], ", hint.name())?;
                for (i, v) in to_decompose.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
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
        }
    }
}

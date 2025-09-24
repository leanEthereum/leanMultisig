use crate::core::{DIMENSION, F, LOG_VECTOR_LEN, Label, SourceLineNumber, VECTOR_LEN};
use crate::diagnostics::RunnerError;
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::operands::MemOrConstant;
use p3_field::{Field, PrimeCharacteristicRing};
use std::fmt::{Display, Formatter};
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
        /// Memory offset where hint will be stored: m[fp + offset]
        offset: usize,
        /// The requested memory size
        size: MemOrConstant,
        /// Whether memory should be vectorized (aligned)
        vectorized: bool,
        /// Length for vectorized memory allocation
        vectorized_len: usize,
    },
    /// Decompose values into their bit representations
    DecomposeBits {
        /// Memory offset for results: m[fp + res_offset..fp + res_offset + 31 * len(to_decompose)]
        res_offset: usize,
        /// Values to decompose into bits
        to_decompose: Vec<MemOrConstant>,
    },
    /// Provide a counter value
    CounterHint {
        /// Memory offset where counter result will be stored: m[fp + res_offset]
        res_offset: usize,
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
        location: SourceLineNumber,
    },
    /// Jump destination label (for debugging purposes)
    Label { label: Label },
}

/// Execution state for hint processing
#[derive(Debug)]
pub struct HintExecutionContext<'a> {
    pub memory: &'a mut Memory,
    pub fp: usize,
    pub ap: &'a mut usize,
    pub ap_vec: &'a mut usize,
    pub counter_hint: &'a mut usize,
    pub std_out: &'a mut String,
    pub instruction_history: &'a mut ExecutionHistory,
    pub cpu_cycles_before_new_line: &'a mut usize,
    pub cpu_cycles: usize,
    pub last_checkpoint_cpu_cycles: &'a mut usize,
    pub checkpoint_ap: &'a mut usize,
    pub checkpoint_ap_vec: &'a mut usize,
}

impl Hint {
    /// Execute this hint within the given execution context
    pub fn execute_hint(&self, ctx: &mut HintExecutionContext<'_>) -> Result<bool, RunnerError> {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
                vectorized_len,
            } => {
                let size = size.read_value(ctx.memory, ctx.fp)?.to_usize();

                if *vectorized {
                    assert!(*vectorized_len >= LOG_VECTOR_LEN, "TODO");

                    // padding:
                    while !(*ctx.ap_vec * VECTOR_LEN).is_multiple_of(1 << *vectorized_len) {
                        *ctx.ap_vec += 1;
                    }
                    ctx.memory.set(
                        ctx.fp + *offset,
                        F::from_usize(*ctx.ap_vec >> (*vectorized_len - LOG_VECTOR_LEN)),
                    )?;
                    *ctx.ap_vec += size << (*vectorized_len - LOG_VECTOR_LEN);
                } else {
                    ctx.memory.set(ctx.fp + *offset, F::from_usize(*ctx.ap))?;
                    *ctx.ap += size;
                }
                Ok(false) // does not increase PC
            }
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                let mut memory_index = ctx.fp + *res_offset;
                for value_source in to_decompose {
                    let value = value_source.read_value(ctx.memory, ctx.fp)?.to_usize();
                    for i in 0..F::bits() {
                        let bit = F::from_bool(value & (1 << i) != 0);
                        ctx.memory.set(memory_index, bit)?;
                        memory_index += 1;
                    }
                }
                Ok(false)
            }
            Self::CounterHint { res_offset } => {
                ctx.memory
                    .set(ctx.fp + *res_offset, F::from_usize(*ctx.counter_hint))?;
                *ctx.counter_hint += 1;
                Ok(false)
            }
            Self::Inverse { arg, res_offset } => {
                let value = arg.read_value(ctx.memory, ctx.fp)?;
                let result = value.try_inverse().unwrap_or(F::ZERO);
                ctx.memory.set(ctx.fp + *res_offset, result)?;
                Ok(false)
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
                        let new_vec_memory = (*ctx.ap_vec - *ctx.checkpoint_ap_vec) * DIMENSION;
                        *ctx.std_out += &format!(
                            "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {} ({:.1}% vec)\n",
                            values[1],
                            pretty_integer(ctx.cpu_cycles - *ctx.last_checkpoint_cpu_cycles),
                            pretty_integer(new_no_vec_memory + new_vec_memory),
                            new_vec_memory as f64 / (new_no_vec_memory + new_vec_memory) as f64
                                * 100.0
                        );
                    }

                    *ctx.last_checkpoint_cpu_cycles = ctx.cpu_cycles;
                    *ctx.checkpoint_ap = *ctx.ap;
                    *ctx.checkpoint_ap_vec = *ctx.ap_vec;
                    return Ok(true); // continue (skip the rest of this iteration)
                }

                let line_info = line_info.replace(';', "");
                *ctx.std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
                Ok(false)
            }
            Self::LocationReport { location } => {
                ctx.instruction_history.lines.push(*location);
                ctx.instruction_history
                    .cycles
                    .push(*ctx.cpu_cycles_before_new_line);
                *ctx.cpu_cycles_before_new_line = 0;
                Ok(false)
            }
            Self::Label { label: _ } => Ok(false),
        }
    }
}

impl Display for Hint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
                vectorized_len,
            } => {
                if *vectorized {
                    write!(
                        f,
                        "m[fp + {offset}] = request_memory_vec({size}, {vectorized_len})"
                    )
                } else {
                    write!(f, "m[fp + {offset}] = request_memory({size})")
                }
            }
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                write!(f, "m[fp + {res_offset}] = decompose_bits(")?;
                for (i, v) in to_decompose.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
            }
            Self::CounterHint { res_offset } => {
                write!(f, "m[fp + {res_offset}] = counter_hint()")
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
                location: line_number,
            } => {
                write!(f, "source line number: {line_number}")
            }
            Self::Label { label } => {
                write!(f, "label: {label}")
            }
        }
    }
}

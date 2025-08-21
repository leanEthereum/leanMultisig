use std::{
    fmt,
    fmt::{Display, Formatter},
};

use p3_field::{Field, PrimeCharacteristicRing};
use utils::ToUsize;

use super::MemOrConstant;
use crate::{DIMENSION, F, Memory, RunnerError};

/// Hints are special instructions for the prover to resolve non-determinism.
///
/// They are not part of the verified computation trace.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Hint {
    /// A hint for the prover to allocate a new memory segment for a function's stack frame.
    ///
    /// This is the core mechanism for memory management in a VM without an `ap` (allocation pointer)
    /// register. The compiler pre-calculates the required memory size for each function.
    RequestMemory {
        /// The offset from `fp` where the pointer to the newly allocated segment will be stored.
        offset: usize,
        /// The requested size of the memory segment in scalar field elements.
        size: MemOrConstant,
        /// If true, the start of the allocated memory is aligned to an 8-element boundary
        /// to facilitate vectorized memory access for extension field operations.
        /// The value stored at `m[fp + offset]` will be the aligned address divided by 8.
        vectorized: bool,
    },
    /// A hint for the prover to compute the bit decomposition of a base field element.
    ///
    /// This is a non-deterministic operation used for operations like range checks
    /// or other logic required by the XMSS signature scheme.
    DecomposeBits {
        /// The starting offset from `fp` where the resulting bits will be stored.
        res_offset: usize,
        /// The field element that needs to be decomposed into its bits.
        to_decompose: MemOrConstant,
    },
    /// A hint used for debugging to print values from memory during execution.
    Print {
        /// A string containing line information (e.g., file and line number) for context.
        line_info: String,
        /// A list of memory locations or constants whose values should be printed.
        content: Vec<MemOrConstant>,
    },
    /// A hint for the prover to compute the modular inverse of a field element.
    Inverse {
        /// The value to be inverted.
        arg: MemOrConstant,
        /// The offset from `fp` where the result (`arg^-1`) will be stored. If `arg` is zero, zero is stored.
        res_offset: usize,
    },
}

impl Hint {
    pub fn execute(
        &self,
        memory: &mut Memory,
        fp: usize,
        ap: &mut usize,
        ap_vec: &mut usize,
        std_out: &mut String,
        cpu_cycles: usize,
        last_checkpoint_cpu_cycles: &mut usize,
        checkpoint_ap: &mut usize,
        checkpoint_ap_vec: &mut usize,
    ) -> Result<(), RunnerError> {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => {
                let sz = size.read_value(memory, fp)?.to_usize();
                if *vectorized {
                    // find the next multiple of 8
                    memory.set(fp + *offset, F::from_usize(*ap_vec))?;
                    *ap_vec += sz;
                } else {
                    memory.set(fp + *offset, F::from_usize(*ap))?;
                    *ap += sz;
                }
                // does not increase PC
            }
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                let to_decompose_value = to_decompose.read_value(memory, fp)?.to_usize();
                for i in 0..F::bits() {
                    let bit = if to_decompose_value & (1 << i) != 0 {
                        F::ONE
                    } else {
                        F::ZERO
                    };
                    memory.set(fp + *res_offset + i, bit)?;
                }
            }
            Self::Inverse { arg, res_offset } => {
                let value = arg.read_value(memory, fp)?;
                let result = value.try_inverse().unwrap_or(F::ZERO);
                memory.set(fp + *res_offset, result)?;
            }
            Self::Print { line_info, content } => {
                let values = content
                    .iter()
                    .map(|m| Ok(m.read_value(memory, fp)?.to_string()))
                    .collect::<Result<Vec<_>, RunnerError>>()?;

                // Logs for performance analysis:
                if values.first().is_some_and(|s| s == "123456789") {
                    use utils::pretty_integer;
                    if values.len() == 1 {
                        *std_out += "[CHECKPOINT]\n";
                    } else {
                        let new_no_vec = *ap - *checkpoint_ap;
                        let new_vec = (*ap_vec - *checkpoint_ap_vec) * DIMENSION;
                        *std_out += &format!(
                            "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {} ({:.1}% vec)\n",
                            values[1],
                            pretty_integer(cpu_cycles - *last_checkpoint_cpu_cycles),
                            pretty_integer(new_no_vec + new_vec),
                            new_vec as f64 / (new_no_vec + new_vec) as f64 * 100.0
                        );
                    }
                    *last_checkpoint_cpu_cycles = cpu_cycles;
                    *checkpoint_ap = *ap;
                    *checkpoint_ap_vec = *ap_vec;
                } else {
                    let line_info = line_info.replace(';', "");
                    *std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
                    // does not increase PC
                }
            }
        }
        Ok(())
    }
}

impl Display for Hint {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => {
                write!(
                    f,
                    "m[fp + {offset}] = {}({size})",
                    if *vectorized { "malloc_vec" } else { "malloc" }
                )
            }
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                write!(f, "m[fp + {res_offset}] = decompose_bits({to_decompose})")
            }
            Self::Print { line_info, content } => {
                write!(f, "print(")?;
                for (i, c) in content.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{c}")?;
                }
                write!(f, ") for \"{line_info}\"")
            }
            Self::Inverse { arg, res_offset } => {
                write!(f, "m[fp + {res_offset}] = inverse({arg})")
            }
        }
    }
}

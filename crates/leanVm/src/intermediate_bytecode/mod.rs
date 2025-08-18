use std::{collections::BTreeMap, fmt};

use crate::{
    bytecode::operation::Operation,
    lang::{Label, const_expr::ConstExpression},
};

pub mod intermediate_value;
pub use intermediate_value::*;
pub mod operation;
pub use operation::*;

#[derive(Debug, Clone)]
pub struct IntermediateBytecode {
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    pub memory_size_per_function: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediaryMemOrFpOrConstant {
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
    Fp,
    Constant(ConstExpression),
}

#[derive(Debug, Clone)]
pub enum IntermediateInstruction {
    Computation {
        operation: Operation,
        arg_a: IntermediateValue,
        arg_c: IntermediateValue,
        res: IntermediateValue,
    },
    Deref {
        shift_0: ConstExpression,
        shift_1: ConstExpression,
        res: IntermediaryMemOrFpOrConstant,
    }, // res = m[m[fp + shift_0]]
    Panic,
    Jump {
        dest: IntermediateValue,
        updated_fp: Option<IntermediateValue>,
    },
    JumpIfNotZero {
        condition: IntermediateValue,
        dest: IntermediateValue,
        updated_fp: Option<IntermediateValue>,
    },
    Poseidon2_16 {
        arg_a: IntermediateValue, // vectorized pointer, of size 1
        arg_b: IntermediateValue, // vectorized pointer, of size 1
        res: IntermediateValue,   // vectorized pointer, of size 2
    },
    Poseidon2_24 {
        arg_a: IntermediateValue, // vectorized pointer, of size 2 (2 first inputs)
        arg_b: IntermediateValue, // vectorized pointer, of size 1 (3rd = last input)
        res: IntermediateValue,   // vectorized pointer, of size 1 (3rd = last output)
    },
    DotProduct {
        arg0: IntermediateValue, // vectorized pointer
        arg1: IntermediateValue, // vectorized pointer
        res: IntermediateValue,  // vectorized pointer
        size: ConstExpression,
    },
    MultilinearEval {
        coeffs: IntermediateValue, // vectorized pointer, chunk size = 2^n_vars
        point: IntermediateValue,  // vectorized pointer, of size `n_vars`
        res: IntermediateValue,    // vectorized pointer, of size 1
        n_vars: ConstExpression,
    },
    // HINTS (does not appears in the final bytecode)
    Inverse {
        // If the value is zero, it will return zero.
        arg: IntermediateValue, // the value to invert
        res_offset: usize,      // m[fp + res_offset] will contain the result
    },
    RequestMemory {
        offset: ConstExpression, // m[fp + offset] where the hint will be stored
        size: IntermediateValue, // the hint
        vectorized: bool, // if true, will be 8-alligned, and the returned pointer will be "divied" by 8 (i.e. everything is in chunks of 8 field elements)
    },
    DecomposeBits {
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31] will contain the decomposed bits
        to_decompose: IntermediateValue,
    },
    Print {
        line_info: String, // information about the line where the print occurs
        content: Vec<IntermediateValue>, // values to print
    },
}

impl IntermediateInstruction {
    #[must_use]
    pub fn computation(
        operation: HighLevelOperation,
        arg_a: IntermediateValue,
        arg_c: IntermediateValue,
        res: IntermediateValue,
    ) -> Self {
        match operation {
            HighLevelOperation::Add => Self::Computation {
                operation: Operation::Add,
                arg_a,
                arg_c,
                res,
            },
            HighLevelOperation::Mul => Self::Computation {
                operation: Operation::Mul,
                arg_a,
                arg_c,
                res,
            },
            HighLevelOperation::Sub => Self::Computation {
                operation: Operation::Add,
                arg_a: res,
                arg_c,
                res: arg_a,
            },
            HighLevelOperation::Div => Self::Computation {
                operation: Operation::Mul,
                arg_a: res,
                arg_c,
                res: arg_a,
            },
            HighLevelOperation::Exp => unreachable!(),
        }
    }

    #[must_use]
    pub const fn equality(left: IntermediateValue, right: IntermediateValue) -> Self {
        Self::Computation {
            operation: Operation::Add,
            arg_a: left,
            arg_c: IntermediateValue::Constant(ConstExpression::zero()),
            res: right,
        }
    }
}

impl fmt::Display for IntermediaryMemOrFpOrConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}

impl fmt::Display for IntermediateInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]"),
            Self::DotProduct {
                arg0,
                arg1,
                res,
                size,
            } => write!(f, "dot_product({arg0}, {arg1}, {res}, {size})"),
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => write!(f, "multilinear_eval({coeffs}, {point}, {res}, {n_vars})"),
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                write!(f, "m[fp + {res_offset}..] = decompose_bits({to_decompose})")
            }
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                write!(f, "{res} = {arg_a} {operation} {arg_c}")
            }
            Self::Panic => write!(f, "panic"),
            Self::Jump { dest, updated_fp } => {
                if let Some(fp) = updated_fp {
                    write!(f, "jump {dest} with fp = {fp}")
                } else {
                    write!(f, "jump {dest}")
                }
            }
            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                if let Some(fp) = updated_fp {
                    write!(f, "jump_if_not_zero {condition} to {dest} with fp = {fp}")
                } else {
                    write!(f, "jump_if_not_zero {condition} to {dest}")
                }
            }
            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                write!(f, "{arg_a} = poseidon2_16({arg_b}, {res})")
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_24({arg_a}, {arg_b})")
            }
            Self::Inverse { arg, res_offset } => {
                write!(f, "m[fp + {res_offset}] = inverse({arg})")
            }
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => write!(
                f,
                "m[fp + {}] = {}({})",
                offset,
                if *vectorized { "malloc_vec" } else { "malloc" },
                size,
            ),
            Self::Print { line_info, content } => write!(
                f,
                "print {}: {}",
                line_info,
                content
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl fmt::Display for IntermediateBytecode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Iterate through each labeled block of instructions in the bytecode.
        for (label, instructions) in &self.bytecode {
            // Write the label for the current block, followed by a newline.
            writeln!(f, "\n{label}:")?;
            // Iterate through each instruction within the block.
            for instruction in instructions {
                // Write the instruction, indented with two spaces for readability.
                writeln!(f, "  {instruction}")?;
            }
        }

        // Write the header for the memory size section.
        writeln!(f, "\nMemory size per function:")?;
        // Iterate through the recorded memory sizes for each function.
        for (function_name, size) in &self.memory_size_per_function {
            // Write the function name and its corresponding memory size.
            writeln!(f, "{function_name}: {size}")?;
        }

        // Return Ok to indicate that formatting was successful.
        Ok(())
    }
}

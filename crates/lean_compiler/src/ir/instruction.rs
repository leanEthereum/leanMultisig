use super::operation::HighLevelOperation;
use super::value::{IntermediaryMemOrFpOrConstant, IntermediateValue};
use crate::lang::ConstExpression;
use lean_vm::{Operation, SourceLineNumber};
use std::fmt::{Display, Formatter, Result as FmtResult};

/// Core instruction type for the intermediate representation.
#[derive(Debug, Clone)]
pub enum IntermediateInstruction {
    /// Basic arithmetic computation: res = arg_a op arg_c
    Computation {
        operation: Operation,
        arg_a: IntermediateValue,
        arg_c: IntermediateValue,
        res: IntermediateValue,
    },
    /// Indirect memory access: res = m[m[fp + shift_0] + shift_1]
    Deref {
        shift_0: ConstExpression,
        shift_1: ConstExpression,
        res: IntermediaryMemOrFpOrConstant,
    },
    /// Abort execution
    Panic,
    /// Unconditional jump
    Jump {
        dest: IntermediateValue,
        updated_fp: Option<IntermediateValue>,
    },
    /// Conditional jump (jump if condition != 0)
    JumpIfNotZero {
        condition: IntermediateValue,
        dest: IntermediateValue,
        updated_fp: Option<IntermediateValue>,
    },
    /// Poseidon2 hash with 16-element state
    Poseidon2_16 {
        arg_a: IntermediateValue, // vectorized pointer, size 1
        arg_b: IntermediateValue, // vectorized pointer, size 1
        res: IntermediateValue,   // vectorized pointer, size 2
    },
    /// Poseidon2 hash with 24-element state
    Poseidon2_24 {
        arg_a: IntermediateValue, // vectorized pointer, size 2
        arg_b: IntermediateValue, // vectorized pointer, size 1
        res: IntermediateValue,   // vectorized pointer, size 1
    },
    /// Dot product computation
    DotProduct {
        arg0: IntermediateValue, // vectorized pointer
        arg1: IntermediateValue, // vectorized pointer
        res: IntermediateValue,  // vectorized pointer
        size: ConstExpression,
    },
    /// Multilinear polynomial evaluation
    MultilinearEval {
        coeffs: IntermediateValue, // vectorized pointer, chunk size = 2^n_vars
        point: IntermediateValue,  // vectorized pointer, size n_vars
        res: IntermediateValue,    // vectorized pointer, size 1
        n_vars: ConstExpression,
    },
    /// Field element inverse hint
    Inverse {
        arg: IntermediateValue,
        res_offset: usize,
    },
    /// Memory allocation request
    RequestMemory {
        offset: ConstExpression,
        size: IntermediateValue,
        vectorized: bool,
        vectorized_len: IntermediateValue,
    },
    /// Bit decomposition hint
    DecomposeBits {
        res_offset: usize,
        to_decompose: Vec<IntermediateValue>,
    },
    /// Counter hint for loops
    CounterHint { res_offset: usize },
    /// Print values for debugging
    Print {
        line_info: String,
        content: Vec<IntermediateValue>,
    },
    /// Source location tracking (no-op)
    LocationReport { location: SourceLineNumber },
}

impl IntermediateInstruction {
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
            HighLevelOperation::Exp | HighLevelOperation::Mod => unreachable!(),
        }
    }

    pub const fn equality(left: IntermediateValue, right: IntermediateValue) -> Self {
        Self::Computation {
            operation: Operation::Add,
            arg_a: left,
            arg_c: IntermediateValue::Constant(ConstExpression::zero()),
            res: right,
        }
    }
}

impl Display for IntermediateInstruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                write!(f, "{res} = {arg_a} {operation} {arg_c}")
            }
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]"),
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
                write!(f, "{res} = poseidon2_16({arg_a}, {arg_b})")
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_24({arg_a}, {arg_b})")
            }
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
            Self::Inverse { arg, res_offset } => {
                write!(f, "m[fp + {res_offset}] = inverse({arg})")
            }
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
                write!(f, "m[fp + {res_offset}..] = decompose_bits(")?;
                for (i, expr) in to_decompose.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{expr}")?;
                }
                write!(f, ")")
            }
            Self::CounterHint { res_offset } => {
                write!(f, "m[fp + {res_offset}] = counter_hint()")
            }
            Self::Print { line_info, content } => {
                write!(f, "print {line_info}: ")?;
                for (i, c) in content.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{c}")?;
                }
                Ok(())
            }
            Self::LocationReport { .. } => Ok(()),
        }
    }
}

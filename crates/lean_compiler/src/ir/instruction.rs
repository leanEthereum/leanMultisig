use super::operation::HighLevelOperation;
use super::value::{IntermediaryMemOrFpOrConstant, IntermediateValue};
use crate::lang::ConstExpression;
use lean_vm::{Operation, SourceLineNumber, Table, TableT};
use std::fmt::{Display, Formatter};

/// Core instruction type for the intermediate representation.
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
    Precompile {
        table: Table,
        arg_a: IntermediateValue,
        arg_b: IntermediateValue,
        arg_c: IntermediateValue,
        aux: ConstExpression,
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
        vectorized: bool, // if true, will be (2^vectorized_len)-alligned, and the returned pointer will be "divied" by 2^vectorized_len
        vectorized_len: IntermediateValue,
    },
    DecomposeBits {
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31 * len(to_decompose)] will contain the decomposed bits
        to_decompose: Vec<IntermediateValue>,
    },
    /// each field element x is decomposed to: (a0, a1, a2, ..., a11, b) where:
    /// x = a0 + a1.4 + a2.4^2 + a3.4^3 + ... + a11.4^11 + b.2^24
    /// and ai < 4, b < 2^7 - 1
    /// The decomposition is unique, and always exists (except for x = -1)
    DecomposeCustom {
        decomposed: IntermediateValue,
        remaining: IntermediateValue,
        to_decompose: Vec<IntermediateValue>,
    },
    CounterHint {
        res_offset: usize,
    },
    Print {
        line_info: String,               // information about the line where the print occurs
        content: Vec<IntermediateValue>, // values to print
    },
    // noop, debug purpose only
    LocationReport {
        location: SourceLineNumber,
    },
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
            HighLevelOperation::Exp
            | HighLevelOperation::Mod
            | HighLevelOperation::Equal
            | HighLevelOperation::NotEqual => unreachable!(),
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
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                write!(f, "{res} = {arg_a} {operation} {arg_c}")
            }
            Self::Deref { shift_0, shift_1, res } => write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]"),
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
            Self::Precompile {
                table,
                arg_a,
                arg_b,
                arg_c,
                aux,
            } => {
                write!(f, "{}({arg_a}, {arg_b}, {arg_c}, {aux})", table.name())
            }
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
                    write!(f, "m[fp + {offset}] = request_memory_vec({size}, {vectorized_len})")
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
            Self::DecomposeCustom {
                decomposed,
                remaining,
                to_decompose,
            } => {
                write!(
                    f,
                    "decompose_custom(m[fp + {decomposed}], m[fp + {remaining}], "
                )?;
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

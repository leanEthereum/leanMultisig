use super::value::IntermediateValue;
use crate::lang::{ConstExpression, MathOperation};
use lean_vm::{BooleanExpr, CustomHint, Operation, SourceLocation, Table, TableT};
use std::fmt::{Display, Formatter};

/// Core instruction type for the intermediate representation.
#[derive(Debug, Clone)]
pub enum IntermediateInstruction {
    Computation {
        operation: Operation,
        arg_a: IntermediateValue,
        arg_b: IntermediateValue,
        res: IntermediateValue,
    },
    Deref {
        shift_0: ConstExpression,
        shift_1: ConstExpression,
        res: IntermediateValue,
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
        aux_1: ConstExpression,
        aux_2: ConstExpression,
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
    },
    CustomHint(CustomHint, Vec<IntermediateValue>),
    /// Deref hint for range checks - records constraint resolved at end of execution
    DerefHint {
        /// Offset of cell containing the address to dereference
        offset_src: ConstExpression,
        /// Offset of cell where result will be stored
        offset_target: ConstExpression,
    },
    Print {
        line_info: String,               // information about the line where the print occurs
        content: Vec<IntermediateValue>, // values to print
    },
    // noop, debug purpose only
    LocationReport {
        location: SourceLocation,
    },
    DebugAssert(BooleanExpr<IntermediateValue>, SourceLocation),
    PanicHint {
        message: Option<String>,
    },
}

impl IntermediateInstruction {
    pub fn computation(
        operation: MathOperation,
        arg_a: IntermediateValue,
        arg_b: IntermediateValue,
        res: IntermediateValue,
    ) -> Self {
        match operation {
            MathOperation::Add => Self::Computation {
                operation: Operation::Add,
                arg_a,
                arg_b,
                res,
            },
            MathOperation::Mul => Self::Computation {
                operation: Operation::Mul,
                arg_a,
                arg_b,
                res,
            },
            MathOperation::Sub => Self::Computation {
                operation: Operation::Add,
                arg_a: res,
                arg_b,
                res: arg_a,
            },
            MathOperation::Div => Self::Computation {
                operation: Operation::Mul,
                arg_a: res,
                arg_b,
                res: arg_a,
            },
            _ => {
                unreachable!()
            }
        }
    }

    pub const fn equality(left: IntermediateValue, right: IntermediateValue) -> Self {
        Self::Computation {
            operation: Operation::Add,
            arg_a: left,
            arg_b: IntermediateValue::Constant(ConstExpression::zero()),
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
                arg_b,
                res,
            } => {
                write!(f, "{res} = {arg_a} {operation} {arg_b}")
            }
            Self::Deref { shift_0, shift_1, res } => write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]"),
            Self::Panic => write!(f, "assert False"),
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
                aux_1,
                aux_2,
            } => {
                write!(f, "{}({arg_a}, {arg_b}, {arg_c}, {aux_1}, {aux_2})", table.name())
            }
            Self::Inverse { arg, res_offset } => {
                write!(f, "m[fp + {res_offset}] = inverse({arg})")
            }
            Self::RequestMemory { offset, size } => {
                write!(f, "m[fp + {offset}] = request_memory({size})")
            }
            Self::CustomHint(hint, args) => {
                write!(f, "{}(", hint.name())?;
                for (i, expr) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{expr}")?;
                }
                write!(f, ")")
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
            Self::DebugAssert(boolean_expr, _) => {
                write!(f, "debug_assert {boolean_expr}")
            }
            Self::DerefHint {
                offset_src,
                offset_target,
            } => {
                write!(f, "m[fp + {offset_target}] = m[m[fp + {offset_src}]]")
            }
            Self::PanicHint { message } => match message {
                Some(msg) => write!(f, "panic hint: \"{msg}\""),
                None => write!(f, "panic hint"),
            },
        }
    }
}

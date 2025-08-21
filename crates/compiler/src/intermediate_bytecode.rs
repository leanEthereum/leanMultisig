use std::collections::BTreeMap;

use p3_field::{PrimeCharacteristicRing, PrimeField64};
use vm::*;

use crate::{F, lang::ConstExpression};

#[derive(Debug, Clone)]
pub(crate) struct IntermediateBytecode {
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    pub memory_size_per_function: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IntermediateValue {
    Constant(ConstExpression),
    Fp,
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
}

impl From<ConstExpression> for IntermediateValue {
    fn from(value: ConstExpression) -> Self {
        IntermediateValue::Constant(value)
    }
}
impl TryFrom<HighLevelOperation> for Operation {
    type Error = String;

    fn try_from(value: HighLevelOperation) -> Result<Self, Self::Error> {
        match value {
            HighLevelOperation::Add => Ok(Operation::Add),
            HighLevelOperation::Mul => Ok(Operation::Mul),
            _ => Err(format!("Cannot convert {:?} to +/x", value)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum IntermediaryMemOrFpOrConstant {
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
    Fp,
    Constant(ConstExpression),
}

impl IntermediateValue {
    pub(crate) fn label(label: Label) -> Self {
        Self::Constant(ConstExpression::label(label))
    }

    pub(crate) fn is_constant(&self) -> bool {
        matches!(self, IntermediateValue::Constant(_))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HighLevelOperation {
    Add,
    Mul,
    Sub,
    Div, // in the end everything compiles to either Add or Mul
    Exp, // Exponentiation, only for const expressions
}

impl HighLevelOperation {
    pub fn eval(&self, a: F, b: F) -> F {
        match self {
            HighLevelOperation::Add => a + b,
            HighLevelOperation::Mul => a * b,
            HighLevelOperation::Sub => a - b,
            HighLevelOperation::Div => a / b,
            HighLevelOperation::Exp => a.exp_u64(b.as_canonical_u64()),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum IntermediateInstruction {
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
    pub(crate) fn computation(
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

    pub(crate) fn equality(left: IntermediateValue, right: IntermediateValue) -> Self {
        Self::Computation {
            operation: Operation::Add,
            arg_a: left,
            arg_c: IntermediateValue::Constant(ConstExpression::zero()),
            res: right,
        }
    }
}

impl ToString for IntermediateValue {
    fn to_string(&self) -> String {
        match self {
            IntermediateValue::Constant(value) => value.to_string(),
            IntermediateValue::Fp => "fp".to_string(),
            IntermediateValue::MemoryAfterFp { offset } => {
                format!("m[fp + {}]", offset.to_string())
            }
        }
    }
}

impl ToString for IntermediaryMemOrFpOrConstant {
    fn to_string(&self) -> String {
        match self {
            Self::MemoryAfterFp { offset } => format!("m[fp + {}]", offset.to_string()),
            Self::Fp => "fp".to_string(),
            Self::Constant(c) => format!("{}", c.to_string()),
        }
    }
}

impl ToString for IntermediateInstruction {
    fn to_string(&self) -> String {
        match self {
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => format!(
                "{} = m[m[fp + {}] + {}]",
                res.to_string(),
                shift_0.to_string(),
                shift_1.to_string()
            ),
            Self::DotProduct {
                arg0,
                arg1,
                res,
                size,
            } => format!(
                "dot_product({}, {}, {}, {})",
                arg0.to_string(),
                arg1.to_string(),
                res.to_string(),
                size.to_string()
            ),
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => format!(
                "multilinear_eval({}, {}, {}, {})",
                coeffs.to_string(),
                point.to_string(),
                res.to_string(),
                n_vars.to_string()
            ),
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                format!(
                    "m[fp + {}..] = decompose_bits({})",
                    res_offset,
                    to_decompose.to_string()
                )
            }
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                format!(
                    "{} = {} {} {}",
                    res.to_string(),
                    arg_a.to_string(),
                    operation.to_string(),
                    arg_c.to_string()
                )
            }
            Self::Panic => "panic".to_string(),
            Self::Jump { dest, updated_fp } => {
                if let Some(fp) = updated_fp {
                    format!("jump {} with fp = {}", dest.to_string(), fp.to_string())
                } else {
                    format!("jump {}", dest.to_string())
                }
            }
            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                if let Some(fp) = updated_fp {
                    format!(
                        "jump_if_not_zero {} to {} with fp = {}",
                        condition.to_string(),
                        dest.to_string(),
                        fp.to_string()
                    )
                } else {
                    format!(
                        "jump_if_not_zero {} to {}",
                        condition.to_string(),
                        dest.to_string()
                    )
                }
            }
            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                format!(
                    "{} = poseidon2_16({}, {})",
                    arg_a.to_string(),
                    arg_b.to_string(),
                    res.to_string(),
                )
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                format!(
                    "{} = poseidon2_24({}, {})",
                    res.to_string(),
                    arg_a.to_string(),
                    arg_b.to_string(),
                )
            }
            Self::Inverse { arg, res_offset } => {
                format!("m[fp + {}] = inverse({})", res_offset, arg.to_string())
            }
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => format!(
                "m[fp + {}] = {}({})",
                offset.to_string(),
                if *vectorized { "malloc_vec" } else { "malloc" },
                size.to_string(),
            ),
            Self::Print { line_info, content } => format!(
                "print {}: {}",
                line_info,
                content
                    .iter()
                    .map(|c| c.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl ToString for HighLevelOperation {
    fn to_string(&self) -> String {
        match self {
            HighLevelOperation::Add => "+".to_string(),
            HighLevelOperation::Mul => "*".to_string(),
            HighLevelOperation::Sub => "-".to_string(),
            HighLevelOperation::Div => "/".to_string(),
            HighLevelOperation::Exp => "**".to_string(),
        }
    }
}

impl ToString for IntermediateBytecode {
    fn to_string(&self) -> String {
        let mut res = String::new();
        for (label, instructions) in &self.bytecode {
            res.push_str(&format!("\n{}:\n", label));
            for instruction in instructions {
                res.push_str(&format!("  {}\n", instruction.to_string()));
            }
        }
        res.push_str("\nMemory size per function:\n");
        for (function_name, size) in &self.memory_size_per_function {
            res.push_str(&format!("{}: {}\n", function_name, size));
        }
        res
    }
}

use super::operation::HighLevelOperation;
use super::value::{IntermediaryMemOrFpOrConstant, IntermediateValue};
use crate::lang::ConstExpression;
use lean_vm::{Operation, SourceLineNumber};
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
        vectorized: bool, // if true, will be (2^vectorized_len)-alligned, and the returned pointer will be "divied" by 2^vectorized_len
        vectorized_len: IntermediateValue,
    },
    DecomposeBits {
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31 * len(to_decompose)] will contain the decomposed bits
        to_decompose: Vec<IntermediateValue>,
    },
    CounterHint {
        res_offset: usize,
    },
    Print {
        line_info: String, // information about the line where the print occurs
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::value::{IntermediaryMemOrFpOrConstant, IntermediateValue};
    use crate::lang::ConstExpression;
    use lean_vm::{Operation, SourceLineNumber};

    #[test]
    fn test_computation_instruction() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(1),
        };
        let arg_c = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(2),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };

        let instruction = IntermediateInstruction::Computation {
            operation: Operation::Add,
            arg_a: arg_a.clone(),
            arg_c: arg_c.clone(),
            res: res.clone(),
        };

        if let IntermediateInstruction::Computation {
            operation,
            arg_a: a,
            arg_c: c,
            res: r,
        } = instruction
        {
            assert_eq!(operation, Operation::Add);
            assert_eq!(a, arg_a);
            assert_eq!(c, arg_c);
            assert_eq!(r, res);
        } else {
            panic!("Expected Computation variant");
        }
    }

    #[test]
    fn test_computation_add_operation() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(1),
        };
        let arg_c = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(2),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };

        let instruction = IntermediateInstruction::computation(
            HighLevelOperation::Add,
            arg_a.clone(),
            arg_c.clone(),
            res.clone(),
        );

        if let IntermediateInstruction::Computation {
            operation,
            arg_a: a,
            arg_c: c,
            res: r,
        } = instruction
        {
            assert_eq!(operation, Operation::Add);
            assert_eq!(a, arg_a);
            assert_eq!(c, arg_c);
            assert_eq!(r, res);
        } else {
            panic!("Expected Computation variant");
        }
    }

    #[test]
    fn test_computation_mul_operation() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(1),
        };
        let arg_c = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(2),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };

        let instruction = IntermediateInstruction::computation(
            HighLevelOperation::Mul,
            arg_a.clone(),
            arg_c.clone(),
            res.clone(),
        );

        if let IntermediateInstruction::Computation {
            operation,
            arg_a: a,
            arg_c: c,
            res: r,
        } = instruction
        {
            assert_eq!(operation, Operation::Mul);
            assert_eq!(a, arg_a);
            assert_eq!(c, arg_c);
            assert_eq!(r, res);
        } else {
            panic!("Expected Computation variant");
        }
    }

    #[test]
    fn test_computation_sub_operation() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(1),
        };
        let arg_c = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(2),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };

        let instruction = IntermediateInstruction::computation(
            HighLevelOperation::Sub,
            arg_a.clone(),
            arg_c.clone(),
            res.clone(),
        );

        // Sub is translated to: res = arg_a + arg_c => arg_a = res + arg_c
        if let IntermediateInstruction::Computation {
            operation,
            arg_a: a,
            arg_c: c,
            res: r,
        } = instruction
        {
            assert_eq!(operation, Operation::Add);
            assert_eq!(a, res); // result becomes arg_a
            assert_eq!(c, arg_c); // arg_c stays the same
            assert_eq!(r, arg_a); // original arg_a becomes result
        } else {
            panic!("Expected Computation variant");
        }
    }

    #[test]
    fn test_computation_div_operation() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(1),
        };
        let arg_c = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(2),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };

        let instruction = IntermediateInstruction::computation(
            HighLevelOperation::Div,
            arg_a.clone(),
            arg_c.clone(),
            res.clone(),
        );

        // Div is translated to: res = arg_a * arg_c => arg_a = res * arg_c
        if let IntermediateInstruction::Computation {
            operation,
            arg_a: a,
            arg_c: c,
            res: r,
        } = instruction
        {
            assert_eq!(operation, Operation::Mul);
            assert_eq!(a, res); // result becomes arg_a
            assert_eq!(c, arg_c); // arg_c stays the same
            assert_eq!(r, arg_a); // original arg_a becomes result
        } else {
            panic!("Expected Computation variant");
        }
    }

    #[test]
    fn test_equality_instruction() {
        let left = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(5),
        };
        let right = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(6),
        };

        let instruction = IntermediateInstruction::equality(left.clone(), right.clone());

        if let IntermediateInstruction::Computation {
            operation,
            arg_a,
            arg_c,
            res,
        } = instruction
        {
            assert_eq!(operation, Operation::Add);
            assert_eq!(arg_a, left);
            assert_eq!(arg_c, IntermediateValue::Constant(ConstExpression::zero()));
            assert_eq!(res, right);
        } else {
            panic!("Expected Computation variant");
        }
    }

    #[test]
    fn test_deref_instruction() {
        let shift_0 = ConstExpression::scalar(5);
        let shift_1 = ConstExpression::scalar(10);
        let res = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(15),
        };

        let instruction = IntermediateInstruction::Deref {
            shift_0: shift_0.clone(),
            shift_1: shift_1.clone(),
            res: res.clone(),
        };

        if let IntermediateInstruction::Deref {
            shift_0: s0,
            shift_1: s1,
            res: r,
        } = instruction
        {
            assert_eq!(s0, shift_0);
            assert_eq!(s1, shift_1);
            assert_eq!(r, res);
        } else {
            panic!("Expected Deref variant");
        }
    }

    #[test]
    fn test_panic_instruction() {
        let instruction = IntermediateInstruction::Panic;
        assert!(matches!(instruction, IntermediateInstruction::Panic));
    }

    #[test]
    fn test_jump_instruction_without_fp() {
        let dest = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(7),
        };
        let instruction = IntermediateInstruction::Jump {
            dest: dest.clone(),
            updated_fp: None,
        };

        if let IntermediateInstruction::Jump {
            dest: d,
            updated_fp,
        } = instruction
        {
            assert_eq!(d, dest);
            assert!(updated_fp.is_none());
        } else {
            panic!("Expected Jump variant");
        }
    }

    #[test]
    fn test_jump_instruction_with_fp() {
        let dest = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(7),
        };
        let fp = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(8),
        };
        let instruction = IntermediateInstruction::Jump {
            dest: dest.clone(),
            updated_fp: Some(fp.clone()),
        };

        if let IntermediateInstruction::Jump {
            dest: d,
            updated_fp,
        } = instruction
        {
            assert_eq!(d, dest);
            assert_eq!(updated_fp, Some(fp));
        } else {
            panic!("Expected Jump variant");
        }
    }

    #[test]
    fn test_jump_if_not_zero_instruction() {
        let condition = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(4),
        };
        let dest = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(7),
        };
        let fp = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(8),
        };

        let instruction = IntermediateInstruction::JumpIfNotZero {
            condition: condition.clone(),
            dest: dest.clone(),
            updated_fp: Some(fp.clone()),
        };

        if let IntermediateInstruction::JumpIfNotZero {
            condition: c,
            dest: d,
            updated_fp,
        } = instruction
        {
            assert_eq!(c, condition);
            assert_eq!(d, dest);
            assert_eq!(updated_fp, Some(fp));
        } else {
            panic!("Expected JumpIfNotZero variant");
        }
    }

    #[test]
    fn test_poseidon2_16_instruction() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(15),
        };
        let arg_b = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(16),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(9),
        };

        let instruction = IntermediateInstruction::Poseidon2_16 {
            arg_a: arg_a.clone(),
            arg_b: arg_b.clone(),
            res: res.clone(),
        };

        if let IntermediateInstruction::Poseidon2_16 {
            arg_a: a,
            arg_b: b,
            res: r,
        } = instruction
        {
            assert_eq!(a, arg_a);
            assert_eq!(b, arg_b);
            assert_eq!(r, res);
        } else {
            panic!("Expected Poseidon2_16 variant");
        }
    }

    #[test]
    fn test_poseidon2_24_instruction() {
        let arg_a = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(15),
        };
        let arg_b = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(16),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(9),
        };

        let instruction = IntermediateInstruction::Poseidon2_24 {
            arg_a: arg_a.clone(),
            arg_b: arg_b.clone(),
            res: res.clone(),
        };

        if let IntermediateInstruction::Poseidon2_24 {
            arg_a: a,
            arg_b: b,
            res: r,
        } = instruction
        {
            assert_eq!(a, arg_a);
            assert_eq!(b, arg_b);
            assert_eq!(r, res);
        } else {
            panic!("Expected Poseidon2_24 variant");
        }
    }

    #[test]
    fn test_dot_product_instruction() {
        let arg0 = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(17),
        };
        let arg1 = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(18),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };
        let size = ConstExpression::scalar(8);

        let instruction = IntermediateInstruction::DotProduct {
            arg0: arg0.clone(),
            arg1: arg1.clone(),
            res: res.clone(),
            size: size.clone(),
        };

        if let IntermediateInstruction::DotProduct {
            arg0: a0,
            arg1: a1,
            res: r,
            size: s,
        } = instruction
        {
            assert_eq!(a0, arg0);
            assert_eq!(a1, arg1);
            assert_eq!(r, res);
            assert_eq!(s, size);
        } else {
            panic!("Expected DotProduct variant");
        }
    }

    #[test]
    fn test_multilinear_eval_instruction() {
        let coeffs = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let point = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(11),
        };
        let res = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(3),
        };
        let n_vars = ConstExpression::scalar(4);

        let instruction = IntermediateInstruction::MultilinearEval {
            coeffs: coeffs.clone(),
            point: point.clone(),
            res: res.clone(),
            n_vars: n_vars.clone(),
        };

        if let IntermediateInstruction::MultilinearEval {
            coeffs: c,
            point: p,
            res: r,
            n_vars: n,
        } = instruction
        {
            assert_eq!(c, coeffs);
            assert_eq!(p, point);
            assert_eq!(r, res);
            assert_eq!(n, n_vars);
        } else {
            panic!("Expected MultilinearEval variant");
        }
    }

    #[test]
    fn test_inverse_instruction() {
        let arg = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(12),
        };
        let res_offset = 42;

        let instruction = IntermediateInstruction::Inverse {
            arg: arg.clone(),
            res_offset,
        };

        if let IntermediateInstruction::Inverse {
            arg: a,
            res_offset: r,
        } = instruction
        {
            assert_eq!(a, arg);
            assert_eq!(r, res_offset);
        } else {
            panic!("Expected Inverse variant");
        }
    }

    #[test]
    fn test_request_memory_instruction_non_vectorized() {
        let offset = ConstExpression::scalar(10);
        let size = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(13),
        };
        let vectorized_len = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(14),
        };

        let instruction = IntermediateInstruction::RequestMemory {
            offset: offset.clone(),
            size: size.clone(),
            vectorized: false,
            vectorized_len: vectorized_len.clone(),
        };

        if let IntermediateInstruction::RequestMemory {
            offset: o,
            size: s,
            vectorized,
            vectorized_len: vl,
        } = instruction
        {
            assert_eq!(o, offset);
            assert_eq!(s, size);
            assert!(!vectorized);
            assert_eq!(vl, vectorized_len);
        } else {
            panic!("Expected RequestMemory variant");
        }
    }

    #[test]
    fn test_request_memory_instruction_vectorized() {
        let offset = ConstExpression::scalar(10);
        let size = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(13),
        };
        let vectorized_len = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(14),
        };

        let instruction = IntermediateInstruction::RequestMemory {
            offset: offset.clone(),
            size: size.clone(),
            vectorized: true,
            vectorized_len: vectorized_len.clone(),
        };

        if let IntermediateInstruction::RequestMemory {
            offset: o,
            size: s,
            vectorized,
            vectorized_len: vl,
        } = instruction
        {
            assert_eq!(o, offset);
            assert_eq!(s, size);
            assert!(vectorized);
            assert_eq!(vl, vectorized_len);
        } else {
            panic!("Expected RequestMemory variant");
        }
    }

    #[test]
    fn test_decompose_bits_instruction() {
        let res_offset = 20;
        let to_decompose = vec![
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(20),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(21),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(22),
            },
        ];

        let instruction = IntermediateInstruction::DecomposeBits {
            res_offset,
            to_decompose: to_decompose.clone(),
        };

        if let IntermediateInstruction::DecomposeBits {
            res_offset: r,
            to_decompose: td,
        } = instruction
        {
            assert_eq!(r, res_offset);
            assert_eq!(td, to_decompose);
            assert_eq!(td.len(), 3);
        } else {
            panic!("Expected DecomposeBits variant");
        }
    }

    #[test]
    fn test_counter_hint_instruction() {
        let res_offset = 15;

        let instruction = IntermediateInstruction::CounterHint { res_offset };

        if let IntermediateInstruction::CounterHint { res_offset: r } = instruction {
            assert_eq!(r, res_offset);
        } else {
            panic!("Expected CounterHint variant");
        }
    }

    #[test]
    fn test_print_instruction() {
        let line_info = "line 42".to_string();
        let content = vec![
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(23),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(24),
            },
        ];

        let instruction = IntermediateInstruction::Print {
            line_info: line_info.clone(),
            content: content.clone(),
        };

        if let IntermediateInstruction::Print {
            line_info: li,
            content: c,
        } = instruction
        {
            assert_eq!(li, line_info);
            assert_eq!(c, content);
            assert_eq!(c.len(), 2);
        } else {
            panic!("Expected Print variant");
        }
    }

    #[test]
    fn test_location_report_instruction() {
        let location: SourceLineNumber = 123;

        let instruction = IntermediateInstruction::LocationReport { location };

        if let IntermediateInstruction::LocationReport { location: l } = instruction {
            assert_eq!(l, location);
        } else {
            panic!("Expected LocationReport variant");
        }
    }

    #[test]
    fn test_instruction_clone() {
        let original = IntermediateInstruction::Panic;
        let cloned = original.clone();
        assert!(matches!(cloned, IntermediateInstruction::Panic));

        let complex_original = IntermediateInstruction::Computation {
            operation: Operation::Add,
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(1),
            },
            arg_c: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(2),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(3),
            },
        };
        let complex_cloned = complex_original.clone();

        if let (
            IntermediateInstruction::Computation {
                operation: op1,
                arg_a: a1,
                arg_c: c1,
                res: r1,
            },
            IntermediateInstruction::Computation {
                operation: op2,
                arg_a: a2,
                arg_c: c2,
                res: r2,
            },
        ) = (&complex_original, &complex_cloned)
        {
            assert_eq!(op1, op2);
            assert_eq!(a1, a2);
            assert_eq!(c1, c2);
            assert_eq!(r1, r2);
        }
    }

    #[test]
    fn test_instruction_debug_format() {
        let instruction = IntermediateInstruction::Computation {
            operation: Operation::Add,
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(1),
            },
            arg_c: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(2),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(26),
            },
        };

        let debug_output = format!("{:?}", instruction);
        assert!(debug_output.contains("Computation"));
        assert!(debug_output.contains("Add"));
        assert!(debug_output.contains("1"));
        assert!(debug_output.contains("2"));
        assert!(debug_output.contains("26"));
    }

    #[test]
    fn test_display_computation() {
        let instruction = IntermediateInstruction::Computation {
            operation: Operation::Add,
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(1),
            },
            arg_c: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(2),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(26),
            },
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "m[fp + 26] = m[fp + 1] + m[fp + 2]");
    }

    #[test]
    fn test_display_deref() {
        let instruction = IntermediateInstruction::Deref {
            shift_0: ConstExpression::scalar(5),
            shift_1: ConstExpression::scalar(10),
            res: IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: ConstExpression::scalar(15),
            },
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "m[fp + 15] = m[m[fp + 5] + 10]");
    }

    #[test]
    fn test_display_panic() {
        let instruction = IntermediateInstruction::Panic;
        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "panic");
    }

    #[test]
    fn test_display_jump_without_fp() {
        let instruction = IntermediateInstruction::Jump {
            dest: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(7),
            },
            updated_fp: None,
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "jump m[fp + 7]");
    }

    #[test]
    fn test_display_jump_with_fp() {
        let instruction = IntermediateInstruction::Jump {
            dest: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(7),
            },
            updated_fp: Some(IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(8),
            }),
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "jump m[fp + 7] with fp = m[fp + 8]");
    }

    #[test]
    fn test_display_jump_if_not_zero_without_fp() {
        let instruction = IntermediateInstruction::JumpIfNotZero {
            condition: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(4),
            },
            dest: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(7),
            },
            updated_fp: None,
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "jump_if_not_zero m[fp + 4] to m[fp + 7]");
    }

    #[test]
    fn test_display_jump_if_not_zero_with_fp() {
        let instruction = IntermediateInstruction::JumpIfNotZero {
            condition: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(4),
            },
            dest: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(7),
            },
            updated_fp: Some(IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(8),
            }),
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "jump_if_not_zero m[fp + 4] to m[fp + 7] with fp = m[fp + 8]"
        );
    }

    #[test]
    fn test_display_poseidon2_16() {
        let instruction = IntermediateInstruction::Poseidon2_16 {
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(27),
            },
            arg_b: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(28),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(29),
            },
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "m[fp + 29] = poseidon2_16(m[fp + 27], m[fp + 28])"
        );
    }

    #[test]
    fn test_display_poseidon2_24() {
        let instruction = IntermediateInstruction::Poseidon2_24 {
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(27),
            },
            arg_b: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(28),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(29),
            },
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "m[fp + 29] = poseidon2_24(m[fp + 27], m[fp + 28])"
        );
    }

    #[test]
    fn test_display_dot_product() {
        let instruction = IntermediateInstruction::DotProduct {
            arg0: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(30),
            },
            arg1: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(31),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(26),
            },
            size: ConstExpression::scalar(8),
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "dot_product(m[fp + 30], m[fp + 31], m[fp + 26], 8)"
        );
    }

    #[test]
    fn test_display_multilinear_eval() {
        let instruction = IntermediateInstruction::MultilinearEval {
            coeffs: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(32),
            },
            point: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(33),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(26),
            },
            n_vars: ConstExpression::scalar(4),
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "multilinear_eval(m[fp + 32], m[fp + 33], m[fp + 26], 4)"
        );
    }

    #[test]
    fn test_display_inverse() {
        let instruction = IntermediateInstruction::Inverse {
            arg: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(34),
            },
            res_offset: 42,
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "m[fp + 42] = inverse(m[fp + 34])");
    }

    #[test]
    fn test_display_request_memory_non_vectorized() {
        let instruction = IntermediateInstruction::RequestMemory {
            offset: ConstExpression::scalar(10),
            size: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(35),
            },
            vectorized: false,
            vectorized_len: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(36),
            },
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "m[fp + 10] = request_memory(m[fp + 35])");
    }

    #[test]
    fn test_display_request_memory_vectorized() {
        let instruction = IntermediateInstruction::RequestMemory {
            offset: ConstExpression::scalar(10),
            size: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(35),
            },
            vectorized: true,
            vectorized_len: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(36),
            },
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "m[fp + 10] = request_memory_vec(m[fp + 35], m[fp + 36])"
        );
    }

    #[test]
    fn test_display_decompose_bits() {
        let instruction = IntermediateInstruction::DecomposeBits {
            res_offset: 20,
            to_decompose: vec![
                IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(37),
                },
                IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(38),
                },
            ],
        };

        let display_output = format!("{}", instruction);
        assert_eq!(
            display_output,
            "m[fp + 20..] = decompose_bits(m[fp + 37], m[fp + 38])"
        );
    }

    #[test]
    fn test_display_counter_hint() {
        let instruction = IntermediateInstruction::CounterHint { res_offset: 15 };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "m[fp + 15] = counter_hint()");
    }

    #[test]
    fn test_display_print() {
        let instruction = IntermediateInstruction::Print {
            line_info: "line 42".to_string(),
            content: vec![
                IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(23),
                },
                IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(24),
                },
            ],
        };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "print line 42: m[fp + 23], m[fp + 24]");
    }

    #[test]
    fn test_display_location_report() {
        let instruction = IntermediateInstruction::LocationReport { location: 123 };

        let display_output = format!("{}", instruction);
        assert_eq!(display_output, "");
    }

    #[test]
    #[should_panic(expected = "unreachable")]
    fn test_computation_exp_unreachable() {
        IntermediateInstruction::computation(
            HighLevelOperation::Exp,
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(1),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(2),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(26),
            },
        );
    }

    #[test]
    #[should_panic(expected = "unreachable")]
    fn test_computation_mod_unreachable() {
        IntermediateInstruction::computation(
            HighLevelOperation::Mod,
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(1),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(2),
            },
            IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(26),
            },
        );
    }
}

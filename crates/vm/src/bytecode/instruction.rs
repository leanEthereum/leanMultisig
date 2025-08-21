use std::{
    fmt,
    fmt::{Display, Formatter},
};

use super::{MemOrConstant, MemOrFp, MemOrFpOrConstant, Operation};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction {
    // 3 basic instructions
    Computation {
        operation: Operation,
        arg_a: MemOrConstant,
        arg_c: MemOrFp,
        res: MemOrConstant,
    },
    Deref {
        shift_0: usize,
        shift_1: usize,
        res: MemOrFpOrConstant,
    }, // res = m[m[fp + shift_0] + shift_1]
    JumpIfNotZero {
        condition: MemOrConstant,
        dest: MemOrConstant,
        updated_fp: MemOrFp,
    },
    // 4 precompiles:
    Poseidon2_16 {
        arg_a: MemOrConstant, // vectorized pointer, of size 1
        arg_b: MemOrConstant, // vectorized pointer, of size 1
        res: MemOrFp, // vectorized pointer, of size 2 (The Fp would never be used in practice)
    },
    Poseidon2_24 {
        arg_a: MemOrConstant, // vectorized pointer, of size 2 (2 first inputs)
        arg_b: MemOrConstant, // vectorized pointer, of size 1 (3rd = last input)
        res: MemOrFp, // vectorized pointer, of size 1 (3rd = last output) (The Fp would never be used in practice)
    },
    DotProductExtensionExtension {
        arg0: MemOrConstant, // vectorized pointer
        arg1: MemOrConstant, // vectorized pointer
        res: MemOrFp,        // vectorized pointer, of size 1 (never Fp in practice)
        size: usize,
    },
    MultilinearEval {
        coeffs: MemOrConstant, // vectorized pointer, chunk size = 2^n_vars
        point: MemOrConstant,  // vectorized pointer, of size `n_vars`
        res: MemOrFp,          // vectorized pointer, of size 1 (never fp in practice)
        n_vars: usize,
    },
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
            } => {
                write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]")
            }
            Self::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                write!(f, "dot_product({arg0}, {arg1}, {res}, {size})")
            }
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                write!(f, "multilinear_eval({coeffs}, {point}, {res}, {n_vars})")
            }
            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                write!(
                    f,
                    "if {condition} != 0 jump to {dest} with next(fp) = {updated_fp}"
                )
            }
            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_16({arg_a}, {arg_b})")
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_24({arg_a}, {arg_b})")
            }
        }
    }
}

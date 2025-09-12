use crate::{F, LocationInSourceCode};
use p3_field::PrimeCharacteristicRing;
use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter},
};

pub type Label = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub hints: BTreeMap<usize, Vec<Hint>>, // pc -> hints
    pub starting_frame_memory: usize,
    pub ending_pc: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrConstant {
    Constant(F),
    MemoryAfterFp { offset: usize }, // m[fp + offset]
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFpOrConstant {
    MemoryAfterFp { offset: usize }, // m[fp + offset]
    Fp,
    Constant(F),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFp {
    MemoryAfterFp { offset: usize }, // m[fp + offset]
    Fp,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operation {
    Add,
    Mul,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction {
    // 4 basic instructions: ADD, MUL, DEREF, JUMP
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
    Jump {
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
        arg0: MemOrConstant, // normal pointer, of size `size`
        arg1: MemOrConstant, // normal pointer, of size `size`
        res: MemOrFp,        // normal pointer, of size 1 (never Fp in practice)
        size: usize,
    },
    MultilinearEval {
        coeffs: MemOrConstant, // vectorized pointer, chunk size = 2^n_vars
        point: MemOrConstant, // normal pointer, pointing to `n_vars` continuous extension field elements
        res: MemOrFp,         // normal pointer, pointing to 1 extension field element
        n_vars: usize,
    },
}

impl Operation {
    pub fn compute(&self, a: F, b: F) -> F {
        match self {
            Self::Add => a + b,
            Self::Mul => a * b,
        }
    }

    pub fn inverse_compute(&self, a: F, b: F) -> Option<F> {
        match self {
            Self::Add => Some(a - b),
            Self::Mul => {
                if b == F::ZERO {
                    None
                } else {
                    Some(a / b)
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Hint {
    Inverse {
        arg: MemOrConstant, // the value to invert (return 0 if arg is zero)
        res_offset: usize,  // m[fp + res_offset] will contain the result
    },
    RequestMemory {
        offset: usize,       // m[fp + offset] where the hint will be stored
        size: MemOrConstant, // the hint
        vectorized: bool,
    },
    DecomposeBits {
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31 * len(to_decompose)] will contain the decomposed bits
        to_decompose: Vec<MemOrConstant>,
    },
    CounterHint {
        res_offset: usize, // m[fp + res_offset] will contain the result
    },
    Print {
        line_info: String,
        content: Vec<MemOrConstant>,
    },
    LocationReport {
        location: LocationInSourceCode, // debug purpose
    },
}

impl MemOrConstant {
    pub const fn zero() -> Self {
        Self::Constant(F::ZERO)
    }

    pub const fn one() -> Self {
        Self::Constant(F::ONE)
    }
}
impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (pc, instruction) in self.instructions.iter().enumerate() {
            for hint in self.hints.get(&pc).unwrap_or(&Vec::new()) {
                writeln!(f, "hint: {hint}")?;
            }
            writeln!(f, "{pc:>4}: {instruction}")?;
        }
        Ok(())
    }
}

impl Display for MemOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(c) => write!(f, "{c}"),
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
        }
    }
}

impl Display for MemOrFp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
        }
    }
}

impl Display for MemOrFpOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Mul => write!(f, "x"),
        }
    }
}

impl Display for Instruction {
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
            Self::Jump {
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

impl Display for Hint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => {
                write!(
                    f,
                    "m[fp + {}] = {}({})",
                    offset,
                    if *vectorized { "malloc_vec" } else { "malloc" },
                    size
                )
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
            Self::LocationReport { .. } => Ok(()),
        }
    }
}

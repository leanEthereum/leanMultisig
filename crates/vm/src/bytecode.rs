use crate::F;
use p3_field::PrimeCharacteristicRing;
use std::collections::BTreeMap;

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

impl Operation {
    pub fn compute(&self, a: F, b: F) -> F {
        match self {
            Operation::Add => a + b,
            Operation::Mul => a * b,
        }
    }

    pub fn inverse_compute(&self, a: F, b: F) -> Option<F> {
        match self {
            Operation::Add => Some(a - b),
            Operation::Mul => {
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
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31] will contain the decomposed bits
        to_decompose: MemOrConstant,
    },
    Print {
        line_info: String,
        content: Vec<MemOrConstant>,
    },
}

impl MemOrConstant {
    pub fn zero() -> Self {
        MemOrConstant::Constant(F::ZERO)
    }

    pub fn one() -> Self {
        MemOrConstant::Constant(F::ONE)
    }
}

impl ToString for Bytecode {
    fn to_string(&self) -> String {
        let mut pc = 0;
        let mut res = String::new();
        for instruction in &self.instructions {
            for hint in self.hints.get(&pc).unwrap_or(&Vec::new()) {
                res.push_str(&format!("hint: {}\n", hint.to_string()));
            }
            res.push_str(&format!("{:>4}: {}\n", pc, instruction.to_string()));
            pc += 1;
        }
        return res;
    }
}

impl ToString for MemOrConstant {
    fn to_string(&self) -> String {
        match self {
            Self::Constant(c) => format!("{}", c),
            Self::MemoryAfterFp { offset } => format!("m[fp + {}]", offset),
        }
    }
}

impl ToString for MemOrFp {
    fn to_string(&self) -> String {
        match self {
            Self::MemoryAfterFp { offset } => format!("m[fp + {}]", offset),
            Self::Fp => "fp".to_string(),
        }
    }
}

impl ToString for MemOrFpOrConstant {
    fn to_string(&self) -> String {
        match self {
            Self::MemoryAfterFp { offset } => format!("m[fp + {}]", offset),
            Self::Fp => "fp".to_string(),
            Self::Constant(c) => format!("{}", c),
        }
    }
}

impl ToString for Operation {
    fn to_string(&self) -> String {
        match self {
            Self::Add => "+".to_string(),
            Self::Mul => "x".to_string(),
        }
    }
}

impl ToString for Instruction {
    fn to_string(&self) -> String {
        match self {
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
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => {
                format!("{} = m[m[fp + {}] + {}]", res.to_string(), shift_0, shift_1)
            }
            Self::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                format!(
                    "dot_product({}, {}, {}, {})",
                    arg0.to_string(),
                    arg1.to_string(),
                    res.to_string(),
                    size
                )
            }
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                format!(
                    "multilinear_eval({}, {}, {}, {})",
                    coeffs.to_string(),
                    point.to_string(),
                    res.to_string(),
                    n_vars
                )
            }
            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                format!(
                    "if {} != 0 jump to {} with next(fp) = {}",
                    condition.to_string(),
                    dest.to_string(),
                    updated_fp.to_string()
                )
            }
            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                format!(
                    "{} = poseidon2_16({}, {})",
                    res.to_string(),
                    arg_a.to_string(),
                    arg_b.to_string(),
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
        }
    }
}

impl ToString for Hint {
    fn to_string(&self) -> String {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => {
                format!(
                    "m[fp + {}] = {}({})",
                    offset,
                    if *vectorized { "malloc_vec" } else { "malloc" },
                    size.to_string()
                )
            }
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                format!(
                    "m[fp + {}] = decompose_bits({})",
                    res_offset,
                    to_decompose.to_string()
                )
            }
            Self::Print { line_info, content } => {
                format!(
                    "print({}) for \"{}\"",
                    content
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<String>>()
                        .join(", "),
                    line_info,
                )
            }
            Self::Inverse { arg, res_offset } => {
                format!("m[fp + {}] = inverse({})", res_offset, arg.to_string())
            }
        }
    }
}

use std::fmt;

use crate::{
    compiler::Compiler,
    constant::{PUBLIC_INPUT_START, ZERO_VEC_PTR},
    lang::Label,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstantValue {
    Scalar(usize),
    PublicInputStart,
    PointerToZeroVector, // In the memory of chunks of 8 field elements
    FunctionSize { function_name: Label },
    Label(Label),
}

impl ConstantValue {
    #[must_use] pub fn eval_constant_value(&self, compiler: &Compiler) -> usize {
        match self {
            Self::Scalar(scalar) => *scalar,
            Self::PublicInputStart => PUBLIC_INPUT_START.offset,
            Self::PointerToZeroVector => ZERO_VEC_PTR.offset,
            Self::FunctionSize { function_name } => *compiler
                .memory_size_per_function
                .get(function_name)
                .unwrap_or_else(|| panic!("Function {function_name} not found in memory size map")),
            Self::Label(label) => compiler.label_to_pc.get(label).copied().unwrap(),
        }
    }
}

impl fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Scalar(scalar) => write!(f, "{scalar}"),
            Self::PublicInputStart => write!(f, "@public_input_start"),
            Self::PointerToZeroVector => write!(f, "@pointer_to_zero_vector"),
            Self::FunctionSize { function_name } => {
                write!(f, "@function_size_{function_name}")
            }
            Self::Label(label) => write!(f, "{label}"),
        }
    }
}

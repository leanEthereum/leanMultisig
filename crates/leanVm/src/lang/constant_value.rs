use std::fmt;

use crate::Label;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstantValue {
    Scalar(usize),
    PublicInputStart,
    PointerToZeroVector, // In the memory of chunks of 8 field elements
    FunctionSize { function_name: Label },
    Label(Label),
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

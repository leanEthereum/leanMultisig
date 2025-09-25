use crate::F;
use lean_vm::Operation;
use p3_field::PrimeCharacteristicRing;
use p3_field::PrimeField64;
use std::fmt::{Display, Formatter};
use utils::ToUsize;

/// High-level operations that can be performed in the IR.
///
/// These operations represent the semantic intent of computations
/// and may be lowered to different VM operations depending on context.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HighLevelOperation {
    /// Addition operation.
    Add,
    /// Multiplication operation.
    Mul,
    /// Subtraction operation (compiled to addition with negation).
    Sub,
    /// Division operation (compiled to multiplication with inverse).
    Div,
    /// Exponentiation (only for constant expressions).
    Exp,
    /// Modulo operation (only for constant expressions).
    Mod,
}

impl HighLevelOperation {
    pub fn eval(&self, a: F, b: F) -> F {
        match self {
            Self::Add => a + b,
            Self::Mul => a * b,
            Self::Sub => a - b,
            Self::Div => a / b,
            Self::Exp => a.exp_u64(b.as_canonical_u64()),
            Self::Mod => F::from_usize(a.to_usize() % b.to_usize()),
        }
    }
}

impl Display for HighLevelOperation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Mul => write!(f, "*"),
            Self::Sub => write!(f, "-"),
            Self::Div => write!(f, "/"),
            Self::Exp => write!(f, "**"),
            Self::Mod => write!(f, "%"),
        }
    }
}

impl TryFrom<HighLevelOperation> for Operation {
    type Error = String;

    fn try_from(value: HighLevelOperation) -> Result<Self, Self::Error> {
        match value {
            HighLevelOperation::Add => Ok(Self::Add),
            HighLevelOperation::Mul => Ok(Self::Mul),
            _ => Err(format!("Cannot convert {value:?} to +/x")),
        }
    }
}

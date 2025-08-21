use std::fmt;

use p3_field::{PrimeCharacteristicRing, PrimeField64};
use vm::F;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HighLevelOperation {
    Add,
    Mul,
    Sub,
    Div, // in the end everything compiles to either Add or Mul
    Exp, // Exponentiation, only for const expressions
}

impl HighLevelOperation {
    #[must_use]
    pub fn eval(&self, a: F, b: F) -> F {
        match self {
            Self::Add => a + b,
            Self::Mul => a * b,
            Self::Sub => a - b,
            Self::Div => a / b,
            Self::Exp => a.exp_u64(b.as_canonical_u64()),
        }
    }
}

impl fmt::Display for HighLevelOperation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Mul => write!(f, "*"),
            Self::Sub => write!(f, "-"),
            Self::Div => write!(f, "/"),
            Self::Exp => write!(f, "**"),
        }
    }
}

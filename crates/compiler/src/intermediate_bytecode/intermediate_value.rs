use std::fmt;

use vm::F;

use crate::{
    Compiler,
    lang::{ConstExpression, Label},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntermediateValue {
    Constant(ConstExpression),
    Fp,
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
}

impl IntermediateValue {
    #[must_use]
    pub const fn label(label: Label) -> Self {
        Self::Constant(ConstExpression::label(label))
    }

    #[must_use]
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    #[must_use]
    pub fn try_as_constant(&self, compiler: &Compiler) -> Option<F> {
        if let Self::Constant(c) = self {
            Some(c.eval(compiler))
        } else {
            None
        }
    }
}

impl From<ConstExpression> for IntermediateValue {
    fn from(value: ConstExpression) -> Self {
        Self::Constant(value)
    }
}

impl fmt::Display for IntermediateValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(value) => write!(f, "{value}"),
            Self::Fp => write!(f, "fp"),
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
        }
    }
}

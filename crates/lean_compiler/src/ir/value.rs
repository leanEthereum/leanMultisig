use crate::lang::ConstExpression;
use lean_vm::Label;
use std::fmt::{Display, Formatter};

/// Represents different types of values in the intermediate representation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntermediateValue {
    /// A compile-time constant value.
    Constant(ConstExpression),
    /// The current frame pointer.
    Fp,
    /// Memory location at frame pointer + offset.
    MemoryAfterFp { offset: ConstExpression },
}

impl IntermediateValue {
    pub const fn label(label: Label) -> Self {
        Self::Constant(ConstExpression::label(label))
    }

    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }
}

impl From<ConstExpression> for IntermediateValue {
    fn from(value: ConstExpression) -> Self {
        Self::Constant(value)
    }
}

impl From<Label> for IntermediateValue {
    fn from(label: Label) -> Self {
        Self::label(label)
    }
}

impl Display for IntermediateValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(value) => write!(f, "{value}"),
            Self::Fp => write!(f, "fp"),
            Self::MemoryAfterFp { offset } => {
                write!(f, "m[fp + {offset}]")
            }
        }
    }
}

/// More restrictive value type used in specific contexts.
///
/// Similar to [`IntermediateValue`] but with different ordering constraints
/// needed for certain operations like dereferencing.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediaryMemOrFpOrConstant {
    /// Memory location at frame pointer + offset.
    MemoryAfterFp { offset: ConstExpression },
    /// The current frame pointer.
    Fp,
    /// A compile-time constant value.
    Constant(ConstExpression),
}

impl Display for IntermediaryMemOrFpOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}

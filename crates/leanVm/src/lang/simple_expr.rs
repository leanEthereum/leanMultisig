use std::fmt;

use crate::lang::{ConstExpression, ConstMallocLabel, ConstantValue, Var};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleExpr {
    Var(Var),
    Constant(ConstExpression),
    ConstMallocAccess {
        malloc_label: ConstMallocLabel,
        offset: ConstExpression,
    },
}

impl SimpleExpr {
    #[must_use]
    pub fn zero() -> Self {
        Self::scalar(0)
    }

    #[must_use]
    pub fn one() -> Self {
        Self::scalar(1)
    }

    #[must_use]
    pub fn scalar(scalar: usize) -> Self {
        Self::Constant(ConstantValue::Scalar(scalar).into())
    }

    #[must_use]
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    #[must_use]
    pub fn as_constant(&self) -> Option<ConstExpression> {
        match self {
            Self::Var(_) | Self::ConstMallocAccess { .. } => None,
            Self::Constant(constant) => Some(constant.clone()),
        }
    }
}

impl From<ConstantValue> for SimpleExpr {
    fn from(constant: ConstantValue) -> Self {
        Self::Constant(constant.into())
    }
}

impl From<ConstExpression> for SimpleExpr {
    fn from(constant: ConstExpression) -> Self {
        Self::Constant(constant)
    }
}

impl From<Var> for SimpleExpr {
    fn from(var: Var) -> Self {
        Self::Var(var)
    }
}

impl fmt::Display for SimpleExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(var) => write!(f, "{var}"),
            Self::Constant(constant) => write!(f, "{constant}"),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => write!(f, "malloc_access({malloc_label}, {offset})"),
        }
    }
}

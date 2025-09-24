//! VM operation definitions

use crate::core::F;
use p3_field::PrimeCharacteristicRing;
use std::fmt::{Display, Formatter};

/// Basic arithmetic operations supported by the VM
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operation {
    Add,
    Mul,
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

impl Display for Operation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Mul => write!(f, "x"),
        }
    }
}

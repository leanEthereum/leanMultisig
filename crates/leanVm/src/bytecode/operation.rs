use std::fmt;

use p3_field::Field;

use crate::constant::F;

/// The basic arithmetic operations supported by the VM's `Computation` instruction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operation {
    /// Field addition in the base field.
    Add,
    /// Field multiplication in the base field.
    Mul,
}

impl Operation {
    /// Computes the result of applying this arithmetic operation to two operands.
    ///
    /// # Parameters
    ///
    /// - `a`: The left-hand operand.
    /// - `b`: The right-hand operand.
    ///
    /// # Returns
    ///
    /// The result of `a ⊕ b`, where `⊕` is the operation represented by `self`.
    /// For example:
    /// - If `self` is `Add`, returns `a + b`.
    /// - If `self` is `Mul`, returns `a * b`.
    #[must_use]
    pub fn compute(&self, a: F, b: F) -> F {
        match self {
            Self::Add => a + b,
            Self::Mul => a * b,
        }
    }

    /// Computes the inverse of the operation with respect to the right-hand operand.
    ///
    /// Solves for `a` given the result `c = a ⊕ b`, by computing `a = c ⊖ b`, where `⊖`
    /// is the inverse of the operation represented by `self`.
    ///
    /// # Parameters
    ///
    /// - `a`: The result value (i.e., `a ⊕ b`).
    /// - `b`: The right-hand operand of the original operation.
    ///
    /// # Returns
    ///
    /// - `Some(a)` if the inverse exists.
    /// - `None` if the inverse does not exist (e.g., `b == 0` for `Mul`).
    #[must_use]
    pub fn inverse_compute(&self, a: F, b: F) -> Option<F> {
        match self {
            Self::Add => Some(a - b),
            Self::Mul => (!b.is_zero()).then(|| a / b),
        }
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Mul => write!(f, "x"),
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    #[test]
    fn test_compute_add() {
        let op = Operation::Add;
        let val1 = F::from_u32(100);
        let val2 = F::from_u32(50);
        assert_eq!(op.compute(val1, val2), F::from_u32(150));
    }

    #[test]
    fn test_compute_mul() {
        let op = Operation::Mul;
        let val1 = F::from_u32(10);
        let val2 = F::from_u32(5);
        assert_eq!(op.compute(val1, val2), F::from_u32(50));
    }

    #[test]
    fn test_inverse_compute_add() {
        let op = Operation::Add;
        let val1 = F::from_u32(150);
        let val2 = F::from_u32(50);
        assert_eq!(op.inverse_compute(val1, val2), Some(F::from_u32(100)));
    }

    #[test]
    fn test_inverse_compute_mul_success() {
        let op = Operation::Mul;
        let val1 = F::from_u32(50);
        let val2 = F::from_u32(5);
        assert_eq!(op.inverse_compute(val1, val2), Some(F::from_u32(10)));
    }

    #[test]
    fn test_inverse_compute_mul_by_zero() {
        let op = Operation::Mul;
        let val1 = F::from_u32(50);
        let val2 = F::ZERO;
        assert_eq!(op.inverse_compute(val1, val2), None);
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::F;

    #[test]
    fn test_high_level_operation_enum_variants() {
        let add = HighLevelOperation::Add;
        let mul = HighLevelOperation::Mul;
        let sub = HighLevelOperation::Sub;
        let div = HighLevelOperation::Div;
        let exp = HighLevelOperation::Exp;
        let mod_op = HighLevelOperation::Mod;

        assert_eq!(add, HighLevelOperation::Add);
        assert_eq!(mul, HighLevelOperation::Mul);
        assert_eq!(sub, HighLevelOperation::Sub);
        assert_eq!(div, HighLevelOperation::Div);
        assert_eq!(exp, HighLevelOperation::Exp);
        assert_eq!(mod_op, HighLevelOperation::Mod);
    }

    #[test]
    fn test_high_level_operation_clone() {
        let original = HighLevelOperation::Add;
        let cloned = original.clone();
        assert_eq!(original, cloned);
    }

    #[test]
    fn test_high_level_operation_copy() {
        let original = HighLevelOperation::Mul;
        let copied = original;
        assert_eq!(original, copied);
    }

    #[test]
    fn test_high_level_operation_partial_eq() {
        assert_eq!(HighLevelOperation::Add, HighLevelOperation::Add);
        assert_ne!(HighLevelOperation::Add, HighLevelOperation::Mul);
    }

    #[test]
    fn test_high_level_operation_partial_ord() {
        let add = HighLevelOperation::Add;
        let mul = HighLevelOperation::Mul;

        assert!(add <= mul);
        assert!(add < mul);
        assert!(mul > add);
        assert!(mul >= add);
    }

    #[test]
    fn test_high_level_operation_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();

        HighLevelOperation::Add.hash(&mut hasher1);
        HighLevelOperation::Add.hash(&mut hasher2);

        assert_eq!(hasher1.finish(), hasher2.finish());
    }

    #[test]
    fn test_eval_add_operation() {
        let op = HighLevelOperation::Add;
        let a = F::from_usize(5);
        let b = F::from_usize(3);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(8));
    }

    #[test]
    fn test_eval_mul_operation() {
        let op = HighLevelOperation::Mul;
        let a = F::from_usize(4);
        let b = F::from_usize(7);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(28));
    }

    #[test]
    fn test_eval_sub_operation() {
        let op = HighLevelOperation::Sub;
        let a = F::from_usize(10);
        let b = F::from_usize(3);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(7));
    }

    #[test]
    fn test_eval_div_operation() {
        let op = HighLevelOperation::Div;
        let a = F::from_usize(15);
        let b = F::from_usize(3);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(5));
    }

    #[test]
    fn test_eval_exp_operation() {
        let op = HighLevelOperation::Exp;
        let a = F::from_usize(2);
        let b = F::from_usize(3);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(8));
    }

    #[test]
    fn test_eval_mod_operation() {
        let op = HighLevelOperation::Mod;
        let a = F::from_usize(17);
        let b = F::from_usize(5);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(2));
    }

    #[test]
    fn test_eval_add_with_zero() {
        let op = HighLevelOperation::Add;
        let a = F::from_usize(42);
        let b = F::ZERO;
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(42));
    }

    #[test]
    fn test_eval_mul_with_zero() {
        let op = HighLevelOperation::Mul;
        let a = F::from_usize(42);
        let b = F::ZERO;
        let result = op.eval(a, b);
        assert_eq!(result, F::ZERO);
    }

    #[test]
    fn test_eval_mul_with_one() {
        let op = HighLevelOperation::Mul;
        let a = F::from_usize(42);
        let b = F::ONE;
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(42));
    }

    #[test]
    fn test_eval_exp_with_zero_exponent() {
        let op = HighLevelOperation::Exp;
        let a = F::from_usize(42);
        let b = F::ZERO;
        let result = op.eval(a, b);
        assert_eq!(result, F::ONE);
    }

    #[test]
    fn test_eval_exp_with_one_exponent() {
        let op = HighLevelOperation::Exp;
        let a = F::from_usize(42);
        let b = F::ONE;
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(42));
    }

    #[test]
    fn test_display_add() {
        let op = HighLevelOperation::Add;
        assert_eq!(format!("{}", op), "+");
    }

    #[test]
    fn test_display_mul() {
        let op = HighLevelOperation::Mul;
        assert_eq!(format!("{}", op), "*");
    }

    #[test]
    fn test_display_sub() {
        let op = HighLevelOperation::Sub;
        assert_eq!(format!("{}", op), "-");
    }

    #[test]
    fn test_display_div() {
        let op = HighLevelOperation::Div;
        assert_eq!(format!("{}", op), "/");
    }

    #[test]
    fn test_display_exp() {
        let op = HighLevelOperation::Exp;
        assert_eq!(format!("{}", op), "**");
    }

    #[test]
    fn test_display_mod() {
        let op = HighLevelOperation::Mod;
        assert_eq!(format!("{}", op), "%");
    }

    #[test]
    fn test_try_from_add_success() {
        let high_level = HighLevelOperation::Add;
        let vm_op = Operation::try_from(high_level);
        assert!(vm_op.is_ok());
        assert_eq!(vm_op.unwrap(), Operation::Add);
    }

    #[test]
    fn test_try_from_mul_success() {
        let high_level = HighLevelOperation::Mul;
        let vm_op = Operation::try_from(high_level);
        assert!(vm_op.is_ok());
        assert_eq!(vm_op.unwrap(), Operation::Mul);
    }

    #[test]
    fn test_try_from_sub_failure() {
        let high_level = HighLevelOperation::Sub;
        let vm_op = Operation::try_from(high_level);
        assert!(vm_op.is_err());
        assert_eq!(vm_op.unwrap_err(), "Cannot convert Sub to +/x");
    }

    #[test]
    fn test_try_from_div_failure() {
        let high_level = HighLevelOperation::Div;
        let vm_op = Operation::try_from(high_level);
        assert!(vm_op.is_err());
        assert_eq!(vm_op.unwrap_err(), "Cannot convert Div to +/x");
    }

    #[test]
    fn test_try_from_exp_failure() {
        let high_level = HighLevelOperation::Exp;
        let vm_op = Operation::try_from(high_level);
        assert!(vm_op.is_err());
        assert_eq!(vm_op.unwrap_err(), "Cannot convert Exp to +/x");
    }

    #[test]
    fn test_try_from_mod_failure() {
        let high_level = HighLevelOperation::Mod;
        let vm_op = Operation::try_from(high_level);
        assert!(vm_op.is_err());
        assert_eq!(vm_op.unwrap_err(), "Cannot convert Mod to +/x");
    }

    #[test]
    fn test_debug_format_add() {
        let op = HighLevelOperation::Add;
        assert_eq!(format!("{:?}", op), "Add");
    }

    #[test]
    fn test_debug_format_mul() {
        let op = HighLevelOperation::Mul;
        assert_eq!(format!("{:?}", op), "Mul");
    }

    #[test]
    fn test_debug_format_sub() {
        let op = HighLevelOperation::Sub;
        assert_eq!(format!("{:?}", op), "Sub");
    }

    #[test]
    fn test_debug_format_div() {
        let op = HighLevelOperation::Div;
        assert_eq!(format!("{:?}", op), "Div");
    }

    #[test]
    fn test_debug_format_exp() {
        let op = HighLevelOperation::Exp;
        assert_eq!(format!("{:?}", op), "Exp");
    }

    #[test]
    fn test_debug_format_mod() {
        let op = HighLevelOperation::Mod;
        assert_eq!(format!("{:?}", op), "Mod");
    }

    #[test]
    fn test_eval_large_numbers() {
        let op = HighLevelOperation::Add;
        let a = F::from_usize(1000000);
        let b = F::from_usize(2000000);
        let result = op.eval(a, b);
        assert_eq!(result, F::from_usize(3000000));
    }

    #[test]
    fn test_eval_edge_case_mod_by_one() {
        let op = HighLevelOperation::Mod;
        let a = F::from_usize(42);
        let b = F::ONE;
        let result = op.eval(a, b);
        assert_eq!(result, F::ZERO);
    }

    #[test]
    fn test_operation_ordering_consistency() {
        let operations = [
            HighLevelOperation::Add,
            HighLevelOperation::Mul,
            HighLevelOperation::Sub,
            HighLevelOperation::Div,
            HighLevelOperation::Exp,
            HighLevelOperation::Mod,
        ];

        for i in 0..operations.len() {
            for j in 0..operations.len() {
                if i < j {
                    assert!(operations[i] < operations[j]);
                } else if i == j {
                    assert!(operations[i] == operations[j]);
                } else {
                    assert!(operations[i] > operations[j]);
                }
            }
        }
    }

    #[test]
    fn test_eval_commutativity_add() {
        let op = HighLevelOperation::Add;
        let a = F::from_usize(7);
        let b = F::from_usize(13);

        let result1 = op.eval(a, b);
        let result2 = op.eval(b, a);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_eval_commutativity_mul() {
        let op = HighLevelOperation::Mul;
        let a = F::from_usize(7);
        let b = F::from_usize(13);

        let result1 = op.eval(a, b);
        let result2 = op.eval(b, a);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_eval_non_commutativity_sub() {
        let op = HighLevelOperation::Sub;
        let a = F::from_usize(10);
        let b = F::from_usize(3);

        let result1 = op.eval(a, b);
        let result2 = op.eval(b, a);
        assert_ne!(result1, result2);
    }

    #[test]
    fn test_eval_non_commutativity_div() {
        let op = HighLevelOperation::Div;
        let a = F::from_usize(15);
        let b = F::from_usize(3);

        let result1 = op.eval(a, b);
        let result2 = op.eval(b, a);
        assert_ne!(result1, result2);
    }

    #[test]
    fn test_all_variants_covered_by_display() {
        let operations = [
            HighLevelOperation::Add,
            HighLevelOperation::Mul,
            HighLevelOperation::Sub,
            HighLevelOperation::Div,
            HighLevelOperation::Exp,
            HighLevelOperation::Mod,
        ];

        let expected_displays = ["+", "*", "-", "/", "**", "%"];

        for (op, expected) in operations.iter().zip(expected_displays.iter()) {
            assert_eq!(format!("{}", op), *expected);
        }
    }

    #[test]
    fn test_all_variants_covered_by_eval() {
        let operations = [
            HighLevelOperation::Add,
            HighLevelOperation::Mul,
            HighLevelOperation::Sub,
            HighLevelOperation::Div,
            HighLevelOperation::Exp,
            HighLevelOperation::Mod,
        ];

        let a = F::from_usize(10);
        let b = F::from_usize(3);

        for op in operations.iter() {
            let _result = op.eval(a, b);
        }
    }
}

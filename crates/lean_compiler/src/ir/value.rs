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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::ConstExpression;
    use lean_vm::Label;

    #[test]
    fn test_intermediate_value_constant_variant() {
        let const_expr = ConstExpression::scalar(42);
        let value = IntermediateValue::Constant(const_expr.clone());

        if let IntermediateValue::Constant(inner) = &value {
            assert_eq!(inner, &const_expr);
        } else {
            panic!("Expected Constant variant");
        }
    }

    #[test]
    fn test_intermediate_value_fp_variant() {
        let value = IntermediateValue::Fp;
        assert_eq!(value, IntermediateValue::Fp);
    }

    #[test]
    fn test_intermediate_value_memory_after_fp_variant() {
        let offset = ConstExpression::scalar(10);
        let value = IntermediateValue::MemoryAfterFp {
            offset: offset.clone(),
        };

        if let IntermediateValue::MemoryAfterFp {
            offset: inner_offset,
        } = &value
        {
            assert_eq!(inner_offset, &offset);
        } else {
            panic!("Expected MemoryAfterFp variant");
        }
    }

    #[test]
    fn test_intermediate_value_clone() {
        let original = IntermediateValue::Constant(ConstExpression::scalar(42));
        let cloned = original.clone();
        assert_eq!(original, cloned);
    }

    #[test]
    fn test_intermediate_value_partial_eq() {
        let value1 = IntermediateValue::Constant(ConstExpression::scalar(42));
        let value2 = IntermediateValue::Constant(ConstExpression::scalar(42));
        let value3 = IntermediateValue::Constant(ConstExpression::scalar(43));

        assert_eq!(value1, value2);
        assert_ne!(value1, value3);
        assert_ne!(value1, IntermediateValue::Fp);
    }

    #[test]
    fn test_intermediate_value_label_method() {
        let label = Label::function("test_function");
        let value = IntermediateValue::label(label.clone());

        if let IntermediateValue::Constant(const_expr) = &value {
            if let ConstExpression::Value(crate::lang::ConstantValue::Label(inner_label)) =
                const_expr
            {
                assert_eq!(inner_label, &label);
            } else {
                panic!("Expected Label within ConstExpression");
            }
        } else {
            panic!("Expected Constant variant");
        }
    }

    #[test]
    fn test_intermediate_value_is_constant_true() {
        let value = IntermediateValue::Constant(ConstExpression::scalar(42));
        assert!(value.is_constant());
    }

    #[test]
    fn test_intermediate_value_is_constant_false_fp() {
        let value = IntermediateValue::Fp;
        assert!(!value.is_constant());
    }

    #[test]
    fn test_intermediate_value_is_constant_false_memory() {
        let value = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        assert!(!value.is_constant());
    }

    #[test]
    fn test_intermediate_value_from_const_expression() {
        let const_expr = ConstExpression::scalar(42);
        let value: IntermediateValue = const_expr.clone().into();

        if let IntermediateValue::Constant(inner) = &value {
            assert_eq!(inner, &const_expr);
        } else {
            panic!("Expected Constant variant");
        }
    }

    #[test]
    fn test_intermediate_value_from_label() {
        let label = Label::function("test_function");
        let value: IntermediateValue = label.clone().into();

        if let IntermediateValue::Constant(const_expr) = &value {
            if let ConstExpression::Value(crate::lang::ConstantValue::Label(inner_label)) =
                const_expr
            {
                assert_eq!(inner_label, &label);
            } else {
                panic!("Expected Label within ConstExpression");
            }
        } else {
            panic!("Expected Constant variant");
        }
    }

    #[test]
    fn test_intermediate_value_display_constant() {
        let value = IntermediateValue::Constant(ConstExpression::scalar(42));
        assert_eq!(format!("{}", value), "42");
    }

    #[test]
    fn test_intermediate_value_display_fp() {
        let value = IntermediateValue::Fp;
        assert_eq!(format!("{}", value), "fp");
    }

    #[test]
    fn test_intermediate_value_display_memory_after_fp() {
        let value = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        assert_eq!(format!("{}", value), "m[fp + 10]");
    }

    #[test]
    fn test_intermediate_value_debug_format() {
        let value = IntermediateValue::Constant(ConstExpression::scalar(42));
        let debug_output = format!("{:?}", value);

        assert!(debug_output.contains("Constant"));
        assert!(debug_output.contains("42"));
    }

    #[test]
    fn test_intermediate_value_equality_different_variants() {
        let constant = IntermediateValue::Constant(ConstExpression::scalar(42));
        let fp = IntermediateValue::Fp;
        let memory = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(42),
        };

        assert_ne!(constant, fp);
        assert_ne!(constant, memory);
        assert_ne!(fp, memory);
    }

    #[test]
    fn test_intermediate_value_equality_same_memory_different_offset() {
        let memory1 = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let memory2 = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(20),
        };

        assert_ne!(memory1, memory2);
    }

    #[test]
    fn test_intermediate_value_equality_same_memory_same_offset() {
        let memory1 = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let memory2 = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };

        assert_eq!(memory1, memory2);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_memory_after_fp() {
        let offset = ConstExpression::scalar(10);
        let value = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: offset.clone(),
        };

        if let IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: inner_offset,
        } = &value
        {
            assert_eq!(inner_offset, &offset);
        } else {
            panic!("Expected MemoryAfterFp variant");
        }
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_fp() {
        let value = IntermediaryMemOrFpOrConstant::Fp;
        assert_eq!(value, IntermediaryMemOrFpOrConstant::Fp);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_constant() {
        let const_expr = ConstExpression::scalar(42);
        let value = IntermediaryMemOrFpOrConstant::Constant(const_expr.clone());

        if let IntermediaryMemOrFpOrConstant::Constant(inner) = &value {
            assert_eq!(inner, &const_expr);
        } else {
            panic!("Expected Constant variant");
        }
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_clone() {
        let original = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));
        let cloned = original.clone();
        assert_eq!(original, cloned);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_partial_eq() {
        let value1 = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));
        let value2 = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));
        let value3 = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(43));

        assert_eq!(value1, value2);
        assert_ne!(value1, value3);
        assert_ne!(value1, IntermediaryMemOrFpOrConstant::Fp);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_partial_ord() {
        let memory = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let fp = IntermediaryMemOrFpOrConstant::Fp;
        let constant = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));

        assert!(memory < fp);
        assert!(fp < constant);
        assert!(memory < constant);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_ord() {
        use std::cmp::Ordering;

        let memory = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let fp = IntermediaryMemOrFpOrConstant::Fp;

        assert_eq!(memory.cmp(&fp), Ordering::Less);
        assert_eq!(fp.cmp(&memory), Ordering::Greater);
        assert_eq!(memory.cmp(&memory), Ordering::Equal);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();

        let value = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));
        value.hash(&mut hasher1);
        value.hash(&mut hasher2);

        assert_eq!(hasher1.finish(), hasher2.finish());
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_display_memory() {
        let value = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        assert_eq!(format!("{}", value), "m[fp + 10]");
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_display_fp() {
        let value = IntermediaryMemOrFpOrConstant::Fp;
        assert_eq!(format!("{}", value), "fp");
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_display_constant() {
        let value = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));
        assert_eq!(format!("{}", value), "42");
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_debug_format() {
        let value = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));
        let debug_output = format!("{:?}", value);

        assert!(debug_output.contains("Constant"));
        assert!(debug_output.contains("42"));
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_equality_different_variants() {
        let memory = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let fp = IntermediaryMemOrFpOrConstant::Fp;
        let constant = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));

        assert_ne!(memory, fp);
        assert_ne!(memory, constant);
        assert_ne!(fp, constant);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_equality_same_memory_different_offset() {
        let memory1 = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let memory2 = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(20),
        };

        assert_ne!(memory1, memory2);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_equality_same_memory_same_offset() {
        let memory1 = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let memory2 = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };

        assert_eq!(memory1, memory2);
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_ordering_consistency() {
        let values = [
            IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: ConstExpression::scalar(5),
            },
            IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: ConstExpression::scalar(10),
            },
            IntermediaryMemOrFpOrConstant::Fp,
            IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(1)),
            IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42)),
        ];

        for i in 0..values.len() {
            for j in 0..values.len() {
                if i < j {
                    assert!(values[i] < values[j], "Expected {} < {}", i, j);
                } else if i == j {
                    assert!(values[i] == values[j], "Expected {} == {}", i, j);
                } else {
                    assert!(values[i] > values[j], "Expected {} > {}", i, j);
                }
            }
        }
    }

    #[test]
    fn test_intermediate_value_all_variants_display() {
        let constant = IntermediateValue::Constant(ConstExpression::scalar(42));
        let fp = IntermediateValue::Fp;
        let memory = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };

        assert_eq!(format!("{}", constant), "42");
        assert_eq!(format!("{}", fp), "fp");
        assert_eq!(format!("{}", memory), "m[fp + 10]");
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_all_variants_display() {
        let memory = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(10),
        };
        let fp = IntermediaryMemOrFpOrConstant::Fp;
        let constant = IntermediaryMemOrFpOrConstant::Constant(ConstExpression::scalar(42));

        assert_eq!(format!("{}", memory), "m[fp + 10]");
        assert_eq!(format!("{}", fp), "fp");
        assert_eq!(format!("{}", constant), "42");
    }

    #[test]
    fn test_intermediate_value_label_with_complex_name() {
        let label = Label::function("complex_function_name_123");
        let value = IntermediateValue::label(label.clone());

        if let IntermediateValue::Constant(const_expr) = &value {
            if let ConstExpression::Value(crate::lang::ConstantValue::Label(inner_label)) =
                const_expr
            {
                assert_eq!(inner_label, &label);
            } else {
                panic!("Expected Label within ConstExpression");
            }
        } else {
            panic!("Expected Constant variant");
        }
    }

    #[test]
    fn test_intermediate_value_memory_with_zero_offset() {
        let value = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(0),
        };
        assert_eq!(format!("{}", value), "m[fp + 0]");
    }

    #[test]
    fn test_intermediate_value_memory_with_large_offset() {
        let value = IntermediateValue::MemoryAfterFp {
            offset: ConstExpression::scalar(1000000),
        };
        assert_eq!(format!("{}", value), "m[fp + 1000000]");
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_memory_with_zero_offset() {
        let value = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(0),
        };
        assert_eq!(format!("{}", value), "m[fp + 0]");
    }

    #[test]
    fn test_intermediary_mem_or_fp_or_constant_memory_with_large_offset() {
        let value = IntermediaryMemOrFpOrConstant::MemoryAfterFp {
            offset: ConstExpression::scalar(1000000),
        };
        assert_eq!(format!("{}", value), "m[fp + 1000000]");
    }

    #[test]
    fn test_intermediate_value_from_implementations() {
        let const_expr = ConstExpression::scalar(42);
        let label = Label::function("test");

        let from_const: IntermediateValue = const_expr.clone().into();
        let from_label: IntermediateValue = label.clone().into();

        assert_eq!(from_const, IntermediateValue::Constant(const_expr));

        if let IntermediateValue::Constant(ConstExpression::Value(
            crate::lang::ConstantValue::Label(inner_label),
        )) = from_label
        {
            assert_eq!(inner_label, label);
        } else {
            panic!("Expected Label constant");
        }
    }

    #[test]
    fn test_value_types_exhaustive_match_coverage() {
        let intermediate_value = IntermediateValue::Fp;
        match intermediate_value {
            IntermediateValue::Constant(_) => {}
            IntermediateValue::Fp => {}
            IntermediateValue::MemoryAfterFp { .. } => {}
        }

        let intermediary_value = IntermediaryMemOrFpOrConstant::Fp;
        match intermediary_value {
            IntermediaryMemOrFpOrConstant::MemoryAfterFp { .. } => {}
            IntermediaryMemOrFpOrConstant::Fp => {}
            IntermediaryMemOrFpOrConstant::Constant(_) => {}
        }
    }
}

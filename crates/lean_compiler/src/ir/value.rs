use crate::backend::evaluation::{CodeGenerator, eval_const_expression_usize, try_as_constant};
use crate::ir::compiler::Compiler;
use crate::lang::{ConstExpression, SimpleExpr};
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
    /// Creates an IntermediateValue from a label.
    pub const fn label(label: Label) -> Self {
        Self::Constant(ConstExpression::label(label))
    }

    /// Returns true if this value is a constant.
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    /// Creates an IntermediateValue from a SimpleExpr during code generation.
    pub fn from_simple_expr(expr: &crate::lang::SimpleExpr, compiler: &Compiler) -> Self {
        match expr {
            SimpleExpr::Var(var) => Self::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
            SimpleExpr::Constant(c) => Self::Constant(c.clone()),
            SimpleExpr::ConstMallocAccess {
                malloc_label,
                offset,
            } => Self::MemoryAfterFp {
                offset: compiler.get_offset(
                    &crate::ir::VarOrConstMallocAccess::ConstMallocAccess {
                        malloc_label: *malloc_label,
                        offset: offset.clone(),
                    },
                ),
            },
        }
    }

    /// Creates an IntermediateValue from a VarOrConstMallocAccess during code generation.
    pub fn from_var_or_const_malloc_access(
        var_or_const: &crate::ir::VarOrConstMallocAccess,
        compiler: &Compiler,
    ) -> Self {
        Self::MemoryAfterFp {
            offset: compiler.get_offset(var_or_const),
        }
    }

    /// Converts this value to a MemOrFp for low-level code generation.
    pub fn try_into_mem_or_fp(&self, compiler: &CodeGenerator) -> Result<lean_vm::MemOrFp, String> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(lean_vm::MemOrFp::MemoryAfterFp {
                offset: eval_const_expression_usize(offset, compiler),
            }),
            Self::Fp => Ok(lean_vm::MemOrFp::Fp),
            _ => Err(format!("Cannot convert {self:?} to MemOrFp")),
        }
    }

    /// Converts this value to a MemOrConstant for low-level code generation.
    pub fn try_into_mem_or_constant(
        &self,
        compiler: &CodeGenerator,
    ) -> Result<lean_vm::MemOrConstant, String> {
        if let Some(cst) = try_as_constant(self, compiler) {
            return Ok(lean_vm::MemOrConstant::Constant(cst));
        }
        if let Self::MemoryAfterFp { offset } = self {
            return Ok(lean_vm::MemOrConstant::MemoryAfterFp {
                offset: eval_const_expression_usize(offset, compiler),
            });
        }
        Err(format!("Cannot convert {self:?} to MemOrConstant"))
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
    use crate::ir::VarOrConstMallocAccess;
    use crate::lang::{ConstExpression, SimpleExpr};
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

    #[test]
    fn test_intermediate_value_from_simple_expr() {
        let mut compiler = Compiler::new();
        compiler.var_positions.insert("x".to_string(), 3);
        compiler.const_mallocs.insert(0, 8);

        // Test variable conversion
        let var_expr = SimpleExpr::Var("x".to_string());
        let result = IntermediateValue::from_simple_expr(&var_expr, &compiler);
        if let IntermediateValue::MemoryAfterFp { offset } = result {
            assert_eq!(offset, ConstExpression::scalar(3));
        } else {
            panic!("Expected MemoryAfterFp variant");
        }

        // Test constant conversion
        let const_expr = SimpleExpr::scalar(42);
        let result = IntermediateValue::from_simple_expr(&const_expr, &compiler);
        if let IntermediateValue::Constant(const_val) = result {
            assert_eq!(const_val, ConstExpression::scalar(42));
        } else {
            panic!("Expected Constant variant");
        }

        // Test const malloc access conversion
        let malloc_expr = SimpleExpr::ConstMallocAccess {
            malloc_label: 0,
            offset: ConstExpression::scalar(2),
        };
        let result = IntermediateValue::from_simple_expr(&malloc_expr, &compiler);
        if let IntermediateValue::MemoryAfterFp { offset } = result {
            // Should be binary expression: 8 + 2
            if let ConstExpression::Binary {
                operation,
                left,
                right,
            } = offset
            {
                assert_eq!(operation, crate::ir::HighLevelOperation::Add);
                assert_eq!(left.as_ref(), &ConstExpression::scalar(8));
                assert_eq!(right.as_ref(), &ConstExpression::scalar(2));
            } else {
                panic!("Expected binary expression for const malloc");
            }
        } else {
            panic!("Expected MemoryAfterFp variant");
        }
    }

    #[test]
    fn test_intermediate_value_from_var_or_const_malloc_access() {
        let mut compiler = Compiler::new();
        compiler.var_positions.insert("y".to_string(), 7);
        compiler.const_mallocs.insert(1, 15);

        // Test variable access
        let var_access = VarOrConstMallocAccess::Var("y".to_string());
        let result = IntermediateValue::from_var_or_const_malloc_access(&var_access, &compiler);
        if let IntermediateValue::MemoryAfterFp { offset } = result {
            assert_eq!(offset, ConstExpression::scalar(7));
        } else {
            panic!("Expected MemoryAfterFp variant");
        }

        // Test const malloc access
        let malloc_access = VarOrConstMallocAccess::ConstMallocAccess {
            malloc_label: 1,
            offset: ConstExpression::scalar(5),
        };
        let result = IntermediateValue::from_var_or_const_malloc_access(&malloc_access, &compiler);
        if let IntermediateValue::MemoryAfterFp { offset } = result {
            // Should be binary expression: 15 + 5
            if let ConstExpression::Binary {
                operation,
                left,
                right,
            } = offset
            {
                assert_eq!(operation, crate::ir::HighLevelOperation::Add);
                assert_eq!(left.as_ref(), &ConstExpression::scalar(15));
                assert_eq!(right.as_ref(), &ConstExpression::scalar(5));
            } else {
                panic!("Expected binary expression for const malloc");
            }
        } else {
            panic!("Expected MemoryAfterFp variant");
        }
    }

    #[test]
    #[should_panic(expected = "Variable z not in scope")]
    fn test_intermediate_value_from_simple_expr_unknown_var() {
        use crate::lang::SimpleExpr;

        let compiler = Compiler::new();

        let var_expr = SimpleExpr::Var("z".to_string());
        let _result = IntermediateValue::from_simple_expr(&var_expr, &compiler);
    }

    #[test]
    #[should_panic(expected = "Const malloc 5 not in scope")]
    fn test_intermediate_value_from_simple_expr_unknown_malloc() {
        let compiler = Compiler::new();

        let malloc_expr = SimpleExpr::ConstMallocAccess {
            malloc_label: 5,
            offset: ConstExpression::scalar(1),
        };
        let _result = IntermediateValue::from_simple_expr(&malloc_expr, &compiler);
    }
}
